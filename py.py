import os
import json
import importlib.util
import sys
import asyncio
import threading
import tkinter as tk
from datetime import datetime, timedelta
import customtkinter
from tkinter import filedialog, messagebox, scrolledtext
import subprocess
import logging
import random
import re
import math
import shutil
import shlex
import time
import hashlib
from functools import wraps
from typing import Callable, Dict, Any, Optional

# ------------- Audit / logging -------------
logging.basicConfig(filename='sudo_audit.log', level=logging.INFO,
                    format='%(asctime)s %(levelname)s %(message)s')

# ------------- Utilidades -------------
def hash_password(plain: str, salt: Optional[str] = None) -> str:
    if salt is None:
        salt = os.urandom(16).hex()
    h = hashlib.sha256((plain + salt).encode('utf-8')).hexdigest()
    return f"{salt}${h}"

# ------------- Armazenamento de usuários (simples) -------------
class UserStore:
    def __init__(self, path='users.json'):
        self.path = path
        self._load()

    def _load(self):
        try:
            with open(self.path, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except Exception:
            data = {}
        # formato: username -> {"perms": [...], "password": hashed or None}
        self.users: Dict[str, Dict[str, Any]] = data

    def save(self):
        with open(self.path, 'w', encoding='utf-8') as f:
            json.dump(self.users, f, indent=2)

    def ensure_user(self, username: str):
        if username not in self.users:
            self.users[username] = {"perms": [], "password": None}
            self.save()

    def set_password(self, username: str, plain: str):
        self.ensure_user(username)
        self.users[username]['password'] = hash_password(plain)
        self.save()

    def check_password(self, username: str, plain: str) -> bool:
        u = self.users.get(username)
        if not u: return False
        hp = u.get('password')
        if hp is None: return False
        salt, hashed = hp.split('$')
        return hash_password(plain, salt) == hp

    def add_perm(self, username: str, perm: str):
        self.ensure_user(username)
        if perm not in self.users[username]['perms']:
            self.users[username]['perms'].append(perm)
            self.save()

    def remove_perm(self, username: str, perm: str):
        self.ensure_user(username)
        if perm in self.users[username]['perms']:
            self.users[username]['perms'].remove(perm)
            self.save()

    def has_perm(self, username: str, perm: str) -> bool:
        u = self.users.get(username)
        if not u: return False
        perms = set(u.get('perms', []))
        return '*' in perms or perm in perms

    def list_users(self):
        return list(self.users.keys())

    def list_perms(self, username: str):
        u = self.users.get(username)
        if not u: return []
        return u.get('perms', [])

# ------------- Command registry -------------
class Context:
    def __init__(self, user: str):
        self.user = user

class CommandRegistry:
    def __init__(self):
        self._cmds: Dict[str, Dict[str, Any]] = {}

    def register(self, name: str, fn: Callable, perm: Optional[str] = None):
        self._cmds[name] = {'fn': fn, 'perm': perm}

    def get(self, name: str):
        return self._cmds.get(name)

    def all_commands(self):
        return list(self._cmds.keys())

registry = CommandRegistry()

def command(name: str, required_perm: Optional[str] = None):
    def deco(fn):
        registry.register(name, fn, required_perm)
        @wraps(fn)
        def wrapper(*a, **k): return fn(*a, **k)
        return wrapper
    return deco

# ------------- Dispatcher with sudo & impersonation -------------
class Dispatcher:
    def __init__(self, user_store: UserStore):
        self.users = user_store
        # impersonation sessions: username -> (target_user, expires_at)
        self.sessions: Dict[str, tuple] = {}

    def _log(self, level, msg):
        getattr(logging, level)(msg)

    def _execute_as(self, target_user: str, cmdline: str, invoker: str):
        parts = shlex.split(cmdline)
        if not parts:
            return "no command"
        name, *args = parts
        entry = registry.get(name)
        if not entry:
            return f"unknown command '{name}'"
        required = entry['perm']
        if required and not self.users.has_perm(target_user, required):
            return f"user '{target_user}' lacks '{required}' permission"
        ctx = Context(target_user)
        try:
            result = entry['fn'](ctx, *args)
            self._log('info', f"EXECUTE: invoker={invoker} as={target_user} cmd='{cmdline}' -> OK")
            return result
        except Exception as e:
            self._log('exception', f"EXECUTE FAILED: invoker={invoker} as={target_user} cmd='{cmdline}'")
            return f"error: {e}"

    def run(self, invoker: str, cmdline: str):
        parts = shlex.split(cmdline)
        if not parts:
            return "no command"

        # caso: comando 'sudo -u target <command...>'
        if parts[0] == 'sudo':
            # sudo format: sudo -u <target> <command...>
            if len(parts) >= 3 and parts[1] == '-u':
                target = parts[2]
                if len(parts) < 4:
                    return "usage: sudo -u <target> <command...>"
                command = ' '.join(parts[3:])
                if not self.users.has_perm(invoker, 'sudo'):
                    return f"invoker '{invoker}' lacks 'sudo' permission"
                logging.info(f"SUDO: {invoker} -> {target}: {command}")
                return self._execute_as(target, command, invoker)

            # sudo to start an impersonation session: sudo -i -u <target> <seconds?>
            if len(parts) >= 4 and parts[1] == '-i' and parts[2] == '-u':
                target = parts[3]
                ttl = 300  # default 5 minutos
                if len(parts) >= 5:
                    try:
                        ttl = int(parts[4])
                    except Exception:
                        pass
                if not self.users.has_perm(invoker, 'sudo'):
                    return f"invoker '{invoker}' lacks 'sudo' permission"
                expires = time.time() + ttl
                self.sessions[invoker] = (target, expires)
                logging.info(f"SUDO_SESSION_START: {invoker} -> {target} for {ttl}s")
                return f"impersonating {target} for {ttl} seconds"

            return "usage: sudo -u <target> <command...>  OR  sudo -i -u <target> [seconds]"

        # caso: se invoker tem sessão ativa, executa como target até expirar
        sess = self.sessions.get(invoker)
        if sess:
            target, expires = sess
            if time.time() < expires:
                # execute as target
                logging.info(f"SUDO_SESSION_EXEC: invoker={invoker} active_as={target} cmd='{cmdline}'")
                return self._execute_as(target, cmdline, invoker)
            else:
                del self.sessions[invoker]
                logging.info(f"SUDO_SESSION_END: invoker={invoker}")

        # exec normal como invoker
        logging.info(f"CMD: {invoker}: {cmdline}")
        return self._execute_as(invoker, cmdline, invoker)

# ------------- Comandos de administração de exemplo -------------
@command('grant', required_perm='grant')
def cmd_grant(ctx: Context, who: str, perm: str):
    dispatcher.users.add_perm(who, perm)
    return f"{ctx.user} granted '{perm}' to {who}"

@command('revoke', required_perm='grant')
def cmd_revoke(ctx: Context, who: str, perm: str):
    dispatcher.users.remove_perm(who, perm)
    return f"{ctx.user} revoked '{perm}' from {who}"

@command('whoami')
def cmd_whoami(ctx: Context):
    return f"you are {ctx.user}"

@command('say', required_perm='say')
def cmd_say(ctx: Context, *words):
    return f"{ctx.user} says: {' '.join(words)}"

@command('echo')
def cmd_echo(ctx: Context, *words):
    return ' '.join(words)

@command('list_users', required_perm='admin')
def cmd_list_users(ctx: Context):
    return ', '.join(dispatcher.users.list_users())

@command('list_perms', required_perm='admin')
def cmd_list_perms(ctx: Context, who: str):
    return ', '.join(dispatcher.users.list_perms(who))

@command('create_user', required_perm='admin')
def cmd_create_user(ctx: Context, who: str):
    dispatcher.users.ensure_user(who)
    return f"user '{who}' created"

@command('change_password', required_perm='admin')
def cmd_change_password(ctx: Context, who: str, new_plain: str):
    if who != ctx.user and not dispatcher.users.has_perm(ctx.user, 'change_others_password'):
        return "no permission to change others' password"
    dispatcher.users.set_password(who, new_plain)
    return f"password changed for {who}"

@command('add_perm', required_perm='admin')
def cmd_add_perm(ctx: Context, who: str, perm: str):
    dispatcher.users.add_perm(who, perm)
    return f"added '{perm}' to {who}"

@command('remove_perm', required_perm='admin')
def cmd_remove_perm(ctx: Context, who: str, perm: str):
    dispatcher.users.remove_perm(who, perm)
    return f"removed '{perm}' from {who}"

@command('list_commands')
def cmd_list_commands(ctx: Context):
    return ', '.join(registry.all_commands())

# ------------- BootSystem and other classes follow... -------------

class BootSystem:
    """Enhanced Boot System with improved logging and recovery"""
    
    def __init__(self, root_dir):
        self.root_dir = root_dir
        self.boot_dir = os.path.join(root_dir, "User", "Boot")
        self.boot_config_file = os.path.join(self.boot_dir, "boot_config.json")
        self.boot_console_file = os.path.join(self.boot_dir, "boot_log.boot")
        
        # Enhanced default boot sequence with more components
        self.default_boot_sequence = {
            "boot_info": {
                "version": "3.0.0",
                "name": "BotCreator OS",
                "author": "xAI Enhanced System"
            },
            "sequence": {
                "SystemCore": {"priority": 1, "path": "config.json", "critical": True},
                "DataService": {"priority": 2, "path": "Services/DataSavingService.conf", "critical": True},
                "UIEngine": {"priority": 3, "path": "Feeds/Main.ui", "critical": False},
                "EditorCache": {"priority": 4, "path": "Feeds/Editor.ui", "critical": False},
                "UserMods": {"priority": 5, "path": "User/Mods", "critical": False},
                "BotRegistry": {"priority": 6, "path": "Bots", "critical": False},
                "AIEngine": {"priority": 7, "path": "Services/AI.conf", "critical": False},
                "DiscordAPI": {"priority": 8, "path": "Services/Discord.conf", "critical": False},
                "LoggingService": {"priority": 9, "path": "Services/Logging.conf", "critical": False},
                "BackupSystem": {"priority": 10, "path": "Services/Backup.conf", "critical": False},
                "SudoSystem": {"priority": 11, "path": "Services/Sudo.conf", "critical": False}
            },
            "settings": {
                "timeout_per_item": 10000,
                "show_splash": True,
                "verbose_logging": True,
                "fallback_on_error": True,
                "auto_recovery": True
            }
        }
        
        self.boot_log = []
        self.boot_success = False
        
    def ensure_boot_files(self):
        """Create boot files if they don't exist with improved defaults"""
        os.makedirs(self.boot_dir, exist_ok=True)
        
        if not os.path.exists(self.boot_config_file):
            with open(self.boot_config_file, 'w') as f:
                json.dump(self.default_boot_sequence, f, indent=4)
            self.log_boot("Created enhanced default boot configuration")
        
        if not os.path.exists(self.boot_console_file):
            with open(self.boot_console_file, 'w') as f:
                f.write(f"# BotCreator OS Boot Console v3.0.0\n")
                f.write(f"# Generated: {datetime.now().isoformat()}\n")
                f.write("="*60 + "\n")
            self.log_boot("Initialized enhanced boot console")
    
    def log_boot(self, message, level="INFO"):
        """Log boot message with levels"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
        log_entry = f"[{timestamp}] [{level}] {message}"
        self.boot_log.append(log_entry)
        
        try:
            with open(self.boot_console_file, 'a') as f:
                f.write(log_entry + "\n")
            logging.log(getattr(logging, level), message)
        except:
            pass
    
    def load_boot_config(self):
        """Load boot configuration with validation"""
        try:
            with open(self.boot_config_file, 'r') as f:
                config = json.load(f)
            # Validate config structure
            if "sequence" not in config or "settings" not in config:
                raise ValueError("Invalid config structure")
            self.log_boot("✓ Boot configuration loaded and validated")
            return config
        except Exception as e:
            self.log_boot(f"✗ Failed to load boot config: {e}", "ERROR")
            self.log_boot("⚠ Falling back to enhanced default sequence", "WARNING")
            return self.default_boot_sequence
    
    def execute_boot_sequence(self, callback=None):
        """Execute boot sequence with timeout and recovery"""
        self.log_boot("Starting BotCreator OS Boot Sequence v3.0...")
        self.log_boot("="*60)
        
        config = self.load_boot_config()
        sequence = config.get("sequence", {})
        settings = config.get("settings", {})
        
        sorted_items = sorted(sequence.items(), key=lambda x: x[1].get("priority", 999))
        
        success_count = 0
        total_count = len(sorted_items)
        
        for name, item in sorted_items:
            priority = item.get("priority", 0)
            path = item.get("path", "")
            critical = item.get("critical", False)
            
            self.log_boot(f"[{priority}] Loading {name}...")
            
            try:
                full_path = os.path.join(self.root_dir, path) if not os.path.isabs(path) else path
                
                if os.path.exists(full_path):
                    self.log_boot(f"    ✓ {name} loaded successfully")
                    success_count += 1
                else:
                    self.log_boot(f"    ✗ {name} not found at {path}", "ERROR" if critical else "WARNING")
                    if critical and settings.get("auto_recovery", False):
                        self.attempt_recovery(name, path)
                
            except Exception as e:
                self.log_boot(f"    ✗ ERROR in {name}: {e}", "ERROR" if critical else "WARNING")
                if critical and settings.get("auto_recovery", False):
                    self.attempt_recovery(name, path)
            
            if callback:
                callback(name, priority, success_count, total_count)
        
        self.log_boot("="*60)
        self.log_boot(f"Boot sequence completed: {success_count}/{total_count} items loaded")
        
        if success_count >= (total_count * 0.7):  # Raised success threshold
            self.boot_success = True
            self.log_boot("✓ BotCreator OS started successfully")
            return True
        else:
            self.log_boot("✗ Boot sequence failed - insufficient components", "ERROR")
            return False
    
    def attempt_recovery(self, name, path):
        """Attempt automatic recovery for critical components"""
        self.log_boot(f"🔄 Attempting recovery for {name}...")
        try:
            full_path = os.path.join(self.root_dir, path)
            dir_path = os.path.dirname(full_path)
            os.makedirs(dir_path, exist_ok=True)
            if not os.path.exists(full_path):
                with open(full_path, 'w') as f:
                    f.write("# Recovered placeholder file\n")
            self.log_boot(f"    ✓ Recovered {name}")
        except Exception as e:
            self.log_boot(f"    ✗ Recovery failed: {e}", "ERROR")

class AIEngine:
    """Enhanced AI Engine with learning and context awareness"""
    
    def __init__(self):
        self.responses = {
            "greeting": ["Hello! How can I assist you today?", "Hi! What's on your mind?", "Hey! Ready to create some bots?"],
            "goodbye": ["Goodbye! Come back soon!", "See you later! Happy coding!", "Bye! Don't forget to save your bots!"],
            "thanks": ["You're welcome! Always here to help.", "No problem at all!", "Happy to be of service!"],
            "help": ["I can help with bot creation, AI responses, and more. What do you need?", "How can I assist with your bot project?"],
            "unknown": ["Hmm, not sure about that one. Can you elaborate?", "Interesting! Tell me more.", "That's a new one for me."]
        }
        self.learned_responses = {}  # For dynamic learning
        self.context_memory = []  # Conversation context
    
    def generate_response(self, message, context="general"):
        """Generate AI response with context and learning"""
        self.context_memory.append(message)
        if len(self.context_memory) > 10:
            self.context_memory.pop(0)
        
        message_lower = message.lower()
        
        if any(word in message_lower for word in ["hello", "hi", "hey"]):
            return self._get_response("greeting")
        elif any(word in message_lower for word in ["bye", "goodbye", "see you"]):
            return self._get_response("goodbye")
        elif any(word in message_lower for word in ["thank", "thanks"]):
            return self._get_response("thanks")
        elif any(word in message_lower for word in ["help", "assist"]):
            return self._get_response("help")
        elif message_lower in self.learned_responses:
            return self.learned_responses[message_lower]
        else:
            return self._get_response("unknown")
    
    def _get_response(self, category):
        responses = self.responses.get(category, ["I understand."])
        return random.choice(responses)
    
    def learn_response(self, input_text, output_text):
        """Learn new response pairs"""
        self.learned_responses[input_text.lower()] = output_text
        logging.info(f"AI learned new response: {input_text} -> {output_text}")

class DiscordBotCreator:
    """Enhanced Discord Bot Creator with more features"""
    
    def __init__(self, parent_app):
        self.parent = parent_app
        self.template = '''import discord
from discord.ext import commands
import asyncio
import logging

# Bot configuration
BOT_TOKEN = "{token}"
COMMAND_PREFIX = "{prefix}"

# Setup logging
logging.basicConfig(level=logging.INFO)

# Create bot instance
intents = discord.Intents.default()
intents.message_content = True
intents.members = True
intents.guilds = True
bot = commands.Bot(command_prefix=COMMAND_PREFIX, intents=intents)

@bot.event
async def on_ready():
    logging.info(f"{bot.user} has connected to Discord!")
    logging.info(f"Bot is in {len(bot.guilds)} servers")
    await bot.change_presence(activity=discord.Game(name="Created with BotCreator OS v3"))

@bot.event
async def on_message(message):
    if message.author == bot.user:
        return
    
    # Custom message processing
    await bot.process_commands(message)

@bot.command(name="ping")
async def ping(ctx):
    """Check bot latency"""
    latency = round(bot.latency * 1000)
    await ctx.send(f"Pong! Latency: {latency}ms")

@bot.command(name="info")
async def info(ctx):
    """Get bot information"""
    embed = discord.Embed(
        title="Bot Information",
        description="Created with BotCreator OS v3",
        color=0x00ff00
    )
    embed.add_field(name="Servers", value=len(bot.guilds), inline=True)
    embed.add_field(name="Latency", value=f"{round(bot.latency * 1000)}ms", inline=True)
    await ctx.send(embed=embed)

# Run the bot
if __name__ == "__main__":
    try:
        bot.run(BOT_TOKEN)
    except Exception as e:
        logging.error(f"Error running bot: {e}")
'''
    
    def create_discord_bot(self, bot_name, prefix, token, features):
        """Create Discord bot with enhanced features"""
        code = self.template.format(token=token, prefix=prefix)
        
        if "moderation" in features:
            code += self.get_moderation_commands()
        if "music" in features:
            code += self.get_music_commands()
        if "ai_chat" in features:
            code += self.get_ai_chat_commands()
        if "games" in features:
            code += self.get_game_commands()
        if "utility" in features:
            code += self.get_utility_commands()
        
        return code
    
    def get_moderation_commands(self):
        return '''
# Enhanced Moderation Commands
@bot.command(name="kick")
@commands.has_permissions(kick_members=True)
async def kick(ctx, member: discord.Member, *, reason="No reason provided"):
    await member.kick(reason=reason)
    await ctx.send(f"{member.mention} has been kicked for: {reason}")

@bot.command(name="ban")
@commands.has_permissions(ban_members=True)
async def ban(ctx, member: discord.Member, *, reason="No reason provided"):
    await member.ban(reason=reason)
    await ctx.send(f"{member.mention} has been banned for: {reason}")

@bot.command(name="mute")
@commands.has_permissions(manage_roles=True)
async def mute(ctx, member: discord.Member, duration: int = 60, *, reason="No reason"):
    mute_role = discord.utils.get(ctx.guild.roles, name="Muted")
    if not mute_role:
        mute_role = await ctx.guild.create_role(name="Muted")
        for channel in ctx.guild.channels:
            await channel.set_permissions(mute_role, speak=False, send_messages=False)
    await member.add_roles(mute_role, reason=reason)
    await ctx.send(f"{member.mention} has been muted for {duration} minutes.")
    await asyncio.sleep(duration * 60)
    await member.remove_roles(mute_role)
    await ctx.send(f"{member.mention} has been unmuted.")
'''
    
    def get_music_commands(self):
        return '''
# Music Commands (requires discord.py[voice], yt-dlp)
import yt_dlp as youtube_dl

@bot.command(name="join")
async def join(ctx):
    if ctx.author.voice:
        channel = ctx.author.voice.channel
        await channel.connect()
        await ctx.send(f"Joined {channel}")
    else:
        await ctx.send("You need to be in a voice channel!")

@bot.command(name="leave")
async def leave(ctx):
    if ctx.voice_client:
        await ctx.voice_client.disconnect()
        await ctx.send("Disconnected from voice channel")

@bot.command(name="play")
async def play(ctx, url):
    if not ctx.voice_client:
        await join(ctx)
    
    ydl_opts = {'format': 'bestaudio'}
    with youtube_dl.YoutubeDL(ydl_opts) as ydl:
        info = ydl.extract_info(url, download=False)
        URL = info['formats'][0]['url']
    
    ctx.voice_client.play(discord.FFmpegPCMAudio(URL, **{'before_options': '-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5', 'options': '-vn'}))
    await ctx.send(f"Playing: {info['title']}")
'''
    
    def get_ai_chat_commands(self):
        return '''
# Enhanced AI Chat Integration
@bot.command(name="chat")
async def ai_chat(ctx, *, message):
    """Chat with AI"""
    # Integrate with parent AI engine
    response = self.parent.ai_engine.generate_response(message)
    await ctx.send(response)
    
@bot.command(name="learn")
async def ai_learn(ctx, input_text, *, output_text):
    """Teach the AI new responses"""
    self.parent.ai_engine.learn_response(input_text, output_text)
    await ctx.send("AI has learned the new response!")
'''
    
    def get_game_commands(self):
        return '''
# Game Commands
@bot.command(name="rps")
async def rps(ctx, choice: str):
    """Play Rock Paper Scissors"""
    choices = ["rock", "paper", "scissors"]
    bot_choice = random.choice(choices)
    if choice.lower() not in choices:
        await ctx.send("Invalid choice! Use rock, paper, or scissors.")
        return
    
    if choice.lower() == bot_choice:
        result = "It's a tie!"
    elif (choice.lower() == "rock" and bot_choice == "scissors") or \
         (choice.lower() == "paper" and bot_choice == "rock") or \
         (choice.lower() == "scissors" and bot_choice == "paper"):
        result = "You win!"
    else:
        result = "I win!"
    
    await ctx.send(f"You chose {choice}, I chose {bot_choice}. {result}")
    
@bot.command(name="guess")
async def guess(ctx, number: int):
    """Guess the number game"""
    secret = random.randint(1, 100)
    if number == secret:
        await ctx.send("Correct! You guessed the secret number!")
    elif number < secret:
        await ctx.send("Too low! Try a higher number.")
    else:
        await ctx.send("Too high! Try a lower number.")
'''
    
    def get_utility_commands(self):
        return '''
# Utility Commands
@bot.command(name="poll")
async def poll(ctx, question: str, *options: str):
    """Create a poll"""
    if len(options) < 2:
        await ctx.send("Need at least 2 options for a poll!")
        return
    poll_message = f"**Poll: {question}**\n"
    for i, option in enumerate(options, 1):
        poll_message += f"{i}️⃣ {option}\n"
    message = await ctx.send(poll_message)
    for i in range(1, len(options) + 1):
        await message.add_reaction(f"{i}\u20E3")

@bot.command(name="remind")
async def remind(ctx, time: int, *, reminder: str):
    """Set a reminder in minutes"""
    await ctx.send(f"Reminder set for {time} minutes: {reminder}")
    await asyncio.sleep(time * 60)
    await ctx.send(f"{ctx.author.mention} Reminder: {reminder}")
'''

class BotCreatorOS:
    def __init__(self):
        self.root_dir = os.path.dirname(os.path.abspath(__file__))
        self.boot_system = BootSystem(self.root_dir)
        self.ai_engine = AIEngine()
        
        # Directory structure
        self.bots_dir = os.path.join(self.root_dir, "Bots")
        self.discord_bots_dir = os.path.join(self.bots_dir, "Discord")
        self.feeds_dir = os.path.join(self.root_dir, "Feeds")
        self.saves_dir = os.path.join(self.root_dir, "Saves")
        self.scripts_dir = os.path.join(self.root_dir, "Scripts")
        self.services_dir = os.path.join(self.root_dir, "Services")
        self.user_dir = os.path.join(self.root_dir, "User")
        self.mods_dir = os.path.join(self.user_dir, "Mods")
        self.logs_dir = os.path.join(self.root_dir, "Logs")
        
        self.discord_creator = DiscordBotCreator(self)
        self.loaded_bots = {}
        self.active_bot = None
        self.boot_successful = False
        
        # Sudo System Integration
        self.user_store = UserStore(os.path.join(self.root_dir, "users.json"))
        self.dispatcher = Dispatcher(self.user_store)
        global dispatcher
        dispatcher = self.dispatcher  # For commands
        
        # Setup default users
        self.user_store.ensure_user('admin')
        if self.user_store.users['admin']['password'] is None:
            self.user_store.set_password('admin', 'adminpass')
        self.user_store.add_perm('admin', '*')
        self.user_store.ensure_user('guest')
        self.user_store.add_perm('guest', 'view')
        self.user_store.ensure_user('alice')
        self.user_store.add_perm('alice', 'say')
        self.user_store.add_perm('alice', 'sudo')
        self.user_store.ensure_user('bob')
        self.user_store.add_perm('bob', 'say')
        
        # Register app-specific commands
        registry.register('list_bots', self.cmd_list_bots, 'view')
        registry.register('reload_bots', self.cmd_reload_bots, 'admin')
        registry.register('whoami', cmd_whoami, None)
        registry.register('grant', cmd_grant, 'admin')
        registry.register('revoke', cmd_revoke, 'admin')
        registry.register('say', cmd_say, 'say')
        registry.register('echo', cmd_echo, None)
        registry.register('list_users', cmd_list_users, 'admin')
        registry.register('list_perms', cmd_list_perms, 'admin')
        registry.register('create_user', cmd_create_user, 'admin')
        registry.register('change_password', cmd_change_password, 'admin')
        registry.register('add_perm', cmd_add_perm, 'admin')
        registry.register('remove_perm', cmd_remove_perm, 'admin')
        registry.register('list_commands', cmd_list_commands, None)
        
        self.current_user = None
        
        self.setup_directories()
        self.create_default_files()
        self.init_gui()
    
    def cmd_list_bots(self, ctx: Context):
        return ', '.join(self.loaded_bots.keys())
    
    def cmd_reload_bots(self, ctx: Context):
        self.reload_all_bots()
        return "Bots reloaded successfully"
    
    def setup_directories(self):
        """Create all necessary directories"""
        directories = [
            self.bots_dir, self.discord_bots_dir, self.feeds_dir, self.saves_dir,
            self.scripts_dir, self.services_dir, self.user_dir, self.mods_dir,
            self.logs_dir, os.path.join(self.user_dir, "Boot")
        ]
        for directory in directories:
            os.makedirs(directory, exist_ok=True)
    
    def create_default_files(self):
        """Create default files with enhancements"""
        self.boot_system.ensure_boot_files()
        
        # Enhanced AI config
        ai_config_path = os.path.join(self.services_dir, "AI.conf")
        if not os.path.exists(ai_config_path):
            ai_config = """# Enhanced AI Engine Configuration
[AI]
enabled=true
model=advanced
response_delay=500
context_memory=20
learning_rate=0.5

[FEATURES]
auto_responses=true
learning=true
personality=dynamic
emotional_intelligence=true
"""
            with open(ai_config_path, 'w') as f:
                f.write(ai_config)
        
        # Enhanced Discord config
        discord_config_path = os.path.join(self.services_dir, "Discord.conf")
        if not os.path.exists(discord_config_path):
            discord_config = """# Enhanced Discord Configuration
[DISCORD]
enabled=true
default_prefix=!
auto_start=false
max_bots=10
webhook_support=true

[FEATURES]
moderation=true
music=true
ai_integration=true
custom_commands=true
games=true
utility=true
"""
            with open(discord_config_path, 'w') as f:
                f.write(discord_config)
        
        # New Logging config
        logging_config_path = os.path.join(self.services_dir, "Logging.conf")
        if not os.path.exists(logging_config_path):
            logging_config = """# Logging Service Configuration
[LOGGING]
enabled=true
level=INFO
rotate_days=7
max_size_mb=10

[FEATURES]
console_output=true
file_output=true
error_alerts=true
"""
            with open(logging_config_path, 'w') as f:
                f.write(logging_config)
        
        # New Sudo config
        sudo_config_path = os.path.join(self.services_dir, "Sudo.conf")
        if not os.path.exists(sudo_config_path):
            sudo_config = """# Sudo System Configuration
[SUDO]
enabled=true
session_timeout=300
log_level=INFO

[FEATURES]
impersonation=true
audit=true
password_required=true
"""
            with open(sudo_config_path, 'w') as f:
                f.write(sudo_config)
    
    def show_boot_sequence(self):
        """Show boot sequence with enhanced UI"""
        boot_window = customtkinter.CTkToplevel(self.window)
        boot_window.title("BotCreator OS - Boot Sequence v3")
        boot_window.geometry("700x600")
        boot_window.transient(self.window)
        boot_window.grab_set()
        
        title_label = customtkinter.CTkLabel(
            boot_window,
            text="🚀 BotCreator OS v3 Starting...",
            font=customtkinter.CTkFont(size=24, weight="bold")
        )
        title_label.pack(pady=20)
        
        console_frame = customtkinter.CTkFrame(boot_window)
        console_frame.pack(fill="both", expand=True, padx=20, pady=10)
        
        console_text = customtkinter.CTkTextbox(console_frame, font=("Consolas", 12))
        console_text.pack(fill="both", expand=True, padx=10, pady=10)
        
        progress_label = customtkinter.CTkLabel(boot_window, text="Initializing System...")
        progress_label.pack(pady=(10, 5))
        
        progress_bar = customtkinter.CTkProgressBar(boot_window, width=600)
        progress_bar.pack(fill="x", padx=20, pady=(0, 20))
        progress_bar.set(0)
        
        def update_console(name, priority, current, total):
            progress = current / total
            progress_bar.set(progress)
            progress_label.configure(text=f"Loading {name} ({current}/{total})")
            console_text.delete("1.0", tk.END)
            console_text.insert("1.0", "\n".join(self.boot_system.boot_log))
            console_text.see(tk.END)
            boot_window.update()
        
        def complete_boot():
            if self.boot_system.boot_success:
                progress_label.configure(text="✓ Boot Complete - System Optimized")
                messagebox.showinfo("Boot Success", "BotCreator OS v3 started successfully with enhancements!")
            else:
                progress_label.configure(text="⚠ Boot Completed with Recoveries")
                messagebox.showwarning("Boot Warning", "Some components were recovered automatically.")
            
            self.boot_successful = True
            self.update_dashboard()
            self.update_system_status()
            boot_window.destroy()
        
        threading.Thread(target=lambda: [self.boot_system.execute_boot_sequence(update_console), boot_window.after(500, complete_boot)]).start()
    
    def init_gui(self):
        """Initialize enhanced GUI with better theme and layout"""
        customtkinter.set_appearance_mode("dark")
        customtkinter.set_default_color_theme("dark-blue")
        
        self.window = customtkinter.CTk()
        self.window.title("BotCreator OS v3.0 - Enhanced Bot Development Platform")
        self.window.geometry("1600x1000")
        
        # Enhanced header with more elements
        header_frame = customtkinter.CTkFrame(self.window, height=90)
        header_frame.pack(fill="x", padx=10, pady=(10, 0))
        header_frame.pack_propagate(False)
        
        title_label = customtkinter.CTkLabel(
            header_frame,
            text="🤖 BotCreator OS v3",
            font=customtkinter.CTkFont(size=32, weight="bold")
        )
        title_label.pack(side="left", padx=20, pady=20)
        
        self.boot_status = customtkinter.CTkLabel(
            header_frame,
            text="⚠ Boot Required",
            font=customtkinter.CTkFont(size=16),
            text_color="orange"
        )
        self.boot_status.pack(side="right", padx=20, pady=20)
        
        boot_btn = customtkinter.CTkButton(
            header_frame,
            text="🚀 Launch OS",
            command=self.show_boot_sequence,
            height=50,
            font=customtkinter.CTkFont(size=16, weight="bold")
        )
        boot_btn.pack(side="right", padx=(0, 10), pady=20)
        
        self.tabview = customtkinter.CTkTabview(self.window)
        self.tabview.pack(fill="both", expand=True, padx=10, pady=10)
        
        self.create_dashboard_tab()
        self.create_bot_creator_tab()
        self.create_discord_tab()
        self.create_ai_lab_tab()
        self.create_chat_tab()
        self.create_manager_tab()
        self.create_system_tab()
        self.create_sudo_tab()
    
    def create_sudo_tab(self):
        """New Sudo Console Tab"""
        self.sudo_tab = self.tabview.add("🔒 Sudo")
        
        header_label = customtkinter.CTkLabel(
            self.sudo_tab,
            text="🔒 Sudo Command Console",
            font=customtkinter.CTkFont(size=26, weight="bold")
        )
        header_label.pack(pady=20)
        
        # Login section
        login_frame = customtkinter.CTkFrame(self.sudo_tab)
        login_frame.pack(pady=10, padx=20, fill="x")
        
        customtkinter.CTkLabel(login_frame, text="Username:").pack(anchor="w", pady=5)
        self.sudo_username = customtkinter.CTkEntry(login_frame)
        self.sudo_username.pack(fill="x")
        
        customtkinter.CTkLabel(login_frame, text="Password:").pack(anchor="w", pady=5)
        self.sudo_password = customtkinter.CTkEntry(login_frame, show="*")
        self.sudo_password.pack(fill="x")
        
        login_btn = customtkinter.CTkButton(login_frame, text="🔑 Login", command=self.sudo_login)
        login_btn.pack(pady=10)
        
        self.sudo_status = customtkinter.CTkLabel(login_frame, text="Not logged in", text_color="orange")
        self.sudo_status.pack(pady=5)
        
        # Command execution section
        cmd_frame = customtkinter.CTkFrame(self.sudo_tab)
        cmd_frame.pack(fill="both", expand=True, padx=20, pady=10)
        
        customtkinter.CTkLabel(cmd_frame, text="Command:").pack(anchor="w", pady=5)
        self.sudo_command = customtkinter.CTkEntry(cmd_frame, placeholder_text="e.g., list_bots or sudo -u admin reload_bots")
        self.sudo_command.pack(fill="x")
        
        exec_btn = customtkinter.CTkButton(cmd_frame, text="▶ Execute", command=self.sudo_execute)
        exec_btn.pack(pady=10)
        
        self.sudo_output = customtkinter.CTkTextbox(cmd_frame, font=("Consolas", 12))
        self.sudo_output.pack(fill="both", expand=True)
    
    def sudo_login(self):
        username = self.sudo_username.get().strip()
        password = self.sudo_password.get()
        if self.user_store.check_password(username, password):
            self.current_user = username
            self.sudo_status.configure(text=f"Logged in as {username}", text_color="green")
            messagebox.showinfo("Success", f"Logged in as {username}")
        else:
            self.sudo_status.configure(text="Invalid credentials", text_color="red")
            messagebox.showerror("Error", "Invalid username or password")
    
    def sudo_execute(self):
        if not self.current_user:
            messagebox.showwarning("Warning", "Please login first!")
            return
        
        command = self.sudo_command.get().strip()
        if not command:
            return
        
        output = self.dispatcher.run(self.current_user, command)
        self.sudo_output.insert(tk.END, f"> {command}\n{output}\n\n")
        self.sudo_output.see(tk.END)
        self.sudo_command.delete(0, tk.END)
    
    # Rest of the class remains the same, with possible integrations in other methods
    
    def run(self):
        logging.info("Starting BotCreator OS v3")
        self.load_all_bots()
        self.update_dashboard()
        self.refresh_bot_list()
        self.window.mainloop()

# Main
if __name__ == "__main__":
    app = BotCreatorOS()
    app.run()
