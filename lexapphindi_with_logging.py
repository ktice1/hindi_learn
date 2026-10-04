import random
import sys
import time
import json
import os
from datetime import datetime
import re
from collections import deque
from collections import defaultdict
import unicodedata

# --- CONFIGURATION ---
SYLLABLES_FILE = 'my-bookmarks.txt'
DICTIONARY_FILE = 'hi_IN.txt'
JSON_FILE = 'stats_pro.json'
REPORT_FILE = 'MY_PROGRESS.txt'
LOG_FILE = 'lexlog.txt'

BOOKMARK_LINE_RE = re.compile(
    r"^\s*(\S+?)\s*(?:\(\s*(\d+)\s*\)|\s+(\d+))?\s*$"
)
HYPHEN_EQUIV = {
    "\u2010": "-",  # hyphen
    "\u2011": "-",  # non-breaking hyphen
    "\u2012": "-",  # figure dash
    "\u2013": "-",  # en dash
    "\u2014": "-",  # em dash
    "\u2212": "-",  # minus sign
}

TARGET_POOL = 25
HELP_CACHE = {}

# Regen letters are the only characters considered when generating
# regeneration value. Their values are calculated from the actual
# frequency of these letters in the loaded dictionary.
REGEN_LETTER_ORDER = "अ ए क ख ग च ज ट ड त द ध न प ब भ म य र ल व श ष स ह".split()
REGEN_LETTERS = set(REGEN_LETTER_ORDER)

# Populated once when the dictionary is loaded.
REGEN_FREQUENCIES = {}
REGEN_VALUES = {}


# Word Bomb / Hindi equivalencies.
# Each prompt maps to every form that should count as equivalent.
HINDI_EQUIVALENCIES = {
    "षत": ["षत", "क्षत"],
    "र्ऋ": ["र्ऋ", "त्रृ"],
    "ख": ["ख", "ख़"],
}


def normalize_token(s: str) -> str:
    s = s.strip()

    for bad, good in HYPHEN_EQUIV.items():
        s = s.replace(bad, good)
    s = re.sub(r"\s+", "-", s)
    return unicodedata.normalize("NFC", s)


def log_turn(prompt, solution):
    """Append one completed player turn to lexlog.txt."""
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"{normalize_token(prompt)}\t{normalize_token(solution)}\n")
    except OSError as e:
        print(f"⚠️ Could not write to {LOG_FILE}: {e}")


def get_equivalent_forms(syllable):
    """
    Return every form that should be treated as equivalent
    to this syllable for solution matching.
    """
    key = normalize_token(syllable)

    forms = HINDI_EQUIVALENCIES.get(key)

    if forms is None:
        return [key]

    return list(dict.fromkeys(
        normalize_token(form)
        for form in forms
    ))


# --- ASCII Hindi transliteration (candidate-based) ---
# Lowercase-only, deliberately permissive phonetic spellings. Ambiguous spellings
# produce multiple candidates; dictionary membership decides which are viable.
ROMAN_CONSONANTS = {
    "k": "क", "kh": "ख", "g": "ग", "gh": "घ", "ng": "ङ",
    "ch": "च", "chh": "छ", "j": "ज", "jh": "झ", "ny": "ञ",
    "t": "त", "th": "थ", "d": "द", "dh": "ध", "n": "न",
    "tt": "ट", "tth": "ठ", "dd": "ड", "ddh": "ढ", "nn": "ण",
    "p": "प", "ph": "फ", "f": "फ़", "b": "ब", "bh": "भ", "m": "म",
    "y": "य", "r": "र", "l": "ल", "ll": "ळ", "v": "व", "w": "व",
    "sh": ("श", "ष"), "s": ("स", "श", "ष"), "h": "ह",
    "q": ("क़", "क"), "z": ("ज़", "ज"), "x": "क्ष", "tr": "त्र", "gy": ("ज्ञ", "ग्य"),
    "ksh": ("क्ष", "क्श"), "jn": ("ज्ञ", "ज्न"), "shr": "श्र",
    "kh": ("ख", "ख़"), "gh": ("घ", "ग़"), "j": ("ज", "ज़"),
    "d": ("द", "ड", "ड़"), "dh": ("ध", "ढ", "ढ़"), "ph": ("फ", "फ़"),
    "r": ("र", "ऱ"), "l": ("ल", "ळ"),
}
ROMAN_VOWELS = {
    "a": ("", "ा"), "aa": "ा", "i": "ि", "ee": "ी", "ii": "ी",
    "u": "ु", "oo": "ू", "uu": "ू", "e": "े", "ai": "ै",
    "o": "ो", "au": "ौ", "ri": "ृ", "rri": "ॄ",
    "ou": "ौ", "oi": "ै", "aw": ("ॉ", "ो"), "om": "ं", "an": ("ं", "ँ"),
    "m": ("ं", "ँ"), "n": ("ं", "ँ"),
}
INDEPENDENT_VOWELS = {"a":"अ", "aa":"आ", "i":"इ", "ee":"ई", "ii":"ई",
                      "u":"उ", "oo":"ऊ", "uu":"ऊ", "e":"ए", "ai":"ऐ",
                      "o":"ओ", "au":"औ", "ri":"ऋ", "rri":"ॠ", "ou":"औ", "oi":"ऐ", "aw":"ऑ"}
VIRAMA = "्"


def transliterate_candidates(text, dictionary=None, max_candidates=12000):
    """Return plausible Devanagari candidates for lowercase ASCII phonetic input."""
    raw = text.strip().lower()
    if not raw or not raw.isascii() or not re.fullmatch(r"[a-z~^: -]+", raw):
        return []
    raw = raw.replace(" ", "-")
    # Longest-first token matching; branch on alternate mappings and vowel ambiguity.
    consonant_keys = sorted(ROMAN_CONSONANTS, key=len, reverse=True)
    vowel_keys = sorted(ROMAN_VOWELS, key=len, reverse=True)
    memo = {}
    def walk(i, pending=False):
        key=(i,pending)
        if key in memo: return memo[key]
        if i == len(raw):
            return [""]
        if raw[i] == "-":
            return ["-" + tail for tail in walk(i+1, False)]
        # Explicit diacritic controls: ~ = chandrabindu, ^ = anusvara, : = visarga.
        # They may follow a consonant or vowel and are emitted literally.
        marker_map = {"~": "ँ", "^": "ं", ":": "ः"}
        if raw[i] in marker_map:
            mark = marker_map[raw[i]]
            return [mark + tail for tail in walk(i+1, False)]
        out=[]
        if pending:
            for vk in vowel_keys:
                if raw.startswith(vk,i):
                    val=ROMAN_VOWELS[vk]
                    vals=val if isinstance(val,tuple) else (val,)
                    for v in vals:
                        for tail in walk(i+len(vk),False): out.append(v+tail)
            # inherent vowel / schwa: allow no written matra
            for tail in walk(i,False): out.append(VIRAMA+tail)
        else:
            for vk in vowel_keys:
                if raw.startswith(vk,i):
                    for tail in walk(i+len(vk),False): out.append(INDEPENDENT_VOWELS[vk]+tail)
            for ck in consonant_keys:
                if raw.startswith(ck,i):
                    val=ROMAN_CONSONANTS[ck]
                    vals=val if isinstance(val,tuple) else (val,)
                    for c in vals:
                        for tail in walk(i+len(ck),True): out.append(c+tail)
            # Conjunct path: adjacent Roman consonant tokens may form C्C.
            # Keep ordinary parses too; dictionary filtering resolves ambiguity.
            for ck in consonant_keys:
                if raw.startswith(ck, i):
                    val1 = ROMAN_CONSONANTS[ck]
                    vals1 = val1 if isinstance(val1, tuple) else (val1,)
                    j = i + len(ck)
                    for ck2 in consonant_keys:
                        if raw.startswith(ck2, j):
                            val2 = ROMAN_CONSONANTS[ck2]
                            vals2 = val2 if isinstance(val2, tuple) else (val2,)
                            for c1 in vals1:
                                for c2 in vals2:
                                    for tail in walk(j + len(ck2), True):
                                        out.append(c1 + VIRAMA + c2 + tail)
        # bound explosion while retaining deterministic variety
        memo[key]=list(dict.fromkeys(out))[:max_candidates]
        return memo[key]
    candidates=walk(0,False)
    cleaned=set()
    for c in candidates:
        c=unicodedata.normalize("NFC", ctarg)
        # Drop trailing virama generated by an omitted final inherent vowel only
        if c.endswith(VIRAMA): c=c[:-1]
        if c: cleaned.add(c)
    if dictionary is not None:
        cleaned={c for c in cleaned if c in dictionary}
    return sorted(cleaned)


def transliterator_audit(sample_path, dictionary):
    """Audit sample words for basic representability and report missing feature classes.

    This is a conservative structural audit: it flags unsupported Devanagari
    codepoints and normalization concerns. Full reverse-search proof requires
    enumerating roman encodings, which is deliberately not guessed here.
    """
    unsupported = set()
    rows = []
    try:
        with open(sample_path, "r", encoding="utf-8-sig") as f:
            words = [normalize_token(line) for line in f if line.strip()]
    except OSError as e:
        print(f"Could not read {sample_path}: {e}")
        return
    known = set("अआइईउऊऋॠऌॡएऐओऔऑकखगघङचछजझञटठडढणतथदधनपफबभमयरलवशषसहळक़ख़ग़ज़ड़ढ़फ़़ािीुूृॄॅॉेैोौंँः्- ")
    for word in words:
        missing = sorted(set(ch for ch in word if ch not in known))
        categories = []
        if missing: categories.append("unsupported character(s): " + "".join(missing))
        if "ँ" in word: categories.append("chandrabindu mapping/placement")
        if "ं" in word: categories.append("anusvara mapping/placement")
        if "ः" in word: categories.append("visarga mapping")
        if any(ch in word for ch in "क़ख़ग़ज़ड़ढ़फ़"): categories.append("nukta-letter aliases")
        if "ॉ" in word or "ऑ" in word: categories.append("aw/au-style vowel variants")
        if any(ch in word for ch in "्"): categories.append("conjunct/virama composition")
        if "-" in word: categories.append("hyphen handling")
        rows.append((word, categories))
    passed = sum(not cats for _, cats in rows)
    print(f"Structural audit: {passed}/{len(rows)} words contain only recognized script characters.")
    print("Note: recognized characters do not prove that a Roman input currently generates the exact word.")
    counts = defaultdict(int)
    for _, cats in rows:
        for c in cats: counts[c] += 1
    print("Feature flags:")
    for category, count in sorted(counts.items(), key=lambda x: (-x[1], x[0])):
        print(f"  {count:4}  {category}")
    out_path = os.path.splitext(sample_path)[0] + "_audit.txt"
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"Structural audit: {passed}/{len(rows)}\n")
        for word, cats in rows:
            f.write(f"{word}\t{' | '.join(cats) if cats else 'no structural flags'}\n")
    print(f"Detailed audit saved to: {out_path}")


def load_resources():
    print("📊 Starting Neuro-Trainer V8 (Forgiving Algorithm)...", end="")

    syllables = []
    wps_map = {}

    try:
        with open(SYLLABLES_FILE, 'r', encoding='utf-8') as f:
            for raw in f:
                line = raw.strip()
                if not line:
                    continue

                m = BOOKMARK_LINE_RE.match(line)
                if not m:
                    continue

                syl = normalize_token(m.group(1))
                wps = m.group(2)

                syllables.append(syl)
                if wps is not None:
                    wps_map[syl] = int(wps)

    except FileNotFoundError:
        print(f"\n❌ Missing '{SYLLABLES_FILE}'")
        sys.exit()

    try:
        with open(DICTIONARY_FILE, 'r', encoding='utf-8') as f:
            dic_set = set(
                normalize_token(line)
                for line in f
                if line.strip()
            )
            dic_list = list(dic_set)
    except FileNotFoundError:
        print(f"\n❌ Missing '{DICTIONARY_FILE}'")
        sys.exit()

    # Calibrate Regen from the actual dictionary vocabulary once at startup.
    initialize_regen_scores(dic_list)

    print(" Ready!\n")
    return syllables, wps_map, dic_set, dic_list


def new_syllable_stats():
    return {
        "views": 0,
        "hits": 0,
        "misses": 0,
        "short_answers": [],
        "best_time": 99.9,
        "last_seen": -1,
        "mastery": "learning",
        "fluency_hits": 0,
        "fluency_mastered": False,
        "stacker": {
            "attempts": 0,
            "full_clears": 0,
            "best_found": 0,
            "last_found_count": 0,
            "last_stacked_turn": -1,
            "retention_passes": 0,
            "fully_mastered": False,
            "missing_counts": {}
        }
    }


def new_stacker_stats():
    return {
        "attempts": 0,
        "full_clears": 0,
        "best_found": 0,
        "last_found_count": 0,
        "last_stacked_turn": -1,
        "retention_passes": 0,
        "fully_mastered": False,
        "missing_counts": {}
    }


def load_stats():
    base = {
        "global": {
            "total_plays": 0,
            "total_hits": 0,
            "total_misses": 0,
            "best_historical_streak": 0,
            "total_accumulated_time": 0,
            "last_session_date": ""
        },
        "syllables": {},
        "turn_count": 0
    }

    if os.path.exists(JSON_FILE):
        try:
            with open(JSON_FILE, 'r', encoding='utf-8') as f:
                d = json.load(f)

            if "global" not in d:
                d["global"] = base["global"]
            if "syllables" not in d:
                d["syllables"] = base["syllables"]
            if "turn_count" not in d:
                d["turn_count"] = 0

            for s, data in d.get("syllables", {}).items():
                defaults = new_syllable_stats()
                for k, v in defaults.items():
                    data.setdefault(k, v)

                stacker_defaults = new_stacker_stats()
                if "stacker" not in data or not isinstance(data["stacker"], dict):
                    data["stacker"] = stacker_defaults.copy()
                else:
                    for k, v in stacker_defaults.items():
                        data["stacker"].setdefault(k, v)

                if data.get("last_seen", -1) == -1:
                    data["last_seen"] = 0

                if data["mastery"] == "learning" and data.get("hits", 0) >= 4:
                    data["mastery"] = "mastered"

            return d

        except Exception:
            return base

    return base


def save_stats(stats, total_syllables_count, turn_count):
    stats["global"]["last_session_date"] = datetime.now().strftime("%Y-%m-%d %H:%M")
    stats["turn_count"] = turn_count
    try:
        with open(JSON_FILE, 'w', encoding='utf-8') as f:
            json.dump(stats, f, indent=4, ensure_ascii=False)
        generate_detailed_report(stats, total_syllables_count)
    except Exception as e:
        print(f"Error saving: {e}")


def calculate_rank(total_hits):
    if total_hits < 50:
        return "Letter Novice"
    if total_hits < 150:
        return "Verbal Apprentice"
    if total_hits < 300:
        return "Lexicon Adept"
    if total_hits < 600:
        return "Syllable Master"
    if total_hits < 1000:
        return "Grand Sage"
    return "GOD OF THE DICTIONARY"


def generate_progress_bar(value, total, length=20):
    if total == 0:
        return f"[{'░' * length}] 0%"
    percentage = value / total
    filled = int(length * percentage)
    empty = length - filled
    return f"[{'█' * filled}{'░' * empty}] {int(percentage * 100)}%"


def generate_detailed_report(stats, total_possible_syllables):
    g = stats["global"]
    total_plays = g.get('total_plays', 0)
    hits = g.get('total_hits', 0)
    acc_time = g.get('total_accumulated_time', 0)

    syllables_stats = stats["syllables"]
    mastered = sum(1 for v in syllables_stats.values() if v.get("hits", 0) >= 4)
    registered = len(syllables_stats)
    in_process = registered - mastered
    untouched = max(0, total_possible_syllables - registered)

    avg_speed = (acc_time / hits) if hits > 0 else 0.0

    with open(REPORT_FILE, 'w', encoding='utf-8') as f:
        f.write("╔══════════════════════════════════════════════════╗\n")
        f.write("║                TRAINING DASHBOARD                ║\n")
        f.write("╚══════════════════════════════════════════════════╝\n")
        f.write(f"📅 Last Session: {datetime.now().strftime('%d/%m/%Y %H:%M')}\n\n")

        rank = calculate_rank(hits)
        f.write(f"👤 CURRENT RANK:  {rank.upper()}\n")
        f.write(f"🎯 Accuracy:      {(hits / total_plays * 100) if total_plays > 0 else 0:.1f}%\n")
        f.write(f"⚡ Avg Speed:     {avg_speed:.2f} seconds/word\n")
        f.write(f"🔥 Best Streak:   {g.get('best_historical_streak', 0)}\n\n")

        f.write("🏆 MASTERY PROGRESS (Syllables with 4+ hits)\n")
        bar = generate_progress_bar(mastered, total_possible_syllables)
        f.write(f"{bar}\n")
        f.write(f"   • Mastered:    {mastered}\n")
        f.write(f"   • Learning:    {in_process}\n")
        f.write(f"   • Pending:     {untouched}\n\n")

        f.write("🚀 HALL OF FAME (Your fastest syllables)\n")
        f.write("-" * 50 + "\n")
        fastest = sorted(
            [item for item in syllables_stats.items() if item[1].get('hits', 0) > 0],
            key=lambda x: x[1].get('best_time', 99.9)
        )[:5]
        if fastest:
            for syl, data in fastest:
                f.write(f"   ★ {syl:<6} -> {data['best_time']}s ({data['hits']} hits)\n")
        else:
            f.write("   (Hit words correctly to enter here)\n")
        f.write("\n")

        f.write("💀 YOUR WORST ENEMIES (Most misses)\n")
        f.write("-" * 50 + "\n")
        worst = sorted(
            [item for item in syllables_stats.items() if item[1].get('misses', 0) > 0],
            key=lambda x: x[1].get('misses', 0),
            reverse=True
        )[:100]

        if worst:
            for syl, data in worst:
                rate = data['misses'] / (data['misses'] + data['hits']) * 100
                shorts = data.get('short_answers', [])
                f.write(f"   🔴 {syl:<6} | {data['misses']} misses ({int(rate)}% error)\n")
                f.write(f"      👉 Study: {', '.join(shorts)}\n")
        else:
            f.write("   (Clean record! Keep it up)\n")


def get_help(syllable, dictionary_list):
    key = normalize_token(syllable)

    if key in HELP_CACHE:
        return HELP_CACHE[key]

    equivalent_forms = get_equivalent_forms(key)

    matches = [
        word
        for word in dictionary_list
        if any(form in word for form in equivalent_forms)
    ]

    matches.sort(key=len)

    HELP_CACHE[key] = matches
    return matches


def generate_visual_mask(word, syllable):
    s_norm = normalize_token(syllable)
    try:
        start_idx = word.find(s_norm)
        if start_idx == -1:
            return "_" * len(word)
        prefix = "_ " * start_idx
        suffix = " _" * (len(word) - start_idx - len(syllable))
        return f"{prefix}[{normalize_token(syllable)}]{suffix}"
    except Exception:
        return "ERROR_MASK"


def select_strategic_syllable(stats, all_syllables):
    unmastered = []
    unmastered_weights = []
    mastered_candidates = []

    for s in all_syllables:
        data = stats["syllables"].get(s)
        if not data:
            continue

        hits = data.get("hits", 0)
        misses = data.get("misses", 0)
        mastery = data.get("mastery", "learning")
        last_seen = data.get("last_seen", -1)

        if mastery == "mastered":
            mastered_candidates.append((s, last_seen))
        else:
            weight = 10 + (misses * 40) - (hits * 20)
            weight = max(weight, 2)
            unmastered.append(s)
            unmastered_weights.append(weight)

    if unmastered and random.random() < 0:
        target = random.choices(unmastered, weights=unmastered_weights, k=1)[0]
        is_review = False
    elif mastered_candidates:
        mastered_candidates.sort(key=lambda x: x[1])
        top_oldest = [s for s, _ in mastered_candidates[:50]]
        target = random.choice(top_oldest)
        is_review = True
    else:
        target = random.choices(unmastered, weights=unmastered_weights, k=1)[0]
        is_review = False

    s_data = stats["syllables"][target]
    s_data["last_seen"] = stats["turn_count"]

    return target, is_review


def get_assigned_stacker_solves(target, dic_list, wps_map, stack_size=4):
    assigned = wps_map.get(target)

    if assigned is None or assigned < 1:
        return None, [], f"[{target}] has no valid assigned solve count."

    required = min(assigned, stack_size)
    all_matches = get_help(target, dic_list)
    unique_solves = sorted(set(normalize_token(w) for w in all_matches))
    chosen = unique_solves[:required]

    if len(chosen) < required:
        return required, chosen, f"[{target}] needs {required} solves, but dictionary only has {len(chosen)}."

    return required, chosen, None

def set_all_prompts_mastered(stats, syllables, wps_map=None):
    for s in syllables:
        data = stats["syllables"].setdefault(s, new_syllable_stats())

        data["hits"] = max(data.get("hits", 0), 4)
        data["mastery"] = "mastered"

        # Optional: fully complete stacker progress too
        if wps_map and s in wps_map:
            assigned = wps_map.get(s)

            if isinstance(assigned, int) and assigned > 0:
                stack = data.setdefault("stacker", new_stacker_stats())

                stack["attempts"] = max(stack.get("attempts", 0), 2)
                stack["full_clears"] = max(stack.get("full_clears", 0), 2)
                stack["best_found"] = max(stack.get("best_found", 0), assigned)
                stack["last_found_count"] = assigned
                stack["retention_passes"] = max(stack.get("retention_passes", 0), 1)
                stack["fully_mastered"] = True


def play_turn(target, dic_set, time_limit, possible_solutions, mode_label, stats, wps_map):
    start_time = time.time()
    limit = start_time + time_limit
    hint_word = possible_solutions[0] if possible_solutions else "???"
    hint_level = 0

    data_sil = stats["syllables"].get(target, {})

    if "RANDOM" not in mode_label:
        if data_sil.get("mastery") == "mastered":
            mode_label = "🌟 MASTERY"
        elif "REVIEW" in mode_label:
            mode_label = "🧠 REVIEW"
        else:
            mode_label = "🔥 ATTACK"

    wps = wps_map.get(target)
    wps_txt = f" | {wps}" if wps is not None else ""
    print(f"\n>>> {mode_label}: [{normalize_token(target)}] ({time_limit}s){wps_txt}")

    while True:
        remaining = limit - time.time()
        if remaining <= 0:
            return False, 0, hint_level > 0

        try:
            prompt = f"   ({int(remaining)}s): "
            if hint_level == 1:
                prompt = f"   ({int(remaining)}s) [Starts with '{hint_word[0]}...']: "
            elif hint_level == 2:
                prompt = f"   ({int(remaining)}s) {generate_visual_mask(hint_word, target)}: "

            raw = input(prompt)
            txt = normalize_token(raw)
            # ASCII phonetic input is expanded into dictionary-backed candidates.
            # Direct Devanagari input remains supported unchanged.
            if txt and txt.isascii() and re.fullmatch(r"[a-z]+", txt.lower()):
                candidates = transliterate_candidates(txt, dic_set)
                matching = [candidate for candidate in candidates if candidate in possible_solutions]
                if matching:
                    txt = matching[0]
                elif candidates:
                    txt = candidates[0]
        except EOFError:
            return False, 0, True

        if time.time() > limit:
            return False, 0, True
        if not txt:
            continue
        
        if txt == "x":
            return False, 0, False
        if txt == "क्ष":
            return False, 0, False

        if txt in ['hint', 'help', 'clue']:
            if not possible_solutions:
                print("      ⚠️ No solutions available.")
                continue
            hint_level += 1
            limit -= 4
            if hint_level == 1:
                print(f"      💡 HINT: '{hint_word[0].upper()}' ({len(hint_word)} letters).")
            elif hint_level >= 2:
                print(f"      🦴 SKELETON: {generate_visual_mask(hint_word, target)}")
            continue

        if txt not in dic_set:
            print("      ⚠️ Unknown word.")
            continue

        if txt not in possible_solutions:
            print(f"      ⚠️ '{txt}' is not a solution for '{target}'.")
            continue

        log_turn(target, txt)
        return True, time.time() - start_time, hint_level > 0

def play_graduation_turn(target, dic_set, possible_solutions, time_limit=None):
    print(f"\n🎓 [{normalize_token(target)}]")

    if time_limit is None:
        txt = normalize_token(input("   ➤ "))
    else:
        start = time.time()

        txt = normalize_token(
            input(f"   ({time_limit:.1f}s) ➤ ")
        )

        if time.time() - start > time_limit:
            print("      ⏰ Time!")
            return False

    if not txt:
        return False

    if normalize_token(target) not in txt:
        return False

    if txt not in dic_set:
        return False

    log_turn(target, txt)
    return True


def play_solve_stacker_turn(target, dic_set, dic_list, wps_map, stack_size=4):
    assigned = wps_map.get(target)

    if assigned is None or assigned < 1:
        print(f"      ⚠️ [{target}] has no valid assigned solve count.")
        return None

    all_matches = get_help(target, dic_list)
    valid_solves = sorted(set(normalize_token(w) for w in all_matches))

    if not valid_solves:
        print(f"      ⚠️ No solutions available for [{target}].")
        return None

    required = min(stack_size, assigned, len(valid_solves))
    remaining = set(valid_solves)
    found = []
    mistakes = 0

    print(f"\n🧩 SOLVE STACKER: [{target}]")
    print(f"   Need {required} solve(s) to pass.", end="")
    if len(valid_solves) > required:
        print(" Type more if you want, then type FINISH.")
    else:
        print()

    while True:
        raw = input(f"   {len(found)}/{required} required | {len(found)}/{len(valid_solves)} total ➤ ")
        txt = normalize_token(raw)

        if not txt:
            continue

        if txt in ["giveup", "skip", "quit"]:
            print("      ❌ Stack abandoned.")
            return {
                "success": False,
                "found": found,
                "missing": [w for w in valid_solves if w not in found],
                "total": len(valid_solves),
                "required": required,
                "mistakes": mistakes,
                "valid_solves": valid_solves
            }

        if txt == "finish":
            if len(found) >= required:
                print("      ✅ Stack finished.")
                return {
                    "success": True,
                    "found": found,
                    "missing": [w for w in valid_solves if w not in found],
                    "total": len(valid_solves),
                    "required": required,
                    "mistakes": mistakes,
                    "valid_solves": valid_solves
                }
            else:
                print(f"      ⚠️ You need at least {required} solves before finishing.")
                continue

        if normalize_token(target) not in txt:
            print(f"      ⚠️ Missing '{target}'.")
            continue

        if txt not in dic_set:
            print("      ⚠️ Unknown word.")
            continue

        if txt not in valid_solves:
            print("      ❌ Valid dictionary word, but not one of this prompt's solves.")
            mistakes += 1
            continue

        if txt in found:
            print("      ♻️ Already found.")
            continue

        found.append(txt)
        remaining.remove(txt)
        log_turn(target, txt)
        print(f"      ✅ {txt.upper()} ({len(found)}/{len(valid_solves)})")

        if not remaining:
            print("      🏁 Full stack complete!")
            return {
                "success": True,
                "found": found,
                "missing": [],
                "total": len(valid_solves),
                "required": required,
                "mistakes": mistakes,
                "valid_solves": valid_solves
            }

        if len(found) == required and len(valid_solves) > required:
            print("      💡 Minimum reached — type more solves or type FINISH.")


def pause_for_space():
    while True:
        key = input("      ⏸️  Press SPACE then Enter to continue... ")
        if key == " ":
            break


def ew_prompts(stats, all_syllables, batch_size=25):
    inactive = [s for s in all_syllables if s not in stats["syllables"]]

    if not inactive:
        return 0

    random.shuffle(inactive)
    to_add = inactive[:min(batch_size, len(inactive))]

    for s in to_add:
        stats["syllables"][s] = new_syllable_stats()

    if not inactive:
        return 0

    return len(to_add)


def update_stacker_stats(s_data, result, turn_count):
    stack = s_data["stacker"]
    old_last_stacked_turn = stack.get("last_stacked_turn", -1)

    stack["attempts"] += 1
    stack["last_found_count"] = len(result["found"])
    stack["best_found"] = max(stack.get("best_found", 0), len(result["found"]))
    stack["last_stacked_turn"] = turn_count

    if result["success"]:
        stack["full_clears"] += 1

        if old_last_stacked_turn != -1 and (turn_count - old_last_stacked_turn) >= 10:
            stack["retention_passes"] += 1

    missing_counts = stack.setdefault("missing_counts", {})
    for word in result.get("missing", []):
        missing_counts[word] = missing_counts.get(word, 0) + 1

    if stack["full_clears"] >= 2 and stack["retention_passes"] >= 1:
        stack["fully_mastered"] = True


def pre_scan_syllables(syllables, dic_list, min_solutions=1):
    """
    Validate every syllable against the dictionary using the same
    equivalency-aware logic that Smart Mode will use.
    """

    print("\n🔎 PRE-SCANNING SYLLABLES...")

    low_coverage = []

    for syllable in syllables:
        solutions = get_help(syllable, dic_list)

        count = len(solutions)

        if count < min_solutions:
            low_coverage.append((syllable, solutions))

    if low_coverage:
        print(
            f"\n⚠️ SYLLABLES WITH FEWER THAN "
            f"{min_solutions} SOLUTIONS:"
        )

        for syllable, solutions in low_coverage:
            print(f"\n  • {syllable} → {len(solutions)} solution(s)")

            if solutions:
                for word in solutions:
                    print(f"      {word}")
            else:
                print("      NO SOLUTIONS FOUND")

    else:
        print(
            f"\n✅ All syllables have at least "
            f"{min_solutions} solution(s).\n"
        )

    return low_coverage


def select_with_cooldown(select_fn, recent, max_attempts=25):
    for _ in range(max_attempts):
        target, is_review = select_fn()
        if target not in recent:
            return target, is_review

    return select_fn()


def handle_mastery_unlock(stats, all_syllables):
    valid = set(all_syllables)

    active = sum(
        1 for s, v in stats["syllables"].items()
        if s in valid and v.get("hits", 0) < 4
    )

    if active > TARGET_POOL:
        excess = active - TARGET_POOL
        print(f"      📉 Pool over target by {excess} — unlock deferred.")
        return False

    inactive = [s for s in all_syllables if s not in stats["syllables"]]
    if inactive:
        s = random.choice(inactive)
        stats["syllables"][s] = new_syllable_stats()
        print("      🆕 New prompt unlocked!")
        return True

    return False


def get_active_prompts(stats, all_syllables):
    valid = set(all_syllables)
    return sorted(
        s for s, data in stats["syllables"].items()
        if s in valid and data.get("hits", 0) < 4
    )


def build_regen_frequencies(dictionary):
    """Count occurrences of the eligible Regen letters in the dictionary."""
    frequencies = {ch: 0 for ch in REGEN_LETTER_ORDER}

    for word in dictionary:
        for ch in word:
            if ch in REGEN_LETTERS:
                frequencies[ch] += 1

    return frequencies


def build_regen_values(frequencies):
    """Convert dictionary frequencies into damped inverse-frequency rarity values."""
    nonzero = [freq for freq in frequencies.values() if freq > 0]
    if not nonzero:
        return {ch: 0.0 for ch in REGEN_LETTER_ORDER}

    max_frequency = max(nonzero)
    values = {}
    for ch in REGEN_LETTER_ORDER:
        frequency = frequencies[ch]
        if frequency <= 0:
            values[ch] = 10.0
        else:
            values[ch] = 10.0 * (max_frequency / frequency) ** 0.5
    return values


def initialize_regen_scores(dictionary):
    """Build and cache Regen frequencies and rarity values for this dictionary."""
    global REGEN_FREQUENCIES, REGEN_VALUES
    REGEN_FREQUENCIES = build_regen_frequencies(dictionary)
    REGEN_VALUES = build_regen_values(REGEN_FREQUENCIES)


def regen_score(word):
    """Score a word using dictionary-derived rarity plus a small diversity bonus."""
    base = 0.0
    seen = set()

    for ch in word:
        if ch in REGEN_LETTERS:
            base += REGEN_VALUES.get(ch, 0.0)
            seen.add(ch)

    # Small bonus for using several different eligible letters.
    diversity_bonus = 0.75 * len(seen)
    return base + diversity_bonus

def load_fluency_pool(filename):
    pool = []

    try:
        with open(filename, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()

                if not line:
                    continue

                m = BOOKMARK_LINE_RE.match(line)

                if m:
                    pool.append(m.group(1).upper())

    except FileNotFoundError:
        print(f"❌ Missing {filename}")
        sys.exit()

    return pool




# Approximate Devanagari -> ASCII helper for post-failure study display.
# Unknown characters are shown as ?? rather than silently omitted.
DEV_TO_ROMAN = {
    "अ":"a","आ":"aa","इ":"i","ई":"ii","उ":"u","ऊ":"uu","ऋ":"ri","ॠ":"rri",
    "ए":"e","ऐ":"ai","ओ":"o","औ":"au","ऑ":"aw",
    "क":"k","ख":"kh","ग":"g","घ":"gh","ङ":"ng","च":"ch","छ":"chh","ज":"j","झ":"jh","ञ":"ny",
    "ट":"tt","ठ":"tth","ड":"dd","ढ":"ddh","ण":"nn","त":"t","थ":"th","द":"d","ध":"dh","न":"n",
    "प":"p","फ":"ph","ब":"b","भ":"bh","म":"m","य":"y","र":"r","ल":"l","ळ":"ll","व":"v",
    "श":"sh","ष":"sh","स":"s","ह":"h","क़":"q","ख़":"kh","ग़":"gh","ज़":"z","ड़":"dd","ढ़":"ddh","फ़":"f",
    "़":"", "ा":"aa","ि":"i","ी":"ii","ु":"u","ू":"uu","ृ":"ri","ॄ":"rri","ॅ":"e","ॉ":"aw",
    "े":"e","ै":"ai","ो":"o","ौ":"au","ं":"^","ँ":"~","ः":":","्":"",
}
_CONS_ROMAN = {
    "क":"k","ख":"kh","ग":"g","घ":"gh","ङ":"ng","च":"ch","छ":"chh","ज":"j","झ":"jh","ञ":"ny",
    "ट":"tt","ठ":"tth","ड":"dd","ढ":"ddh","ण":"nn","त":"t","थ":"th","द":"d","ध":"dh","न":"n",
    "प":"p","फ":"ph","ब":"b","भ":"bh","म":"m","य":"y","र":"r","ल":"l","ळ":"ll","व":"v",
    "श":"sh","ष":"sh","स":"s","ह":"h","क़":"q","ख़":"kh","ग़":"gh","ज़":"z","ड़":"dd","ढ़":"ddh","फ़":"f",
}
_MATRA_ROMAN = {"ा":"aa","ि":"i","ी":"ii","ु":"u","ू":"uu","ृ":"ri","ॄ":"rri","ॅ":"e","ॉ":"aw","े":"e","ै":"ai","ो":"o","ौ":"au"}
def approximate_roman(word):
    out=[]
    i=0
    while i < len(word):
        ch=word[i]
        if ch in _CONS_ROMAN:
            out.append(_CONS_ROMAN[ch])
            if i+1 < len(word) and word[i+1] == "्":
                i += 2
                continue
            # Inherent 'a' is approximate; visible matra after consonant handled next.
            out.append("a")
        elif ch in _MATRA_ROMAN:
            # Remove inherent vowel before replacing with the explicit matra.
            if out and out[-1] == "a":
                out.pop()
            out.append(_MATRA_ROMAN[ch])
        elif ch == "्":
            if out and out[-1] == "a":
                out.pop()
        elif ch in DEV_TO_ROMAN:
            out.append(DEV_TO_ROMAN[ch])
        elif ch == "-":
            out.append("-")
        else:
            out.append("??")
        i += 1
    return "".join(out)


def generate_failure_solutions(possible_solutions):
    if not possible_solutions:
        return [], [], []

    # Keep the 3 shortest solutions, as before.
    shortest = sorted(
        possible_solutions,
        key=lambda w: (len(w), w)
    )[:3]

    # Balanced regen: prioritize regen value, but only consider
    # solutions that are 10 characters or fewer.
    balanced_candidates = [
        w for w in possible_solutions
        if len(w) <= 8 
    ]

    scored_balanced = [
        (w, regen_score(w))
        for w in balanced_candidates
    ]

    balanced_regen = sorted(
        scored_balanced,
        key=lambda x: (-x[1], len(x[0]), x[0])
    )[:3]

    balanced_regen_words = [w for w, _ in balanced_regen]

    # Keep the existing top regen picks unchanged.
    scored = [
        (w, regen_score(w))
        for w in possible_solutions
    ]

    top_regen = sorted(
        scored,
        key=lambda x: (-x[1], len(x[0]), x[0])
    )[:3]

    top_regen_words = [w for w, _ in top_regen]

    return top_regen_words, shortest, balanced_regen_words


def scan_solve_stacker_mismatches(syllables, wps_map, dic_list):
    mismatches = []

    for syl in syllables:
        assigned = wps_map.get(syl)
        if assigned is None or assigned > 12:
            continue

        required = min(assigned, 12)
        sols = get_help(syl, dic_list)
        unique_solves = sorted(set(normalize_token(w) for w in sols))
        actual = len(unique_solves)

        if actual < required:
            diff = assigned - actual
            mismatches.append((syl, assigned, actual, diff, unique_solves))

    if mismatches:
        print("\n⚠️ SOLVE STACKER COUNT MISMATCHES:")
        for syl, assigned, actual, diff, solves in mismatches:
            if diff > 0:
                status = f"needs {diff} more"
            else:
                status = f"has {-diff} extra"

            print(f"  • {syl}: assigned={assigned}, actual={actual} -> {status}")
            print(f"    solves: {', '.join(solves)}")
    else:
        print("\n✅ All ≤8-WPS syllables match their solution counts.")

    return mismatches

STACKER_POOL_SIZE = 30


def get_all_stacker_prompts(syllables, wps_map):
    return [
        s for s in syllables
        if isinstance(wps_map.get(s), int) and wps_map.get(s) > 0
    ]


def is_stacker_complete(s_data, assigned):
    stack = s_data.get("stacker", {})

    if stack.get("fully_mastered", False):
        return True

    if (
        stack.get("full_clears", 0) >= 2 and
        stack.get("best_found", 0) >= assigned
    ):
        return True

    return False


def stacker_priority(stats, s, wps_map, turn_count):
    s_data = stats["syllables"].setdefault(s, new_syllable_stats())
    stack = s_data["stacker"]

    assigned = wps_map.get(s)
    if assigned is None or assigned < 1:
        return -10**9  # impossible / skip

    best_found = stack.get("best_found", 0)
    last_found = stack.get("last_found_count", 0)
    full_clears = stack.get("full_clears", 0)
    last_stacked_turn = stack.get("last_stacked_turn", -1)
    fully_mastered = stack.get("fully_mastered", False)

    age = turn_count - last_stacked_turn if last_stacked_turn >= 0 else 999
    missing = max(0, assigned - best_found)

    weight = 1
    weight += missing * 50

    if full_clears == 0:
        weight += 40

    if last_found < assigned:
        weight += 20

    weight += min(age, 40)
    weight += assigned * 3

    if fully_mastered:
        weight = max(1, weight // 4)

    return weight


def get_active_stacker_prompts(stats, syllables, wps_map, turn_count, pool_size=STACKER_POOL_SIZE):
    """
    Return only the top-priority incomplete stacker prompts, capped at pool_size.
    This enforces a real rolling pool even if many prompts are already unlocked in stats.
    """
    valid = set(get_all_stacker_prompts(syllables, wps_map))
    candidates = []

    for s in stats["syllables"]:
        if s not in valid:
            continue

        assigned = wps_map.get(s)
        if assigned is None or assigned < 1:
            continue

        s_data = stats["syllables"].get(s, {})
        if is_stacker_complete(s_data, assigned):
            continue

        priority = stacker_priority(stats, s, wps_map, turn_count)
        candidates.append((s, priority))

    candidates.sort(key=lambda x: (-x[1], x[0]))
    return [s for s, _ in candidates[:pool_size]]


def seed_stacker_pool(stats, syllables, wps_map, turn_count, pool_size=STACKER_POOL_SIZE):
    all_stacker = get_all_stacker_prompts(syllables, wps_map)
    valid = set(all_stacker)

    current_incomplete = [
        s for s, data in stats["syllables"].items()
        if s in valid
        and isinstance(wps_map.get(s), int)
        and wps_map.get(s) > 0
        and not is_stacker_complete(data, wps_map[s])
    ]

    need = max(0, pool_size - len(current_incomplete))
    if need == 0:
        return 0

    unlocked = set(stats["syllables"].keys())
    inactive = [s for s in all_stacker if s not in unlocked]

    if not inactive:
        return 0

    to_add = random.sample(inactive, k=min(need, len(inactive)))

    for s in to_add:
        stats["syllables"][s] = new_syllable_stats()

    return len(to_add)


def handle_stacker_unlock(stats, syllables, wps_map, turn_count, pool_size=STACKER_POOL_SIZE):
    added = seed_stacker_pool(stats, syllables, wps_map, turn_count, pool_size)
    if added > 0:
        print(f"      🆕 New stacker prompt unlocked! (+{added})")
        return True
    return False

def get_mastered_prompts(stats, all_syllables):
    valid = set(all_syllables)
    return [
        s for s, data in stats["syllables"].items()
        if s in valid and data.get("mastery") == "mastered"
    ]


def play_regen_zen_turn(target, dic_set, possible_solutions):
    print(f"\n🧘 REGEN ZEN: [{target}]")

    txt = input("   ➤ ").strip().lower()
    if not txt:
        return None

    log_turn(target, txt)

    if normalize_token(target) not in txt:
        print("      ⚠️ Missing syllable.")
        return txt

    if txt not in dic_set:
        print("      ⚠️ Unknown word.")
        return txt

    return txt

def generate_alpha_slice(word):
    if len(word) < 4:
        return None  # too short to safely slice

    # choose slice length (weighted)
    r = random.random()
    if r < 0.4:
        L = 2
    elif r < 0.8:
        L = 3
    else:
        L = 4

    if len(word) <= L + 1:
        return None  # no valid slice avoiding first letter

    # start index must NOT be 0
    start = random.randint(1, len(word) - L)
    return word[start:start + L]

def get_alpha_solutions(slice_str, alpha_pool):
    return [w for w in alpha_pool if slice_str in w]

def filter_solutions_by_start(solutions, letter):
    if not letter:
        return solutions
    return [w for w in solutions if w.startswith(letter.lower())]

def build_wpp_map(dic_list, min_len=1, max_len=4):
    from collections import defaultdict

    wpp = defaultdict(int)

    for word in dic_list:
        w = word.lower()

        for L in range(min_len, max_len + 1):
            if len(w) < L:
                continue

            for i in range(len(w) - L + 1):
                slice_str = w[i:i + L]
                wpp[slice_str] += 1

    return dict(wpp)

def shuffle_stats_order(stats):
    items = list(stats["syllables"].items())
    random.shuffle(items)
    stats["syllables"] = dict(items)
    

def clear_all_prompts(stats, syllables):
    for s in syllables:
        stats["syllables"][s] = new_syllable_stats()

    stats["global"]["best_historical_streak"] = 0
    stats["syllables"].clear()

    print("🧹 All prompt mastery has been cleared.")

def play_alpha_slice_turn(alpha_letter, dic_set, alpha_pool, wpp_map):
    # generate valid slice
    while True:
        base_word = random.choice(alpha_pool)
        slice_str = generate_alpha_slice(base_word)
        if not slice_str:
            continue

        solutions = get_alpha_solutions(slice_str, alpha_pool)
        if solutions:
            break

    print(f"\n🔤 ALPHA: [{slice_str.upper()}] (start with '{alpha_letter.upper()}')")
    print("   Enter ONE word or type 'giveup'.")

    while True:
        txt = input("   ➤ ").strip().lower()

        if not txt:
            continue

        if txt.startswith("print"):
            parts = txt.split()

            slice_length = 1
            min_wpp = None
            max_wpp = None
            mode = "include"  # default

            try:
                base = parts[0]

                if base != "print":
                    slice_length = int(base.replace("print", ""))

                if len(parts) >= 2:
                    min_wpp = int(parts[1])

                if len(parts) >= 3:
                    max_wpp = int(parts[2])

                if len(parts) >= 4:
                    mode = parts[3].lower()
                    if mode not in ["include", "clean", "exclude"]:
                        print("      ⚠️ Mode must be: include, clean, or exclude.")
                        continue

            except ValueError:
                print("      ⚠️ Invalid print command.")
                continue

            print(f"\n🧠 Generating {slice_length}-letter slices...")
            print(f"🔎 WPP Filter: {min_wpp} → {max_wpp}")
            print(f"🔤 Mode: {mode}")

            slices = generate_all_alpha_slices(
                alpha_pool,
                slice_length,
                wpp_map=wpp_map,
                min_wpp=min_wpp,
                max_wpp=max_wpp,
                mode=mode
            )

            print(f"\n📊 Total slices: {len(slices)}\n")

            for s in slices:
                print(f"{s} ({wpp_map.get(s,0)})")

            print("\n--- END ---\n")
            sys.exit()

def generate_all_alpha_slices(
    alpha_pool,
    slice_length,
    wpp_map=None,
    min_wpp=None,
    max_wpp=None,
    mode="include"  # NEW
):
    seen = set()

    for word in alpha_pool:
        w = word.strip().lower()

        if len(w) < slice_length:
            continue

        for i in range(len(w) - slice_length + 1):
            s = w[i:i + slice_length]

            # --- NEW: character filtering ---
            if mode == "clean" or mode == "exclude":
                if not is_clean_slice(s):
                    continue
            # include = do nothing

            # --- WPP filtering ---
            if wpp_map:
                count = wpp_map.get(s, 0)

                if min_wpp is not None and count < min_wpp:
                    continue
                if max_wpp is not None and count > max_wpp:
                    continue

            seen.add(s)

    return sorted(seen)

def is_clean_slice(s):
    return s.isalpha()


def get_regen_rankings(solutions, top_n=3):
    scored = [(w.upper(), regen_score(w)) for w in solutions]
    scored.sort(key=lambda x: (-x[1], len(x[0]), x[0]))

    top_regen = scored[:top_n]
    shortest = sorted(solutions, key=len)[:top_n]

    return top_regen, [w.upper() for w in shortest]


def select_stacker_prompt(stats, candidates, wps_map, turn_count):
    weighted = []

    for s in candidates:
        s_data = stats["syllables"].setdefault(s, new_syllable_stats())
        stack = s_data["stacker"]

        assigned = wps_map.get(s)
        if assigned is None or assigned < 1:
            continue

        best_found = stack.get("best_found", 0)
        last_found = stack.get("last_found_count", 0)
        full_clears = stack.get("full_clears", 0)
        last_stacked_turn = stack.get("last_stacked_turn", -1)
        fully_mastered = stack.get("fully_mastered", False)

        age = turn_count - last_stacked_turn if last_stacked_turn >= 0 else 999
        missing = max(0, assigned - best_found)

        weight = 1
        weight += missing * 50

        if full_clears == 0:
            weight += 40

        if last_found < assigned:
            weight += 20

        weight += min(age, 40)
        weight += assigned * 3

        if fully_mastered:
            weight = max(1, weight // 4)

        weighted.append((s, weight))

    if not weighted:
        return random.choice(candidates), False

    prompts = [s for s, _ in weighted]
    weights = [w for _, w in weighted]
    return random.choices(prompts, weights=weights, k=1)[0], False


def main():
    t0 = time.perf_counter()
    syllables, wps_map, dic_set, dic_list = load_resources()
    print("load_resources:", time.perf_counter() - t0)

    t1 = time.perf_counter()
    stats = load_stats()
    print("load_stats:", time.perf_counter() - t1)

    valid = set(syllables)
    stats["syllables"] = {s: d for s, d in stats["syllables"].items() if s in valid}
    
    wpp_map = build_wpp_map(dic_list)
    print(f"🧠 WPP map built: {len(wpp_map)} slices")
    
    #print("\n🔎 VALIDATING SYLLABLE DATA...")
    #pre_scan_syllables(syllables, dic_list)
    #print("-" * 50)

    streak = 0
    total_syllables = len(syllables)
    turn_count = stats.get("turn_count", 0)
    cooldown_turns = 6
    recent_prompts = deque(maxlen=cooldown_turns)
    letter_filter = None  # ← add this near other variables

    ACTIVE_POOL_SIZE = 25
    print(turn_count)

    print("\n=== NEURO-TRAINER V8 (ADJUSTED) ===")
    print("1. Smart Mode (Improved Algorithm)")
    print("2. Mastered Mode (Random Mastered Only)")
    print("3. Regen Zen (Optimization, No Timer)")
    print("4. Solve Stacker (SN)")
    print("5. Alpha (Alphabet Training)")
    print("6. Graduation Test")
    print("7. Fluency Mode")
    print("8. Transliterator Audit (with nasal/visarga controls)")

    mode = input("Choose Mode (1-8) [Enter=1]: ").strip()
    if mode == '8':
        print("\n=== TRANSLITERATOR REACHABILITY AUDIT ===")
        sample = input("Sample file (default=hinditestdata.txt): ").strip() or "hinditestdata.txt"
        transliterator_audit(sample, dic_set)
        return

    if mode not in ('1', '2', '3', '4', '5', '6', '7'):
        mode = '1'

    mode_name = {
        '1': "SMART",
        '2': "MASTERED",
        '3': "REGEN",
        '4': "STACKER",
        '5': "ALPHA",
        '6': "GRADUATION"
    }[mode]
    
    if mode == '7':
        fluency_file = input(
            "Bookmark file (default=fluency.txt): "
        ).strip()

        if not fluency_file:
            fluency_file = "fluency.txt"
    
    admin_command = input("Admin command (Enter to skip): ").strip().lower()

    if admin_command == "masterall":
        set_all_prompts_mastered(stats, syllables, wps_map)
        shuffle_stats_order(stats)
        save_stats(stats, total_syllables, turn_count)

        print("🌟 ALL PROMPTS HAVE BEEN MASTERED.")
        print(f"📘 Total prompts updated: {len(syllables)}")

        sys.exit()
    elif admin_command == "clearall":
        clear_all_prompts(stats, syllables)

        save_stats(stats, total_syllables, turn_count)

        print(f"📘 Total prompts reset: {len(syllables)}")
        sys.exit()

    print(f"\n🚀 STARTING {mode_name} MODE! (Ctrl+C to exit)\n")
    if mode == '1':
        current = sum(
            1 for v in stats["syllables"].values()
            if v.get("hits", 0) < 4
        )

        print(f"DEBUG: active={current}, target={ACTIVE_POOL_SIZE}")

        if current < ACTIVE_POOL_SIZE:
            added = ew_prompts(
                stats,
                syllables,
                batch_size=ACTIVE_POOL_SIZE - current
            )
            print(f"DEBUG: added={added}")

            if added > 0:
                print(f"🆕 Initialized with {added} prompts\n")

        active = get_active_prompts(stats, syllables)
        print(f"📦 ACTIVE TRAINING POOL ({len(active)} prompts):")
        print("   " + ", ".join(active))
        print("-" * 50)
        letter_filter = input("Filter solves by starting letter? (Enter = none): ").strip().lower()

        if letter_filter and (len(letter_filter) != 1 or not letter_filter.isalpha()):
                print("⚠️ Invalid letter — disabling filter.")
                letter_filter = None
        
    if mode == '4':
        added = seed_stacker_pool(stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE)
        active_stacker = get_active_stacker_prompts(stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE)
        print(f"🧩 ACTIVE STACKER POOL ({len(active_stacker)} prompts):")
        print("   " + ", ".join(active_stacker[:40]))
        if len(active_stacker) > 40:
            print("   ...")
        print("-" * 50)

    if mode == '5':
        while True:
            alpha_letter = input("Choose a letter (a-z): ").strip().lower()
            if len(alpha_letter) == 1 and alpha_letter.isalpha():
                break
            print("⚠️ Please enter a single letter (a-z).")

        # ✅ compute ONCE (not in loop)
        alpha_pool = [w for w in dic_list if w.startswith(alpha_letter)]

        if not alpha_pool:
            print(f"❌ No words found starting with '{alpha_letter}'. Exiting.")
            sys.exit()

        print(f"\n🔤 ALPHA MODE — '{alpha_letter.upper()}'")
        print(f"📦 Pool size: {len(alpha_pool)} words")
        print("-" * 50)
    
    if mode == '6':
        graduation_pool = syllables[:]
        random.shuffle(graduation_pool)

        grad_correct = 0
        grad_incorrect = 0
        grad_missed = []

        print("\n🎓 GRADUATION TEST")
        print(f"📚 Total prompts: {len(graduation_pool)}")
        print("Each prompt appears exactly once.")
        print("-" * 50)
    
    if mode == '7':

        fluency_pool = load_fluency_pool(fluency_file)
        session_failures = defaultdict(int)
        
        fluency_state = {}

        for s in fluency_pool:
            fluency_state[s] = {
                "weight": 1,
                "last_seen": -999
            }
        fluency_turn = 0
        
        
        print("\n🔎 VALIDATING FLUENCY DATA...")
        pre_scan_syllables(fluency_pool, dic_list)

        for s in fluency_pool:
            stats["syllables"].setdefault(
                s,
                new_syllable_stats()
            )

        print("\n⚡ FLUENCY MODE")
        print(f"Pool size: {len(fluency_pool)}")
        print("Goal: 3 fast hits")
        print("Timer: 3.5s")
        print("-" * 50)
        if not fluency_file:
            fluency_file = "fluency.txt"

    t = 5

    if mode == '7':
        t = 3.5

    try:
        while True:
            if mode == '2':
                def picker():
                    mastered = get_mastered_prompts(stats, syllables)

                    if not mastered:
                        print("⚠️ No mastered syllables yet.")
                        raise KeyboardInterrupt

                    return random.choice(mastered), True

            elif mode == '3':
                def picker():
                    mastered = get_mastered_prompts(stats, syllables)
                    if not mastered:
                        print("⚠️ No mastered syllables yet.")
                        raise KeyboardInterrupt
                    return random.choice(mastered), True

            elif mode == '4':
                def picker():
                    candidates = get_active_stacker_prompts(
                        stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE
                    )

                    if not candidates:
                        seed_stacker_pool(stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE)
                        candidates = get_active_stacker_prompts(
                            stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE
                        )

                    if not candidates:
                        print("⚠️ No active stacker prompts available.")
                        raise KeyboardInterrupt

                    return select_stacker_prompt(stats, candidates, wps_map, turn_count)
            elif mode == '5':
                turn_count += 1

                success, slice_str, solutions = play_alpha_slice_turn(
                    alpha_letter, dic_set, alpha_pool, wpp_map
                )

                stats["global"]["total_plays"] += 1

                if success:
                    streak += 1
                    stats["global"]["total_hits"] += 1
                    print(f"      ✅ Correct! | Streak: {streak}")

                else:
                    streak = 0
                    stats["global"]["total_misses"] += 1
                    print("      ❌ Gave up.")

                    shortest = sorted(solutions, key=len)[:5]
                    print(f"      📘 Solutions: {', '.join(w.upper() for w in shortest)}")

                save_stats(stats, total_syllables, turn_count)
                print("-" * 50)
                continue
            if mode == '6':
                
                timer_input = input(
                    "\nGraduation timer (seconds, Enter = no timer): "
                ).strip()

                if timer_input == "":
                    grad_timer = None
                else:
                    try:
                        grad_timer = float(timer_input)
                    except ValueError:
                        print("Invalid timer. Using untimed mode.")
                        grad_timer = None

                for idx, target in enumerate(graduation_pool, start=1):

                    print(f"\n[{idx}/{len(graduation_pool)}]")
                    turn_count += 1

                    solutions = get_help(target, dic_list)

                    success = play_graduation_turn(
                        target,
                        dic_set,
                        solutions,
                        grad_timer
                    )

                    if success:
                        grad_correct += 1
                        print("      ✅ Correct")

                    else:
                        grad_incorrect += 1
                        grad_missed.append((target, solutions[:5]))
                        with open("graduation_misses.txt", "a", encoding="utf-8") as f:
                            f.write(target + "\n")

                        print("      ❌ Incorrect")

                        if solutions:
                            print(
                                "      📘 Solutions: "
                                + ", ".join(w.upper() for w in solutions[:5])
                            )

                accuracy = (
                    grad_correct / len(graduation_pool) * 100
                    if graduation_pool else 0
                )

                print("\n" + "=" * 60)
                print("🎓 GRADUATION REPORT")
                print("=" * 60)

                print(f"Total Prompts : {len(graduation_pool)}")
                print(f"Correct       : {grad_correct}")
                print(f"Incorrect     : {grad_incorrect}")
                print(f"Accuracy      : {accuracy:.1f}%")

                if accuracy == 100:
                    print("\n🏆 PERFECT SCORE!")
                elif accuracy >= 95:
                    print("\n🌟 EXCELLENT")
                elif accuracy >= 90:
                    print("\n✅ PASS")
                else:
                    print("\n📚 MORE REVIEW RECOMMENDED")

                if grad_missed:
                    print("\n❌ MISSED PROMPTS")
                    print("-" * 50)

                    for syllable, sols in grad_missed:
                        print(
                            f"{syllable}: "
                            + ", ".join(w.upper() for w in sols)
                        )

                save_stats(stats, total_syllables, turn_count)
                sys.exit()            
            elif mode == '7':
            

                def picker():
                    
                    nonlocal fluency_turn
                    fluency_turn += 1

                    unfinished = [
                        s for s in fluency_pool
                        if not stats["syllables"][s]
                            .get("fluency_mastered", False)
                    ]

                    if not unfinished:
                        
                        easy = []
                        medium = []
                        hard = []
                    
                        for s in fluency_pool:
                            misses = session_failures[s]

                            if misses == 0:
                                easy.append(s)
                            elif misses == 1:
                                medium.append(s)
                            else:
                                hard.append(s)
                        easy.sort()
                        medium.sort()
                        hard.sort(
                            key=lambda s: session_failures[s],
                            reverse=True
                        )
                        total = len(easy) + len(medium) + len(hard)

                        easy_pct = (len(easy) / total) * 100
                        medium_pct = (len(medium) / total) * 100
                        hard_pct = (len(hard) / total) * 100                        
                        print("\n═══════════════════════════════")
                        print("        FLUENCY REPORT")
                        print("═══════════════════════════════")
                        print(f"🟢 Easy   : {len(easy):3d} ({easy_pct:5.1f}%)")
                        print(f"🟡 Medium : {len(medium):3d} ({medium_pct:5.1f}%)")
                        print(f"🔴 Hard   : {len(hard):3d} ({hard_pct:5.1f}%)")
                        print("═══════════════════════════════")   
                        print(f"\n🟢 Easy ({len(easy)})")
                        print(", ".join(easy) if easy else "None")

                        print(f"\n🟡 Medium ({len(medium)})")
                        print(", ".join(medium) if medium else "None")

                        print(f"\n🔴 Hard ({len(hard)})")
                        for s in hard:
                            print(f"  {s} ({session_failures[s]} misses)")
                        save_stats(stats, total_syllables, turn_count)
                        sys.exit()

                    eligible = [
                        s for s in unfinished
                        if fluency_turn - fluency_state[s]["last_seen"] >= 6
                    ]

                    if not eligible:
                        eligible = unfinished

                    weights = [
                        fluency_state[s]["weight"]
                        for s in eligible
                    ]

                    chosen = random.choices(
                        eligible,
                        weights=weights,
                        k=1
                    )[0]

                    fluency_state[chosen]["last_seen"] = fluency_turn

                    return chosen, False
            else:
                def picker():
                    unlocked = [s for s in stats["syllables"] if s in valid]

                    if not unlocked:
                        ew_prompts(stats, syllables, batch_size=min(ACTIVE_POOL_SIZE, len(syllables)))
                        unlocked = [s for s in stats["syllables"] if s in valid]

                        if not unlocked:
                            return random.choice(syllables), False

                    return select_strategic_syllable(stats, unlocked)

            target, is_review = select_with_cooldown(picker, recent_prompts)

            if mode == '3':
                all_sols = get_help(target, dic_list)
                guess = play_regen_zen_turn(target, dic_set, all_sols)

                top_regen, shortest = get_regen_rankings(all_sols)
                print("\n      🔥 Regen picks:", ", ".join(w for w, _ in top_regen))

                best_score = top_regen[0][1] if top_regen else 0
                guess_score = regen_score(guess) if guess else 0

                if guess_score == best_score:
                    print("      🏆 PERFECT REGEN — TOP-TIER SOLUTION!")
                else:
                    print(f"      🧠 Your score: {guess_score} (Best: {best_score})")

                print("-" * 50)
                continue

            if mode == '4':
                
                active = [s for s,v in stats["syllables"].items() if v.get("hits",0) < 4]
                print("ACTIVE SIZE:", len(active))
                turn_count += 1
                result = play_solve_stacker_turn(target, dic_set, dic_list, wps_map)

                if result is None:
                    print("-" * 50)
                    continue

                s_data = stats["syllables"].setdefault(target, new_syllable_stats())
                s_data["last_seen"] = turn_count
                s_data["short_answers"] = result["valid_solves"][:6]
                s_data["views"] = s_data.get("views", 0) + 1
                stats["global"]["total_plays"] += 1

                update_stacker_stats(s_data, result, turn_count)

                if result["mistakes"] > 0:
                    stats["global"]["total_misses"] += result["mistakes"]
                    s_data["misses"] = s_data.get("misses", 0) + result["mistakes"]

                if result["success"]:
                    streak += 1
                    if streak > stats["global"]["best_historical_streak"]:
                        stats["global"]["best_historical_streak"] = streak
                        print("      🏆 RECORD STREAK!")

                    stats["global"]["total_hits"] += 1
                    s_data["hits"] = s_data.get("hits", 0) + 1

                    if s_data["mastery"] == "learning" and s_data["hits"] >= 4:
                        s_data["mastery"] = "mastered"
                        print("      🌟 MASTERY ACHIEVED!")
                        handle_mastery_unlock(stats, syllables)
                    
                    assigned = wps_map.get(target)
                    if assigned is not None and is_stacker_complete(s_data, assigned):
                        handle_stacker_unlock(stats, syllables, wps_map, turn_count, STACKER_POOL_SIZE)

                    stack = s_data["stacker"]
                    print(
                        f"      ✅ Found {len(result['found'])}/{result['total']} solves "
                        f"(required: {result['required']}) "
                        f"| Best: {stack['best_found']} "
                        f"| Full clears: {stack['full_clears']} "
                        f"| Streak: {streak}"
                    )

                    if result["missing"]:
                        print(f"      📘 Unused solves: {', '.join(w.upper() for w in result['missing'])}")
                        pause_for_space()

                    if stack.get("fully_mastered"):
                        print("      🧠 STACK MASTERED!")

                else:
                    streak = 0
                    print(f"      📉 Found {len(result['found'])}/{result['required']} required before stopping.")
                    if result["missing"]:
                        print(f"      🧩 Missing: {', '.join(w.upper() for w in result['missing'])}")
                    pause_for_space()

                recent_prompts.append(target)
                save_stats(stats, total_syllables, turn_count)
                print("-" * 50)
                continue

            turn_count += 1
            label = "SMART"

            if target not in stats["syllables"]:
                stats["syllables"][target] = new_syllable_stats()
            s_data = stats["syllables"][target]

            all_sols = get_help(target, dic_list)
            s_data["short_answers"] = sorted(all_sols, key=len)[:6]
            s_data["views"] = s_data.get("views", 0) + 1
            stats["global"]["total_plays"] += 1

            success, duration, used_hint = play_turn(target, dic_set, t, all_sols, label, stats, wps_map)

            if success:
                if mode == '7':

                    s_data["fluency_hits"] = (
                        s_data.get("fluency_hits", 0) + 1
                    )

                    required_hits = 2 if session_failures[target] == 0 else 3

                    if s_data["fluency_hits"] >= required_hits:

                        if not s_data.get("fluency_mastered", False):

                            s_data["fluency_mastered"] = True

                            completed = sum(
                                1 for s in fluency_pool
                                if stats["syllables"][s]
                                    .get("fluency_mastered", False)
                            )

                            print(
                                f"      ⚡ FLUENCY ACHIEVED! "
                                f"[{completed}/{len(fluency_pool)}]"
                            )
                streak += 1
                if streak > stats["global"]["best_historical_streak"]:
                    stats["global"]["best_historical_streak"] = streak
                    print("      🏆 RECORD STREAK!")

                stats["global"]["total_hits"] += 1
                stats["global"]["total_accumulated_time"] += duration

                prev_hits = s_data.get("hits", 0)
                s_data["hits"] = prev_hits + 1
                
                mastered = sum(
                    1 for d in stats["syllables"].values()
                    if d.get("hits", 0) >= 4
                )
                remaining = total_syllables - mastered

                if s_data["mastery"] == "learning" and s_data["hits"] >= 4:
                    s_data["mastery"] = "mastered"

                    pending = sum(
                        1 for s, d in stats["syllables"].items()
                        if d.get("hits", 0) < 4
                    )

                    print(f"      🌟 MASTERY ACHIEVED! ({remaining} remaining)")
                    handle_mastery_unlock(stats, syllables)

                if duration < s_data.get("best_time", 99):
                    s_data["best_time"] = round(duration, 2)

                extra = " (With Hint)" if used_hint else ""
                print(f"      ✅ Correct!{extra} ({duration:.1f}s) | Streak: {streak}")

            else:
                if mode == '7':
                    s_data["fluency_hits"] = 0
                    session_failures[target] += 1
                    fluency_state[target]["weight"] += 4
                streak = 0
                stats["global"]["total_misses"] += 1
                s_data["misses"] = s_data.get("misses", 0) + 1

                if s_data["mastery"] == "mastered":
                    s_data["mastery"] = "learning"
                    print("      🔄 Mastery lost — returning to training pool.")

                print("      ❌ Failed.")

                filtered = filter_solutions_by_start(all_sols, letter_filter)


                top_regen, shortest, balanced_regen = generate_failure_solutions(
                    filtered if filtered else all_sols
                )
            
                # Study-friendly compact list: Devanagari first, approximate Roman below.
                sections = [
                    ("🔥 REGEN PICKS", top_regen),
                    ("⚖️ BALANCED REGEN", balanced_regen),
                    ("📏 SHORTEST", shortest),
                ]
                shown = set()
                print("      📚 SOLUTIONS — Hindi | approximate spelling")
                for heading, words in sections:
                    words = [w for w in words if w not in shown]
                    if not words:
                        continue
                    print(f"      {heading}")
                    for word in words:
                        shown.add(word)
                        print(f"        {word}   |   {approximate_roman(word)}")


                pause_for_space()

            recent_prompts.append(target)
            save_stats(stats, total_syllables, turn_count)
            print("-" * 50)

    except KeyboardInterrupt:
        print("\n\n💾 Saving and exiting...")
        save_stats(stats, total_syllables, turn_count)
        print("📄 Progress updated.")
        sys.exit()


if __name__ == "__main__":
    main()