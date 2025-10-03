# Session Recovery and Crash Prevention Protocol

**Created**: 2025-10-03
**Purpose**: Prevent session crashes and enable rapid recovery

---

## 🚨 WHAT HAPPENED: Session Crash Analysis

### Root Cause (2025-10-03 Crash)
Between 04:55 (last successful update to `sorry_elimination_lessons_learned.md`) and session restart, the Lean build broke:

**Failures:**
- `PhysicalLogicFramework.QuantumEmergence.BellInequality` - Missing identifiers
- `PhysicalLogicFramework.QuantumEmergence.OrthomodularCore` - Syntax errors

**Working modules preserved:**
- ✅ Foundations (ThreeFundamentalLaws, InformationSpace)
- ✅ LogicField (Operator, ConstraintAccumulation)

**Likely cause:** File edits to quantum modules introduced errors without testing build before session end.

---

## 🛡️ PREVENTION PROTOCOLS

### Protocol 1: Pre-Session Commit
**RULE**: Start every session with clean git status

```bash
# At session start
git status
# If changes exist, commit or stash
git add -A
git commit -m "Session start checkpoint: $(date)"
```

**Why:** Provides recovery point if session crashes mid-work.

---

### Protocol 2: Build Verification Checkpoints
**RULE**: Verify build after every significant change

```bash
# After editing ANY Lean file
cd lean && lake build

# If errors, revert immediately
git checkout -- path/to/file.lean
```

**Frequency:**
- ⚠️ **MANDATORY**: After editing any .lean file
- ⚠️ **MANDATORY**: Before switching files
- ⚠️ **MANDATORY**: Every 15 minutes during active work

**Why:** Prevents cascading failures from accumulating.

---

### Protocol 3: Session State Logging
**RULE**: Create session log file tracking progress

```bash
# At session start
echo "=== Session $(date) ===" >> .claude/session_log.txt
echo "Working on: [TASK]" >> .claude/session_log.txt

# During session (every major milestone)
echo "✓ Completed: [MILESTONE]" >> .claude/session_log.txt
echo "Current file: [FILE]" >> .claude/session_log.txt

# Before session end
echo "=== Session end $(date) ===" >> .claude/session_log.txt
echo "Build status: [PASSING/FAILING]" >> .claude/session_log.txt
```

**Why:** Enables rapid context recovery in next session.

---

### Protocol 4: Incremental Commit Strategy
**RULE**: Commit working code frequently, not just at session end

```bash
# After each successfully building change
git add [modified_files]
git commit -m "Working: [brief description] - build passing"

# Every 30 minutes, even with sorry placeholders
git add -A
git commit -m "WIP: [current task] - checkpoint"
```

**Why:** Git history becomes session recovery log.

---

### Protocol 5: Build Status File
**RULE**: Maintain build status indicator

```bash
# After successful build
echo "PASSING - $(date)" > .claude/last_build_status.txt
echo "$(cd lean && lake build 2>&1 | tail -5)" >> .claude/last_build_status.txt

# Check at session start
cat .claude/last_build_status.txt
```

**Why:** Immediate visibility into last known good state.

---

## 🔄 RECOVERY PROTOCOLS

### Recovery Step 1: Assess Damage
```bash
# Check what changed since last commit
git status
git diff

# Identify last known good commit
git log --oneline -5
```

### Recovery Step 2: Check Build Status
```bash
cd lean && lake build 2>&1 | tee /tmp/build_errors.txt

# Count errors
grep "error:" /tmp/build_errors.txt | wc -l

# Identify failing modules
grep "error:" /tmp/build_errors.txt | grep "Building" | cut -d' ' -f4
```

### Recovery Step 3: Selective Revert
```bash
# If specific file caused break
git checkout HEAD -- path/to/broken_file.lean

# If multiple files broken
git checkout HEAD -- lean/LFT_Proofs/PhysicalLogicFramework/QuantumEmergence/

# Verify fix
cd lean && lake build
```

### Recovery Step 4: Resume from Checkpoint
```bash
# Review session log
cat .claude/session_log.txt | tail -20

# Review last consultation
ls -t multi_LLM/consultation_log_*.json | head -1 | xargs cat | jq '.prompt' -r

# Review lessons learned
cat .claude/sorry_elimination_lessons_learned.md | tail -50
```

---

## 📋 SESSION START CHECKLIST

**Every session MUST begin with:**

- [ ] Check git status: `git status`
- [ ] Check build status: `cd lean && lake build`
- [ ] Review session log: `cat .claude/session_log.txt | tail -20`
- [ ] Review last commit: `git log -1 --stat`
- [ ] Create session entry: `echo "=== Session $(date) ===" >> .claude/session_log.txt`
- [ ] Note working task: `echo "Task: [DESCRIPTION]" >> .claude/session_log.txt`

---

## 📋 SESSION END CHECKLIST

**Every session MUST end with:**

- [ ] Verify build: `cd lean && lake build`
- [ ] Commit changes: `git add -A && git commit -m "Session end: [summary]"`
- [ ] Update build status: `echo "PASSING/FAILING - $(date)" > .claude/last_build_status.txt`
- [ ] Log session end: `echo "=== End $(date) ===" >> .claude/session_log.txt`
- [ ] Update sorry_elimination_lessons_learned.md if applicable

---

## 🎯 CRITICAL RULES

### NEVER do these without committing first:
1. ❌ Edit multiple .lean files without intermediate commits
2. ❌ Refactor without verifying build
3. ❌ End session with failing build
4. ❌ Skip build verification after file changes

### ALWAYS do these:
1. ✅ Commit after each successful build
2. ✅ Log session progress continuously
3. ✅ Revert immediately if build breaks
4. ✅ Check build before ending session

---

## 🔧 TOOLS

### Quick Build Check
```bash
# Add to .bashrc or create alias
alias lft-build='cd lean && lake build 2>&1 | tail -20'
alias lft-status='git status && echo "--- Build ---" && lft-build'
```

### Session State Helper
```bash
# Create .claude/session_state.sh
#!/bin/bash
echo "Git: $(git status --short | wc -l) files changed"
echo "Build: $(cd lean && lake build 2>&1 | grep -c error) errors"
echo "Last commit: $(git log -1 --oneline)"
echo "Session log: $(cat .claude/session_log.txt 2>/dev/null | tail -3)"
```

---

## 📊 SUCCESS METRICS

Track these per session:
- Number of crashes: Target = 0
- Average recovery time: Target < 5 minutes
- Build failures caught before commit: Target = 100%
- Uncommitted work at session end: Target = 0 files

---

**Last Updated**: 2025-10-03
**Next Review**: After next 5 sessions to validate effectiveness
