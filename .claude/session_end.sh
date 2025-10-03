#!/bin/bash
# Physical Logic Framework - Session End Script
# Created: 2025-10-03

echo "==================================="
echo "Physical Logic Framework - Session End"
echo "$(date)"
echo "==================================="
echo ""

# Check Lean build before ending
echo "🔧 Final Build Verification:"
cd lean
BUILD_OUTPUT=$(lake build 2>&1)
BUILD_STATUS=$?
echo "$BUILD_OUTPUT" | tail -10
cd ..

echo ""
if [ $BUILD_STATUS -eq 0 ]; then
    echo "✅ Build PASSING - Safe to end session"
    echo "PASSING - $(date)" > .claude/last_build_status.txt
    echo "$BUILD_OUTPUT" | tail -5 >> .claude/last_build_status.txt
else
    echo "❌ Build FAILING - DO NOT END SESSION"
    echo "FAILING - $(date)" > .claude/last_build_status.txt
    echo "$BUILD_OUTPUT" | grep "error:" >> .claude/last_build_status.txt
    echo ""
    echo "⚠️  CRITICAL: Fix build errors before ending session!"
    echo "   Run: cd lean && lake build"
    echo ""
    exit 1
fi

echo ""
echo "📊 Git Status:"
git status --short
echo ""

# Check for uncommitted changes
UNCOMMITTED=$(git status --porcelain | wc -l)
if [ "$UNCOMMITTED" -gt 0 ]; then
    echo "⚠️  WARNING: $UNCOMMITTED uncommitted file(s)"
    echo ""
    read -p "Commit all changes before ending? (y/n): " -n 1 -r
    echo ""
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        echo ""
        read -p "Commit message: " COMMIT_MSG
        git add -A
        git commit -m "$COMMIT_MSG"
        echo "✅ Changes committed"
    else
        echo "⚠️  Ending session with uncommitted changes"
    fi
fi

# Log session end
echo "=== Session End $(date) ===" >> .claude/session_log.txt
echo "Build Status: $(cat .claude/last_build_status.txt | head -1)" >> .claude/session_log.txt
echo "Uncommitted files: $UNCOMMITTED" >> .claude/session_log.txt
echo ""

echo "==================================="
echo "Session Ended Successfully"
echo "==================================="
