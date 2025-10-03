#!/bin/bash
# Physical Logic Framework - Session Start Script
# Created: 2025-10-03

echo "==================================="
echo "Physical Logic Framework - Session Start"
echo "$(date)"
echo "==================================="
echo ""

# Log session start
echo "=== Session Start $(date) ===" >> .claude/session_log.txt

# Check git status
echo "📊 Git Status:"
git status --short
echo ""

# Check for uncommitted changes
UNCOMMITTED=$(git status --porcelain | wc -l)
if [ "$UNCOMMITTED" -gt 0 ]; then
    echo "⚠️  WARNING: $UNCOMMITTED uncommitted file(s)"
    echo "   Consider committing or stashing before starting work"
    echo ""
fi

# Check Lean build status
echo "🔧 Lean Build Check:"
cd lean
BUILD_OUTPUT=$(lake build 2>&1 | tail -10)
BUILD_STATUS=$?
echo "$BUILD_OUTPUT"
cd ..

if [ $BUILD_STATUS -eq 0 ]; then
    echo "✅ Build PASSING" | tee -a .claude/last_build_status.txt
    echo "$(date)" >> .claude/last_build_status.txt
else
    echo "❌ Build FAILING" | tee -a .claude/last_build_status.txt
    echo "$(date)" >> .claude/last_build_status.txt
    echo ""
    echo "⚠️  WARNING: Build has errors - fix before making changes!"
fi

echo ""
echo "==================================="
echo "Session Ready - Document your task:"
echo "  echo 'Task: [DESCRIPTION]' >> .claude/session_log.txt"
echo "==================================="
