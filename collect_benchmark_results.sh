#!/bin/bash

# Collect benchmark results from Criterion output
# This script runs after benchmarks complete to gather results

set -e

RESULTS_DIR="${1:-benchmark-results}"
mkdir -p "$RESULTS_DIR"

echo "Collecting benchmark results..."

# Check if Criterion generated reports
if [ -d "target/criterion" ]; then
    echo "✅ Found Criterion reports"
    
    # Create a summary of all benchmark results
    find target/criterion -name "raw.csv" | while read -r file; do
        benchmark_name=$(echo "$file" | sed 's|target/criterion/||' | sed 's|/raw.csv||')
        echo "Found benchmark: $benchmark_name"
        
        # Extract key metrics from the raw data
        if [ -f "$file" ]; then
            # Get the last (most recent) measurement
            tail -n 1 "$file" > "$RESULTS_DIR/${benchmark_name}_latest.csv" 2>/dev/null || true
        fi
    done
    
    # Create a summary JSON with key metrics
    cat > "$RESULTS_DIR/summary.json" << 'EOF'
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "benchmarks_found": $(find target/criterion -name "raw.csv" | wc -l),
  "status": "completed",
  "criterion_version": "0.5",
  "environment": {
    "os": "$(uname -s)",
    "arch": "$(uname -m)",
    "cpu_count": "$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 'unknown')"
  }
}
EOF
    
    echo "✅ Benchmark results collected successfully"
    echo "Results saved to: $RESULTS_DIR"
    echo "Benchmark count: $(find target/criterion -name "raw.csv" | wc -l)"
    
else
    echo "⚠️ No Criterion reports found"
    echo "This might indicate benchmark execution issues"
    
    # Create a minimal status file
    cat > "$RESULTS_DIR/status.json" << 'EOF'
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "status": "no_reports_found",
  "error": "Criterion reports directory not found"
}
EOF
fi

echo "Benchmark result collection completed"