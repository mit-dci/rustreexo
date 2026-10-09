#!/usr/bin/env bash

# SPDX-License-Identifier: MIT OR Apache-2.0

# Check if all commits in this branch contain PGP or SSH signatures.
# This is a presence check, not a trust/validity check.

set -euo pipefail

BASE=${1:-origin/main}
RANGE="$BASE..HEAD"

TOTAL=$(git log --pretty='tformat:%H' "$RANGE" | wc -l | tr -d ' ')

UNSIGNED=$(
    for COMMIT in $(git log --pretty='tformat:%H' "$RANGE"); do
        # Avoid %G? on SSH signatures; it requires gpg.ssh.allowedSignersFile.
        # Only inspect commit headers, not the commit message.
        if git cat-file commit "$COMMIT" | awk '
            BEGIN { in_headers = 1; in_ssh_sig = 0; found = 0 }

            /^$/ {
                in_headers = 0
            }

            in_headers && /^gpgsig(-sha256)? -----BEGIN SSH SIGNATURE-----$/ {
                in_ssh_sig = 1
            }

            in_headers && in_ssh_sig && /^ -----END SSH SIGNATURE-----$/ {
                found = 1
            }

            END {
                exit found ? 0 : 1
            }
        '; then
            continue
        fi

        git log -1 --pretty='tformat:%H %G?' "$COMMIT"
    done | awk '$2 == "N" {count++} END {print count+0}'
)

if [ "$UNSIGNED" -gt 0 ]; then
    echo "⚠️ Unsigned commits in this branch [$UNSIGNED/$TOTAL]"
    exit 1
else
    echo "🔏 All commits in this branch contain a signature [$TOTAL/$TOTAL]"
fi
