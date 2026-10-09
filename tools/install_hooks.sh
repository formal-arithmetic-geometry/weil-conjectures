#!/bin/sh
# Installs the server-side hook of this repository (run once on the server, from the project root):
# pushes are accepted only to refs/heads/deliver/<group>/<item>; the checked-out branch is refused by git itself
# (receive.denyCurrentBranch=refuse). Groups on other machines deliver through those branches (roles/remote-lead.md).
set -e
cd "$(dirname "$0")/.."
git config receive.denyCurrentBranch refuse
git config receive.denyDeleteCurrent true
cat > .git/hooks/pre-receive <<'HOOK'
#!/bin/sh
# Accept pushes to refs/heads/deliver/<group>/<item> only.
status=0
while read old new ref; do
  case "$ref" in
    refs/heads/deliver/*/*) ;;
    *) echo "refused: push only to refs/heads/deliver/<group>/<item> (roles/remote-lead.md)"; status=1 ;;
  esac
done
exit $status
HOOK
chmod +x .git/hooks/pre-receive
echo "hooks installed: pushes accepted to refs/heads/deliver/<group>/<item> only"
