#!/bin/bash
# The global build, run continuously for stage 2 (started by the launcher, 2026-10-11). Stop: kill $(cat ~/cc1/buildloop.pid)
# Green or nothing to build: build again at once (build.py itself waits for the next landing). Red: wait 2 minutes for the
# maintainer's fix or revert, then build a new snapshot.
echo $$ > ~/cc1/buildloop.pid
export PATH=$HOME/.elan/bin:$PATH SHEAF_LEAD=L-only
cd ~/weil-conjectures-sheaf
while true; do
  python3 tools/build.py >> ~/cc1/buildloop.log 2>&1; rc=$?
  echo "$(date +%F\ %T) build.py exit $rc" >> ~/cc1/buildloop.log
  [ $rc = 0 ] && [ -x ~/cc1/proof-imports-cycle.sh ] && ~/cc1/proof-imports-cycle.sh >> ~/cc1/proof-imports-cycle.log 2>&1   # stage 2 rule 7: the missing proof-dependency imports, one commit, verified by the next build
  [ $rc = 0 ] && sleep 5 || sleep 15
done
