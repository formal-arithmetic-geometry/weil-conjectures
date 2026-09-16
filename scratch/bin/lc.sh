#!/bin/bash
cd /data/orchestra/repos/formal-arithmetic-geometry/weil-conjectures-slot-0
timeout 1200 lake env lean -Dbackward.isDefEq.respectTransparency=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true "$@"
