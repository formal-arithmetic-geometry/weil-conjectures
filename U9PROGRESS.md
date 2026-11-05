# BZ72 progress

- Unit: BZ72, branch `u9/BZ72`.
- Scope: Cospecialization, FinitarySliceEnoughPoints, ProEtale.Adic.UpperStar, BifunctorHomHomotopyExactSupplement.
- First three modules pass remote `ucheck-bump`.
- Supplement proofs ported; coordinate theorem needed canonical `quotientCompQhIso` transports because Mathlib now hides Qh. Proposed exception explicitly, then user instructed continuation; patch applied.
- Four-module check final2 reduced to one final reassociation in the coordinate proof. Replaced the failed simplifier call with Category.assoc; final3 is running.
- No local Lean/Lake execution, no sorries or trust escapes, no heartbeat increases.
- Fix log: `/home/ubuntu/u9/bz/FIXES-BZ72.md`.
- After green: record final remote log and commit, write `/home/ubuntu/u9/state/BZ72.DONE`, remove stale BLOCKED marker.
