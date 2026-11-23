# MOE tooling

`MOEStage.lean` provides the commands used by the Mismatch Origin Audit:

```lean
import MOEStage

#moe_decl SomeDeclaration
#moe_root SomeDeclaration
#moe_elab (some notation expression)
#moe_pair leftExpression ; rightExpression
```

Compile it once in the probe directory and add that directory to `LEAN_PATH`
when compiling a scratch probe. Redirect the compiler output to a snapshot
file. `#moe_root` compares the stored declaration type with the type inferred
from its stored value. `#moe_pair` elaborates both terms, prints S0/S1/S2,
and replays the pair at S5. Use `#moe_decl` for every named constant observed
on the READY4 M0/M1 path.

`moe_compare.py` compares snapshots by structural expression path. The full
field contract is in `MOE-CONTRACT.md`.
