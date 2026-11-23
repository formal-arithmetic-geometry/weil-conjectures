# P4 same-context frozen argument-26 replay

Probe: `P4Frozen.lean`, a scratch declaration importing the two P4 helper
modules. It elaborates direct `hv` (`h0`) and whole-proposition transport
(`h`) in one local context. After both values exist, it extracts each
argument-26 actual type and the helper's expected domain after the first
25 arguments, then calls `Kernel.isDefEq` with the same Environment/local
context. The source premise is intentionally different; this is not an
Elaborator-only perturbation.

| Pair | Actual hash | Expected hash | Syntactically equal | Kernel result | READY4.2 root | Calls | Wall |
| --- | ---: | ---: | --- | --- | ---: | ---: | ---: |
| F0 direct `hv` | 1172892286 | 2832094282 | no | true | 2749 | 3,180,439 | 26,052.431 ms |
| F1 transport | 2832094282 | 2832094282 | yes | true | 2750 | 1 | 0.013 ms |

The uninstrumented run and READY4.2 counters run both compiled successfully.
The whole-consumer controls in the case report (3,180,470 versus 7,039 calls)
remain distinct from these isolated frozen-pair counts.
