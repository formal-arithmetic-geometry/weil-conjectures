# RealPurity M1 propagation (READY4.1 attempt)

The fresh O attempt used `probes/mprwe/Original.lean`, Lean 4.35.0,
current import revision `15b8acba63e`, and the READY4.1 binary from
dataset commit `5ae674db0c7`, with a 3600-second timeout. Both the
counters and trace invocations stopped at import loading:

```text
error: object file .../WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenLowerShriekInterchange.olean ... does not exist
```

The source module exists, but its `.olean` is absent from the read-only
current-case import closure. The probe never reached the expensive root.
Consequently there are no fresh O counters, analyzed aggregate calls,
raw-capture calls, M1 share, A2 depth/fan-out metrics, or A3 transition
matrix. No number from an earlier MPRWE round is substituted here.
The kernel patch was not changed, and the read-only dependency tree was
not rebuilt. Whether the EtaleHom projection strategy remains dominant
when this case's M2 is large cannot be tested in this round.
