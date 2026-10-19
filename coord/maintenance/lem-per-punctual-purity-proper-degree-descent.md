# Q31 punctual-purity dependency selection repair

Item: `lem-per-punctual-purity-proper-degree-descent`, stage 2.

The side landing `171ae863e9260cfe39e29432b5b5a680e317c6e0` extended
`lean/Sheaf/AlgebraicGeometry/EtaleFiniteTwistPullback.lean` with
`AlgebraicGeometry.Scheme.finiteEtaleTwistPullbackData`. The landed
`RegularImmersionClassCalculus` calls it at lines 69 and 80. The live source
and published artifact under `weil-conjectures-sheaf/lean` still have the
older interface, which lacks this declaration. The side source is present,
but was absent from `coord/stage2-source-overrides.json`.

`tools/nt_source_overlay.py` deliberately uses a published live artifact
when a live source exists and no explicit side override is registered.
Thus repeated normal compiles picked the older dependency, whereas an
explicitly supplied copy of the landed source compiled successfully.
Redelivering its unchanged node/module correctly failed delivery ownership
checks. This was missing source-selection metadata, not a mathematics fault
or a dependency module that needed to be delivered again.

Repair: register `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` in the
existing override manifest. Both compiler paths then select the landed
side source and compile it privately. The source snapshot/cache keys change
automatically; no cache deletion or live artifact mutation is needed.

Backup of the prior manifest:
`coord/stage2-source-overrides.json.maint-Q31-1792365349.bak`.

Validation used an unchanged copy of Q31's saved item with
`tools/lean_file.sh lean/.sandbox/maint_Q31_punctual_purity_1792365349.lean`.
Before the change it failed with both unknown-constant errors. After the
change it passed with no errors or warnings: dependency 13.9 s,
class calculus 41.0 s, trait dualizing restriction 4.8 s, item 11.5 s.
Each file used nice 19, two threads, and the existing 60-second limit.

Next worker: retain the saved packet and use the ordinary `deliver2.py`
dry run and delivery. Do not restore the diagnostic dependency copy under
`lean/` or redeliver its unchanged node. The saved copy in `scratchpad/`
is diagnostic material only. The Q41 history entry was a stage-1 split,
not a completed stage-2 declaration. The item still needs ordinary stage-2
preflight, delivery, and independent review. Its mathematics was not changed
by this repair. Do not edit launcher state to clear retry counters.
