# Workplan experiments: PR #1563

Case: `P1563-eq-mpr-domain`, declaration
`AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula`. Lean
4.35.0, master revision `1ef1fddac73e`, original module identity, one Lean
thread.

## Baseline

The value is a four-argument `Eq.mpr`; the expensive conversion is the
fourth argument's instantiated domain. The actual and expected types have
the same `Eq` head. Carrier and left composition compare immediately. The
right `CategoryStruct.comp` pair takes 31.026 s. Its seven argument costs
in the rerun were 0, 1, 2,198, 2,022, 2,109, 6,653, and 21,864 ms,
respectively; every pair is definitionally equal although structurally
different. The nested composition is argument 6. The probe used 254.49 s
CPU, 4:17.66 wall, and 10,241,356 KB RSS.

## G1-A/B: nested descent

Probe: [`G1A-EqCompArguments.lean`](probes/wp/G1A-EqCompArguments.lean).
It records the seven outer arguments, descends only into nested argument 6,
records that node's arguments, and replaces one nested argument at a time.
Each replacement is accepted only if the nested result type is structurally
unchanged; the same nested `CategoryStruct.comp` conversion is then timed.
The immediate body of `CategoryStruct.comp` is `Expr.proj CategoryStruct.2`.

The outer shared accessor is therefore not enough to close the comparison:
the expensive work is distributed through concrete `Functor.obj`,
`Functor.map`, and the nested composition arguments. This is a controlled
descent rather than a whole-theorem before/after comparison.

The nested pair itself takes 21,537 ms. Type-preserving one-factor controls
for nested arguments 2, 3, 4, 5, and 6 take 18,975, 20,810, 20,603, 11,325,
and 15,552 ms, respectively. Argument 5 is a substantial contributor, but
the remaining conversion stays slow after every single replacement.

## Interpretation

The measured first expensive child is the nested composition (21.537 s),
with preceding concrete object/map children also contributing 2.0--6.6 s.
Argument 5 is a confirmed contributor, not a sufficient trigger. The
accessor projection is exposed in one step, but the controls do not separate
projection reduction from work in the remaining differing major/data
arguments. The fixed helper changes the proof construction and avoids this
old `Eq.mpr` value. **Necessary versus unfavorable remains unresolved.**

**Confidence:** plausible same-head/nested-argument mechanism; a decisive
type-preserving major-premise alignment was not obtained.
