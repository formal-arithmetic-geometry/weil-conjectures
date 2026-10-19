# Maintenance: prop-weil-pbc-levelwise-truncations

2026-10-16, stage 2, dispatcher group NC.

The recurring BLOCKED result was a prerequisite interface defect. Batch
`0c985cbd563598b0de3aecc8b49940fbb3ab6a25` rebound
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` to
`AlgebraicGeometry.Scheme.proEtaleCanonicalTensorPullback`. That theorem only
handles a scheme map between two pro-etale sites and an invertible coefficient
comparison. It cannot express the etale-to-pro-etale morphism or noninvertible
coefficient quotients needed by the final normalization clause of the NC item.
The publicly imported older generic theorem identifies site object, site Hom,
and coefficient universes, so is also unusable at the prescribed sites. Workers
correctly obeyed the latest bottom-up brief and named the unusable dependency;
the source/search tools were working. Retrying and counting failures cannot
repair this data defect.

The new side-only compatibility modules are:

- `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`:
  ordinary comparison data, with insertion `q_one`, generalized pure-tensor
  normalization, uniqueness, unit normalization and signed total comparison.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  and its selected comparison. They retain flat-term K-flat preservation and
  the unique derived representative square from the older generic interface.

For sites with objects in `Type s` and morphisms in `Type h`, coefficients and
modules live in `max s h`. Thus for a scheme in universe `u`, use `s = u+1`
and `h = u`: both `T.Etale` and `T.ProEt` retain their actual category universes,
and coefficients/modules are in `u+1`. The geometric inverse image and its
algebraic lift are arbitrary; the coefficient map is a morphism, not an
isomorphism. Flatness is the existing `IsFlatOnSite` (exactness of the actual
sheafified tensor). Both older APIs remain available through public imports.
Stage 2 states theorems with `sorry`; the new definitions contain no `sorry`.
No truncation statement or target mathematics was added.

These companion paths are intentional. `tools/nt_compile.py` resolves any
module also present in the live tree through published live artifacts, whose
K-flat interface currently uses coefficients in `max s h`. Editing a side
copy of an existing live module alone would not repair downstream compilation.
The dependency's Lean binding is promoted to the shared DAG so periodic
live-to-side synchronization does not restore the bad binding. Live Lean
source and build artifacts are untouched.

Validation used `tools/lean_file.sh`, one Lean file at a time, with its existing
60-second per-file limit. The ordinary and derived companion modules compile
without errors or warnings. The separate diagnostic
`lean/.sandbox/MAINTNC/EtaleProEtaleConsumer.lean` checks:

- the recorded theorem and ordinary data at `T.Etale` and `T.ProEt`, with
  coefficient sheaves in `Type (u+1)`;
- continued availability of the old generic and specialized pro-etale APIs;
- composition of `ProEtale.pbcComparisonReduction` with
  `Scheme.pbcFunctionReduction` at the actual quotient ring maps, yielding
  compatibility of etale inverse image followed by function-ring realization
  with `pbcDerivedExtend` along `pbcAdicQuotient`.

The latter composition uses functor associators and whiskering of the two
existing canonical isomorphisms. The first is the mate of the specified
restriction comparison; the second is the mate of the section-normalized
function-ring restriction comparison. It introduces no arbitrary comparison
choice or extra normalization hypothesis. The diagnostic is an interface test,
not a replacement for the levelwise truncation proposition.

Next worker: import
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` and read the repaired
dependency record. The ordinary data and derived theorem share namespace
`SheafOfModules.CanonicalTensorPullbackOfUniverses`. Use the existing
`pbcComparisonReduction`, `pbcDerivedFunctionRealization` and
`pbcFunctionReduction` for actual coefficient presentations; the saved consumer
shows their composite. Preserve the target's TC, cocycle, strict-transition,
retained-origin and counterexample requirements. Continue the original stage-2
statement/delivery work. The old dispatcher BLOCKED note predates this repair.

Existing changed records in the side and live DAG have sibling
`.maint-NC-levelwise-truncations-1792135673.bak` backups. New modules and this
report also have sibling `.bak` snapshots. No mathematical DAG statement,
dispatcher counter, claim or stopping rule was changed. No `lake build` was
run and no foreign process was stopped.
