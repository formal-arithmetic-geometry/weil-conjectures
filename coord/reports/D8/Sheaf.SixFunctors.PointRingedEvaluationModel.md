## What changed

Reduced the hole in `Sheaf.SixFunctors.PointRingedEvaluationModel` by a direct construction
using final-object evaluation, its monoidal structure on modules and complexes, and
localization on the recorded flat-term K-flat representatives. Existing public definitions,
visibility, imports and theorem signature are preserved. Proof-only imports supply the
point, sheafification, K-flat and localization interfaces. Updated the node proof to this route.

## Proved and sorry left

Decomposition: the original hole in
`AlgebraicGeometry.ProEtale.PointEvaluation.point_ringed_evaluation_model` is closed
by combining an existing-interface chain-model statement with proved geometric-point,
coefficient-section and representative-localization arguments. One hole closed, one added;
net zero. The only remaining hole is
`AlgebraicGeometry.ProEtale.PointEvaluation.point_evaluation_chain_models`, node
`lem-sf-point-evaluation-chain-models`, in `PointEvaluationChainModels.lean`.
No sorry occurs in a definition. The new statement excludes geometric point identification,
all derived uniqueness/descent assertions, and coefficient section calculations.

## No longer needed

The direct final-object construction avoids presenting the target of the point as a
one-object ringed site and applying the general exact-pullback signed-comparison theorem.
The proof does not invoke `lem-pur-exact-pullback-signed-comparison`,
`lem-weil-pbc-site-derived-tensor-descent`, or
`lem-weil-pbc-localization-universal-property`; it uses the existing representative
whiskering and comparison descent declarations directly.

The constant-section argument works for every commutative ring, so the proof does not
need `lem-pur-proetale-finite-constant-sections` or
`lem-weil-valued-dvr-finite-quotients`. The existing profinite-tower isomorphism supplies
the completed integer-ring assertion, so no new Cauchy-sequence argument or direct use of
`lem-weil-l-adic-extension-complete` is needed. All adopted source declarations remain.

Proof-only imports are listed in the module. One new chain-model node is introduced.

Removed direct imports: `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Mathlib.Topology.Algebra.Valued.LocallyCompact`,
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, and
`Mathlib.CategoryTheory.Localization.Predicate`.
The finite-constant-sections module leaves this module's import closure. Arithmetic inputs
remain transitive dependencies of `IntegersProfiniteTower`; no arithmetic module is withdrawn.

Removed direct DAG proof dependencies:
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `def-pc-tensor-complex-sheaves`,
`lem-pur-exact-pullback-signed-comparison`, `lem-weil-pbc-site-derived-tensor-descent`,
`lem-weil-pbc-localization-universal-property`, `lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-valued-dvr-finite-quotients`, `lem-pur-proetale-finite-constant-sections`,
`def-pur-sheaf-inverse-limit`, and `lem-weil-l-adic-extension-complete`.
The normalized point construction, representative descent, and existing profinite tower
supply the needed assertions directly. Their underlying general constructions remain in
public statement dependencies where required. Removed corresponding obsolete tool approvals
for ringed-topoi-derived-tensor-pullback, exact-pullback-signed-comparison,
site-derived-tensor-descent, extension-integers-dvr, and proetale-finite-constant-sections;
all remaining approvals retain their original order.

## Where the brief, the DAG or earlier work was wrong

The planned one-object-site specialization is unnecessary for this statement. Final-object
sheafification and the standard monoidal extension to cochain complexes give the normalized
maps directly. Constant-section bijectivity here does not require finiteness of the ring.
No existing statement or definition is changed.

## New nodes

`lem-sf-point-evaluation-chain-models` isolates the normalized chain tensor and scalar
construction (original steps 3, 5, 6). Its source, generator calculation, signs and
coherence proof are recorded in its docstring and node. The geometric point, completed
coefficient calculation, and derived representative descent remain proved in the item.
The full attempted construction and performance investigations remain in the sandbox scratch
archive and are not part of the delivery.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
