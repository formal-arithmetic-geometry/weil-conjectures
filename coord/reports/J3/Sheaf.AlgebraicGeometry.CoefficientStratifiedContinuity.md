## What changed

Replaced the sole proof hole of
`AlgebraicGeometry.ProEtale.coefficientStratified_continuity` by a complete assembly
of the stated argument. The existing signature and docstring are unchanged.
The proof converts each finite constant model to a finitely presented model using
`Module.finitePresentation_of_finite`, obtains an etale origin for each stratum,
glues those origins, and uses the affine comparison colimit cocone. Naturality of
`continuityMap` and cancellation of the induced colimit isomorphism transport this
result to the original fixed-scalar sheaf. Three private proof imports supply
strictly separate missing interfaces for independent coefficient size.

The new modules are `CoefficientFpLocalSystemOrigin`,
`CoefficientStratifiedEssentialImage`, and `CoefficientComparisonContinuity`, all
under `Sheaf.AlgebraicGeometry`. Each states one public theorem, with its literature
source, proof in words, edge cases, and a new DAG node. The item node's proof and
proof dependencies now describe this actual Lean assembly.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.coefficientStratified_continuity`
(node `lem-pe-coefficient-stratified-continuity`) is closed by decomposition.
The assigned module has zero remaining holes. This is a decomposition, not a
sorry-free proof of its mathematics: one hole is closed and three are added
(net minus two). The new remaining holes are exactly:

- `AlgebraicGeometry.ProEtale.coefficientFpLocalSystem_essImage`, node
  `lem-pe-coefficient-fp-local-system-origin`: descent for a single finitely
  presented local system, with no stratification or Noetherian hypothesis.
- `AlgebraicGeometry.ProEtale.coefficientFixed_essImage_of_stratification`, node
  `lem-pe-coefficient-stratified-essential-image`: gluing arbitrary etale origins;
  it assumes those origins on strata and has no finite-model or continuity claim.
- `AlgebraicGeometry.ProEtale.coefficientFixedComparison_isColimit`, node
  `lem-pe-coefficient-comparison-continuity`: the projection restriction cocone for
  an already given etale sheaf is a colimit, with no stratification hypothesis.

Each new proof is exactly `:= by sorry`; no definition or private helper has a
hole. Existential origins are eliminated inside a theorem proof, and no arbitrary
witness is used to define data.

## No longer needed

No module or node is withdrawn, and no original public import is removed.
The new modules retain only the public imports their statements need: the local-system
lemma needs the affine interface for its independent-universe sheafification
instances and finite-presentation API (removing it gave stuck universe constraints); the stratified
lemma uses the fixed-pullback definitions; the colimit lemma uses the comparison
models and continuity-cocone definitions. Redundant imports of the full affine
constructibility interface and re-exported comparison models were removed. The
original planned dependencies remain relevant through the new interfaces:
`det-pe-finite-local-systems-twist` supports the local-system lemma,
`lem-weil-pbc-comparison-stratified-essential-image` supports the gluing lemma,
and the comparison-section and classical-continuity lemmas support the final
colimit lemma. They are not claimed pruned. The finite-module finite-presentation
Mathlib leaf is used directly. The source-library boundary is unchanged.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies supply the mathematical steps, but their current Lean
interfaces do not specialize to the assigned coefficient universe. In particular,
`finiteLocalSystemsTwist` uses a ring `Lambda : Type u` lifted to `Type (u+1)`,
whereas `comparison_essImage_of_stratification` and
`proEtaleClassicalSheavesModules` use modules in `Type (u+1)` for schemes in
`Scheme.{u}`. The assigned theorem permits `Type (max v (u+1))` coefficients on
AsSmall site models. The new statements isolate these universe-independent
versions without changing any existing interface or replacing the assigned
statement by a renamed copy.

The proof route follows the existing unit: finite local-system comparison,
open-closed induction and Zariski locality, then the affine section colimit.
The new statements include the empty scheme, empty strata, zero strata, and zero
module models; the gluing proof does not mistake a full-image immersion for an
isomorphism. No global quasi-compactness assumption was added.

## New nodes

`lem-pe-coefficient-fp-local-system-origin` records the single-local-system step
of the constructible-comparison proof, following Stacks 099Y. Its module is
`Sheaf.AlgebraicGeometry.CoefficientFpLocalSystemOrigin`.

`lem-pe-coefficient-stratified-essential-image` records the finite-partition
induction after origins on strata have been supplied, following the induction
in Stacks 09AK. Its module is
`Sheaf.AlgebraicGeometry.CoefficientStratifiedEssentialImage`.

`lem-pe-coefficient-comparison-continuity` records the canonical affine section
colimit for any etale inverse image, with the exact presentation and coefficient
universes required here. Its module is
`Sheaf.AlgebraicGeometry.CoefficientComparisonContinuity`.

No change record is necessary: no existing statement, definition, visibility,
or public import changed, and there are no forced consumer adaptations.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
