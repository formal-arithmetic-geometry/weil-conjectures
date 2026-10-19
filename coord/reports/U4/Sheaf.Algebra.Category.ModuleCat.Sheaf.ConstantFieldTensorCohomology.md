## What changed

Proved `SheafOfModules.exists_constantFieldTensorCohomology` with its exact original
signature, naturality in complexes and tensor factors, and the local cycle-class formula.
Its isomorphism is the inverse of Mathlib's canonical short-complex homology comparison.
The local formula follows from the cycle comparison, quotient compatibility, and the
module-sheafification unit, with a proved private `tensorMap_tmul` lemma.

Added two fully proved modules: ConstantFieldLocalSections (local surjectivity of the
constant-field unit, including arbitrary universe levels), and ConstantFieldFlat
(flatness by lifting finitely many coefficients to the field on a covering sieve).
Generalized private helpers in the unclaimed FlatEquationalCriterionOfUniverses module
and exposed its proved implication to flatness at an independent module universe.
The existing public equivalence is unchanged. Change record:
`coord/changes/constant-field-independent-universe-flatness.md`.

All four sandbox modules compile in import order with lcompile.py, without warnings.
The unchanged consumers FlatAlgebraicInverseImageOfUniverses (12.6 s) and
InverseImageModuleFlat (5.2 s) also compile against the generalized helper.
Their temporary verbatim sandbox copies were removed after these checks.
The empty covering sieve, an empty relation, N = 0, disconnected objects and unbounded
complexes cause no special assumptions: the proof uses covering sieves and three-term
homology throughout. Local surjectivity does not assert global equality of sections
with the coefficient field.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.exists_constantFieldTensorCohomology`
(node `lem-exc-constant-field-sheaf-tensor-cohomology`).

Also proved, without adding holes:
- `SheafOfModules.constantFieldUnit_locallySurjective`
  (`lem-exc-constant-field-local-sections`).
- `SheafOfModules.isFlat_constantFieldModule`
  (`lem-exc-constant-field-module-flat`).
- `SheafOfModules.isFlatOnSite_of_local_equationalCriterion`
  (`lem-exc-site-local-relations-imply-flat`).

Actual remaining textual holes in the delivery: zero. Holes added: zero. No split-offs
with sorry. Existing imported API results retain their own independent obligations;
this delivery does not claim to close those transitive holes.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` (available through the flatness lemma).
- `Mathlib.LinearAlgebra.Basis.VectorSpace` (used in ConstantFieldFlat instead).
- `Mathlib.Algebra.Module.Projective` (field flatness instances are available there).
- `Mathlib.RingTheory.Flat.Basic` (the field relation proof uses the EquationalCriterion API).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (added to the current
  source since the retained attempt; termwise tensor and homology use SiteTensorFunctoriality
  directly, so the total-complex monoidal interface is unnecessary here).
- The retained draft's unused `Mathlib.CategoryTheory.Sites.PreservesSheafification` import
  from ConstantFieldFlat.

The parent no longer uses `lem-pc-sites-modules-sheafification-flat` or its module,
`lem-pc-sites-module-sheafification-interface` as a separate flatness step,
or `lem-weil-pbc-flat-tensor-exact`. The generic sheafification-flatness route assumes
coincident universes and is replaced by the local relation criterion. Removed the
obsolete tool_uses approval for `lem-pc-sites-modules-sheafification-flat` from the parent
node. Its proof_deps now records only the actual flatness and homology-comparison route.
The field free/projective/flat facts remain needed inside ConstantFieldFlat; the generic
ringed-site modules, constant sheaf and site tensor APIs remain needed for statements.
No blueprint unit statement or realized step is bypassed; this item's unit record has
empty realized statement/steps arrays. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned sheafification-flatness theorem is specialized to coincident universes and
cannot directly prove the assigned independently sized statement. The alternative is to
lift a finite family of coefficients locally and use the equational flatness criterion.
The pre-existing criterion's full equivalence has a max(r,m) module universe, but its
implication to flatness does not require that restriction; generalized its private proof.

Mathlib's standard unit-local-surjectivity instances also impose universe restrictions
that the statement does not supply. Proved local surjectivity directly using the local
image subsheaf, its sectionwise subring structure and sheafification's universal property.
The forgetful functor reflects the required large limits because a limiting cone of
underlying small types makes its type of compatible sections small. This avoids changing
any of the assigned hypotheses.

The read-only `tools/downstream.py` user query was terminated with exit code 137
without output. Direct source searches found the two consumers listed in the change
record; both were compiled unchanged against the delivery. No project or launcher
tool was edited.

## New nodes

`lem-exc-constant-field-local-sections`: the unit's local surjectivity. Fully proved by the
local-image subring sheaf and universal property; needs no further proof.

`lem-exc-constant-field-module-flat`: local field-coefficient factorizations imply flatness.
Fully proved using the field's flatness and the criterion; needs no further proof.

`lem-exc-site-local-relations-imply-flat`: the criterion's implication to flatness without
a coefficient/module universe bound. Fully proved by the generalized existing private
finite-matrix argument; needs no further proof. The new node is attached to the added
theorem in FlatEquationalCriterionOfUniverses, keeping the old equivalence's node intact.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
