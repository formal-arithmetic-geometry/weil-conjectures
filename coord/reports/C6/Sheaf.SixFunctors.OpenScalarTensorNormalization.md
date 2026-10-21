## What changed

Replaced the single original hole in
`AlgebraicGeometry.ProEtale.OpenScalarTensor.open_scalar_tensor_normalization`
by a complete formal proof from three strictly smaller source comparisons.

The proof establishes the open adjunct of inverse beta directly from the
published common-right-adjoint definition. `scalarOpenTranspose` expands
composite units, applies the scalar Hom bijection, and uses the unit equation
for the mate. `transported_open_unit` handles both scalar-presentation transports
by naturality, giving `beta_inverse_aux` without a new assumption.

The private `tensor_square` proves the entire final mixed square, for arbitrary
unbounded complexes, by comparing inverse routes under the open Hom bijection.
It substitutes the beta and projection adjuncts, moves the open unit through
lambda and the inverse scalar tensorator by naturality, uses precisely one
inverse lambda tensor compatibility equation, cancels lambda at Q, and then
inverts the equality of isomorphisms. No tensor-square-shaped hole is introduced.

The private `coefficient_comp` and `coefficient_id` similarly compare inverse beta
routes under the open Hom bijection. They substitute beta adjuncts, use the
coefficient law for inverse lambda, and cancel the scalar associator or unitor
by naturality at the open unit. Thus both beta coefficient laws are proved in
Lean, and the remaining coefficient hole is purely a scalar-pullback coherence
statement with no open extension functor.

The normalized projection is now constructed explicitly, rather than included
in a new existence theorem. `projectionInverse` is the natural open transpose of
the unit/tensorator map. The existing
`WeilConjectures.PurCompactSupport.openProjectionInverse_isIso`, instantiated
with constant-ring coefficients and `tensorModel m`, proves each component
invertible. The definitions of its open adjunction and tensorator match here
definitionally. `normalizedProjection` assembles the isomorphism; its adjunct
equation is `Equiv.apply_symm_apply`.

Three independent source facts remain separately stated: the local canonical
tensor models and their scalar compatibility; the restriction-of-scalars
interpretation of an already supplied normalized projection; and the
scalar-pullback coefficient cocycle/identity before taking open adjuncts.

Existing data declarations move verbatim to the publicly re-exported
`OpenScalarTensorData`, allowing the new comparison modules to import them
without a cycle. The original theorem signature is unchanged. See
`coord/changes/C6-open-scalar-tensor-data.md`.

## Proved and sorry left

Original holes closed: 1, by declaration name:
`AlgebraicGeometry.ProEtale.OpenScalarTensor.open_scalar_tensor_normalization`.
This is a decomposition, not a fully discharged proof: three lower holes are
added, so the packet's net hole change is minus two closed holes.

The main module has zero remaining `sorry`. Every remaining delivery hole is:

- `AlgebraicGeometry.ProEtale.OpenScalarTensor.open_scalar_tensor_models`
  in `Sheaf.SixFunctors.OpenScalarTensorModels`, node
  `lem-sp-canonical-open-scalar-tensor-models`.
- `AlgebraicGeometry.ProEtale.OpenScalarTensor.open_scalar_projection_compatibility`
  in `Sheaf.SixFunctors.OpenScalarProjectionCompatibility`, node
  `lem-sp-open-projection-scalar-comparison`.
- `AlgebraicGeometry.ProEtale.OpenScalarTensor.scalar_pullback_coefficient_coherence`
  in `Sheaf.SixFunctors.OpenScalarCoefficientCoherence`, node
  `lem-sp-open-scalar-coefficient-coherence`.

All three are named public theorems with their entire proof `by sorry`, source,
complete proof description, and separate DAG nodes. No definition contains a
hole. No arbitrary data is defined by choosing a witness of these theorems.
The canonical presentation witnesses are used only in the proof of the original
existential theorem. The beta adjunct formula, beta coefficient cocycle/identity and tensor-square
calculation are proved, and no new hypothesis is added to the original theorem.

## No longer needed

Removed from the original module the proof-only imports
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`,
`Sheaf.Paper.KFlatScalarComparisonNormalization`, and
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
The original public imports are preserved through the data module's public
re-export. The main proof imports the three source-comparison modules and the existing
`Sheaf.Paper.IntegralCompactSupportCoefficientData` for its intrinsic projection
invertibility theorem, in addition to the data module.

No complete mathematical node or module is claimed pruned: the source
comparisons still need the old generic facts. In particular the source-library
projection declaration is preserved, and no old theorem body is replaced by a
hole. No module is withdrawn; no `deleted.txt` is needed. The unit's realized
statement/step route is unchanged. No top-level tool-use approvals are removed.

## Where the brief, the DAG or earlier work was wrong

The prescribed declarations exist, but their signatures do not directly supply
all of the required intrinsic comparisons. `RingedDerivedComparisons.Site` uses
the same object and morphism universe, whereas this item uses site objects in
u+1 and morphisms in u. `KFlatScalarComparisonNormalization` similarly states its
geometric scalar comparison at equal site universes. The published
`derivedOpenImmersionLowerShriekProjectionIso` uses fixed-coefficient sheaves,
while this item uses sheaves of modules over the constant ring sheaf and fixes
its map by the intrinsic open adjunction. None of these statements is disputed;
the remaining source-comparison results explicitly record the bridges.
The broader search later found the intrinsic
`PurCompactSupport.openProjectionInverse_isIso`, formerly owned by the broad
`def-pur-integral-compact-support-coefficient-data`; this is now used directly,
so the new projection lemma asks only for the restriction identity. This is a
generic open projection tool, used without any integral, completed, constructible
or finite-Tor hypothesis.

Searches were run with LeanSearch, leanfinder, loogle and grep via msearch, and with local
rg in both Lean roots and Mathlib. Leanfinder returned ordinary Zariski module
and ordinary scalar-tensor results. Loogle's final query was unavailable due to
load, recorded as unavailable rather than no match. Adjunction.Unique and
Adjunction.Mates give the formal calculation used in the main proof.
`DerivedExactSquareComposition` supplies a possible exact-localization step
for the remaining coefficient cocycle, but does not itself state this beta law.
The blueprint ancestor and whole-blueprint scalar, projection-formula and
extension-by-zero searches were checked. Related blueprint results concern
module objects, bounded constructible categories or the already cited generic
projection theorem; no existing declaration gives all three precise intrinsic
bridge statements.

Using the existing projection theorem exposed a spurious DAG cycle through its
broad data owner and the Frobenius conventions. The six actual general
open-adjunction definitions and the existing theorem are therefore given narrow
`existing: true` attachments; the broad owner retains all its other declarations. No source-module code changes. See
`coord/changes/C6-intrinsic-open-projection-attachment.md` for the cycle, exact
ownership delta and all existing consumers. This does not add a theorem or hole.

New statements were checked at empty opens, identity immersions, the zero ring,
identity coefficient maps and nonflat maps such as Z/4 to Z/2. Projection has
arbitrary Q; the tensor comparison contains no projection-square conclusion;
the coefficient lemma does not mention extension by zero or beta and does not
assume a tensor choice. The formal main proof needs exactly these pieces. No extra properness, quasi-compactness, finite-Tor,
boundedness or coefficient-flatness hypothesis is introduced.

## New nodes

`def-sp-open-coefficient-adjunction-data` and
`lem-sp-intrinsic-open-projection-invertible` attach the already existing general
open data and projection-invertibility theorem in
`IntegralCompactSupportCoefficientData`. These are ownership repairs, with no
new Lean declarations or holes. The broad integral data node relinquishes only those seven declaration attachments;
its statement and statement dependencies remain verbatim.


`def-sp-open-scalar-tensor-data` owns only the verbatim relocated definitions and
structures. Its new module has no hole and preserves their public signatures.

`lem-sp-canonical-open-scalar-tensor-models` is the local ringed-topos tensor
comparison: canonical choices, invertibility of tensoring with the restricted
coefficient unit, and the inverse lambda tensor equation. It has no j-shriek
projection-square claim.

`lem-sp-open-projection-scalar-comparison` records the scalar-restriction
interpretation of any supplied projection with the specified inverse adjunct,
and invertibility of the restriction/open mate. Projection existence is proved
in the original module from the already stated intrinsic theorem.

`lem-sp-open-scalar-coefficient-coherence` records only the coefficient
tower and identity laws for scalar pullback (inverse lambda), obtained by pasting
scalar adjunction mates of exact restriction squares. The coefficient laws for
beta are proved formally in the original module.

Validation: all four prerequisites compiled in import order; the final main
module then compiled cleanly in 7.2 seconds. The three new theorem statements and the
data module compile separately. A textual check confirms the relocated data
bodies are unchanged, ignoring only comments and whitespace. All new dependency
references resolve and the modified nodes have no dependency cycle.

Change records: `coord/changes/C6-open-scalar-tensor-data.md` and
`coord/changes/C6-intrinsic-open-projection-attachment.md`.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
