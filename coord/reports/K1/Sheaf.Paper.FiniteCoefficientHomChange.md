## What changed

Replaced the single hole in `WeilConjectures.finiteCoefficient_derivedHom_change`
by a proof with its original signature and all nine clauses. The proof uses the
existing domain calculus, normalized generator word and site-descent theorem.
Private categorical calculations prove evaluation and uniqueness, naturality,
transpose compatibility, composition, the quotient cocycles and the ambient site
square. The intrinsic endpoint and isomorphism assertions are obtained from
etale witnesses by explicit isomorphisms and cancellation in the site square.

Added `FiniteHomEtaleIso.lean`, with the thick-generation proof, and
`LisseProjectiveConstantModels.lean`, with the finite-projective constant-model
bridge proved from the existing finite-values/stalk theorem. Added two smaller
normalization statements in their own modules. All added imports of the item are
private proof imports. No existing definition, declaration signature, public
import or adopted source module was changed.

Validation: `lcompile.py --all` compiled all five delivery modules in import order.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.finiteCoefficient_derivedHom_change` (1 of 1).
This is a decomposition, not a claim of an axiom-free proof: one named hole is
closed and two lower holes are added. Existing imported holes remain the intended
stage-3 dependencies. The delivery ledger determines changes to the full target
import closure.

Also proved `WeilConjectures.finiteHomEtale_isIso` and
`AlgebraicGeometry.lisseProjective_constantModels`.

Every added hole, and the only holes in the delivery:

- `WeilConjectures.finiteHom_ordinary_transpose`
  (`lem-coef-finite-hom-ordinary-transpose`): identifies the ordinary and
  right-tensor coordinates of the same evaluation-defined map, as equality of
  `Arrow` objects (endpoints included), on arbitrary
  ambient inputs. It asserts no invertibility or domain preservation.
- `WeilConjectures.finiteHomIntrinsic_tensorComposition`
  (`lem-coef-finite-hom-intrinsic-tensor-composition`): the tensor square for
  successive intrinsic quotients, before taking Hom transposes. It asserts no
  internal-Hom result.

The item module has zero `sorry`; each remaining obligation has its source and a
complete proof in words in its docstring and node.

## No longer needed

The formal closed-category calculations are proved privately for the actual
closed records, so `lem-coef-evaluation-transpose-coherence` and its module are
not needed by this proof. Its obsolete `tool_uses` approval is removed from the
item node. Its chosen-ihom interface does not directly identify
the normalized records used in the target. The direct declared dependency
`lem-coef-etale-lisse-hom-reduction` is superseded for this assembly by the
published `normalizedComparison`, which already packages the generator
comparison. That node may still be needed by other parents; no withdrawal or
whole-library unreachability is claimed.

The thick-locus, flat-generation and locally closed generator modules remain
needed through `FiniteHomEtaleIso`; the item no longer imports their lower
implementation tools directly. Endpoint and scalar-coherence uses are supplied by `FiniteHomDomainCalculus`; site comparison and constructible
origin uses are supplied by `CoefFiniteHomSiteDescent`. The selected diagram itself supplies tensorator normalization, so the proof no
longer calls `finiteHomDomain_monoidal`. No adopted-source declaration or module
is removed.

Removed these direct private imports from the item (their transitive need is
determined by the retained dependencies):

- `Sheaf.Paper.FiniteConstructibleHom`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`
- `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.Paper.EtaleKFlatCriteria`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.SixFunctors.EtaleHomThickLocus`
- `Sheaf.SixFunctors.FlatModelGeneration`
- `Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect`
- `Sheaf.Paper.OpenComplementUnconditional`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.Paper.EtaleLocallyClosedShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`
- `Sheaf.Paper.FiniteCoefficientDirectImage`
- `Sheaf.SixFunctors.EtaleOpenTensor`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.Topology.Defs.Filter`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.InternalAdjunctionPairingChange`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.SixFunctors.CoefMonoidalSquareHomTransport`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`

## Where the brief, the DAG or earlier work was wrong

The stated route is mathematically usable. Its interfaces require two
normalizations not directly present as usable equations: the thick-locus and
generator statements use the ordinary left-tensor transpose, while the target
uses the normalized right-tensor closed record; and the intrinsic target
cocycle is ambient, whereas the successive-quotient clause of site descent is
only on constructible pairs. These gaps are isolated by the two new statements.
The ordinary normalization was already flagged in the earlier Lean review of
the item node.

The constant-model bridge is needed because flat generation records finite
projective geometric stalks and normalizedComparison asks for finite projective
constant trivializations. It is proved using the public finite-values theorem,
refining away empty cover members. The source-library coefficient-Hom theorem
for algebras over ZMod l cannot replace this argument for general higher
uniformizer-power quotients.

The current blueprint was read at `literature/blueprint/latest/`: the finite-Hom
proof and flat-model generation clause (3). The unit's route is retained. Edge
cases checked in the new statements are the empty scheme/empty cover, zero
modules, rank zero, identity quotients, the first positive exponent and
nonflat successive quotients. None requires an inverse to a Hom comparison
before its isomorphism proof.

## New nodes

`lem-coef-finite-hom-ordinary-transpose`, in
`Sheaf.Paper.FiniteHomOrdinaryTranspose`, is the remaining coordinate
normalization step. Its hypotheses are arbitrary ambient inputs; it is strictly
smaller than the coefficient-change theorem.

`lem-coef-lisse-projective-constant-models`, in
`Sheaf.Paper.LisseProjectiveConstantModels`, is proved. It converts the stalk
hypothesis of the existing generators to the constant-model hypothesis of the
normalized comparison.

`lem-coef-finite-hom-intrinsic-tensor-composition`, in
`Sheaf.Paper.FiniteHomIntrinsicTensorComposition`, is the remaining intrinsic
scalar tensor square. Uncurrying and cancellation, proved in the item, turn
this tensor equation into the specified Hom cocycle.

`lem-coef-finite-hom-etale-iso`, in `Sheaf.Paper.FiniteHomEtaleIso`, is proved
from the existing normalized word and thick generation, using the ordinary-transpose
and constant-model lemmas. It bundles no endpoint or coherence assertions.

No change record is needed: no existing statement or definition changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
