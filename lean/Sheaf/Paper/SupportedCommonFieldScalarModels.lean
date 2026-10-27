/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.SupportedCommonFieldScalarData
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.SixFunctors.OpenScalarConjugateNormalization
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence
import Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Normalized common finite-field scalar models

Source: blueprint main-20261015, direct-image stability proof (3), common-field obligation;
scalar-six pullback proof (1)--(3)
(blueprint: lem-sfb-supported-common-field-scalar-models).

## Main statements

* `supported_common_field_scalar_models`: independent supported lisse common-field models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

universe u u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedCommonField

/-- Independent supported lisse modules admit normalized common finite-field models.
No flatness of C to B or boundedness of its scalar extensions is assumed. The displayed
isomorphisms alpha, beta, alpha_B and beta_B are the definitions `alpha` and `alphaB`
for the two separate instances of `ModelAssertions`. The field `commonField` is literally
the compositum and carries the finite-dimensional instance, not a chosen larger field.

Source: blueprint main-20261015, direct-image stability proof (3), extracted agent
obligation; scalar-six pullback proof (1)--(3).
(blueprint: lem-sfb-supported-common-field-scalar-models).

Proof plan (exact literature proof WANTED for the extracted obligation):
1. A field is Noetherian; finite type makes X Noetherian by
lem-weil-pbc-finite-type-over-noetherian. The closure factorization and exact support
functors are those of lem-sfb-coefficient-heart-locally-closed-extension. Closed and
locally closed subschemes are Noetherian, and all their opens are quasi-compact.
2. Apply lem-weil-pbc-compositum-degree-bound and expand a finite spanning family through
the finite tower: the products of the two finite spanning families span EF over Q_l.
The two inclusions carry the restricted norm topology, so induce the recorded ring maps.
3. Apply lem-sfb-locally-free-derived-scalars on the two separate supports. It identifies
our adjunction-defined singleComparison with ordinary scalar extension, which is locally
finite free of the same ranks. Transport by lem-pe-internal-section-tensor-comparison
and lem-sfb-internal-section-scalar-adjunction. Rank zero is included.
4. On S, closure(S) minus S, and X minus closure(S), the support extension restricts to
L_0, zero, zero by lem-weil-pbc-proetale-ringed-open-closed and
lem-sfb-internal-module-operations-transport. These three constructible locally closed
strata give finite constant local models, hence constantModelBoundedConstructible.
Repeat with T and M_0. The exact single complex has cohomology only in degree zero.
5. Use lem-sfb-exact-open-closed-unbounded-calculus and the exact inverse images of
lem-sfb-locally-closed-extension-coherence on full unbounded categories. The mate of the
action square is the K-flat comparison by lem-sfb-kflat-scalar-comparison-normalization.
lem-sfb-open-scalar-conjugate-normalization gives the displayed open-unit equation.
lem-sfb-closed-supported-scalar-comparison gives the SupportNormalized closed-counit
mate equation and zero open restriction. No scalar flatness or cohomological bound is used.
6. The normalized immersion coherence lemma and lem-sfb-scalar-inverse-image-tower-diagram
identify these support comparisons with their scalar towers. Flat-term K-flat models
remain so under inverse image and scalar extension by
lem-weil-pbc-ringed-pullback-preserves-kflat. Both balanced paths send t tensor (s tensor x)
to t b(s) tensor the inverse image of x. Localization gives the comparison on all objects.
7. Insert the inverse scalar associator and singleComparison to form finiteReassociation.
Apply support extension, inverse supportComparison and supportSingle: this is alpha.
Applying J followed by tower gives alphaB; step 6 identifies it with directB. Repeat
independently for the second support and finite field.
8. Naturality of the actual scalar unit gives the left side of UnitEquation as the unit
on S_C K followed by tower. Resolve K by lem-pc-kflat-resolution and use
lem-sfb-successive-derived-quotient-normalization: z tensor v maps to 1 tensor (z tensor v),
then to c(z) tensor v, the transpose defining inducedMap. The balanced scalar associator
is (v tensor z) tensor w mapped to v tensor c(z)w, identifying successive units with the
direct unit. The same computation applies to N.
9. lem-pe-internal-section-tensor-comparison preserves underlying sheaves, tensors and
K-flat models. lem-sfb-internal-section-scalar-adjunction preserves the actual units and
counits; lem-sfb-internal-module-operations-transport preserves support extension; and
lem-sfb-module-object-ringed-site-derived-comparison preserves derived internal Homs.
Localize lowerComparison on imageι and openComparison on toImage, then compose them:
this is sectionSupportComparison. Use the existing fixed-adjunction ScalarTransport data,
whose restriction comparison is identity on sections and whose extension comparison is
pinned by the mate equation. Assemble sectionAlpha from section reassociation, inverse
sectionSupportScalar and the support-single comparison. Naturality and the two canonical
support/scalar squares give its identity with the image of alpha. Applying the section
scalar functor and the transported tower gives sectionAlphaB and its identity with the
image of alphaB (hence with the image of directB). The mate equation identifies the actual
section scalar unit with the transported internal unit. Insert these identities into
SectionUnitEquation, cancel the adjacent restriction comparisons, and apply UnitEquation;
its right side is the image of inducedMap. Thus the same comparisons and equations hold
in the section-ring model, including the specified open/closed normalizations.
Empty supports and zero ranks use zero local models and require no additional hypothesis. -/
theorem supported_common_field_scalar_models
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (S T : Scheme.{u}) (a : S ⟶ X.left) [IsImmersion a]
    (haCons : Topology.IsConstructible (Set.range a))
    (b : T ⟶ X.left) [IsImmersion b]
    (hbCons : Topology.IsConstructible (Set.range b))
    (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : Modules (Profinite.continuousMapRingObj E) S)
    (hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L)
    (M : Modules (Profinite.continuousMapRingObj F) T)
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) M) :
    Exists fun [_hX : IsNoetherian X.left] ↦
      Exists fun [_hS : IsNoetherian S] ↦ Exists fun [_hT : IsNoetherian T] ↦
        IsNoetherian a.image ∧ IsNoetherian b.image ∧
        (∀ U : X.left.Opens, IsCompact (U : Set X.left)) ∧
        (∀ U : a.image.Opens, IsCompact (U : Set a.image)) ∧
        (∀ U : b.image.Opens, IsCompact (U : Set b.image)) ∧
        ModelAssertions ℓ (E := E) (A := commonField ℓ E F)
          (le_sup_left (a := E.1)) a L ∧
        ModelAssertions ℓ (E := F) (A := commonField ℓ E F)
          (le_sup_right (a := E.1)) b M := by
  sorry

end AlgebraicGeometry.ProEtale.SupportedCommonField
