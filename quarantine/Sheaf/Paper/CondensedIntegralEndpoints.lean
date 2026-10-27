/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.TransportIntegralCounitData

/-! # Normalized integral encodings and operation comparisons

Source: purity-transport Step 2, integral-models and direct-image-tower.
(blueprint: lem-pur-condensed-integral-endpoints). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- The normalized integral encoding identifies the actual compact-support and
Tate-twisted pullback functors on their constructible finite-Tor subcategories.
Source: latest blueprint, purity-transport Step 2; integral-models (1)--(3) and
integral-direct-image-tower (2)--(3).
(blueprint: lem-pur-condensed-integral-endpoints).

Proof: use the normalized completed coefficient-ring isomorphism m.reductionX.coefficient
and its Y counterpart in the ordinary module equivalence and the exact internal/section
encoding. The integral-model criterion identifies constructibility and derived
completeness under this equivalence in both directions; its finite-Tor assertion
identifies the precise full subcategories. Restrict the equivalences to these full
subcategories. Their inclusion comparisons are the restrictions of internalization.
The actual compact-support comparison is the proper/open derived-limit comparison:
the proper factor preserves the counit and the open factor preserves extension by zero.
For the source, ordinary pullback commutes with the coefficient encoding, the specified
Tate line is carried by the same normalized encoding, and exactness carries its shift.
These comparisons identify the encoded functors with the literal condensed functors.
Thus preservation by the integral functors, recorded in m.realization.support_closed
and m.realization.source_complete, gives the two condensed membership certificates.
Restrict the natural comparisons to obtain the last two isomorphisms. This is independent
of a choice of adjunction on the twisted pullback. The empty scheme has the zero
subcategory, and dimension zero uses the unit line and the zero shift. -/
theorem condensed_integral_endpoints (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d) :
    ∃ (eX : FieldExtensionTowers.Integral P E X ≌ Condensed P E X)
      (eY : FieldExtensionTowers.Integral P E Y ≌ Condensed P E Y),
      Nonempty (eX.functor ⋙ condensedInclusion P E X ≅
        (sfIntegralConstructible P.coefficients.l E.val X).ι ⋙
          (RationalizedSmoothAdjunction.internalization P.coefficients.l E.val X
            ((D.coordinates E).abelian X) m.reductionX).functor) ∧
      Nonempty (eY.functor ⋙ condensedInclusion P E Y ≅
        (sfIntegralConstructible P.coefficients.l E.val Y).ι ⋙
          (RationalizedSmoothAdjunction.internalization P.coefficients.l E.val Y
            ((D.coordinates E).abelian Y) m.reductionY).functor) ∧
      ∃ (hF : ∀ M : Condensed P E X,
          (constantModelBoundedConstructible (spIntegralCondensed P.coefficients.l E.val) Y ⊓
            fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
            ((IntegralDirectImageTower.shriek P.coefficients.l E.val
              (SpTowerGamma.factorization j p)).obj ((condensedInclusion P E X).obj M)))
        (hJ : ∀ K : Condensed P E Y,
          (constantModelBoundedConstructible (spIntegralCondensed P.coefficients.l E.val) X ⊓
            fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L)
            ((condensedSource P D j p d E m).obj ((condensedInclusion P E Y).obj K))),
        Nonempty (FieldExtensionTowers.support P D j p d m ⋙ eY.functor ≅
          eX.functor ⋙ condensedRestriction P E
            (IntegralDirectImageTower.shriek P.coefficients.l E.val
              (SpTowerGamma.factorization j p)) hF) ∧
        Nonempty (FieldExtensionTowers.puritySource P D j p d m ⋙ eX.functor ≅
          eY.functor ⋙ condensedRestriction P E (condensedSource P D j p d E m) hJ) := by sorry

end AlgebraicGeometry.ProEtale.TransportIntegralCounit
