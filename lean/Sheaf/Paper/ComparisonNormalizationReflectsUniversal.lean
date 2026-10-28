/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.DerivedLocalIsomorphismSheaf

/-! # Reflection of universal scalar arrows through etale comparison

Source: Stacks Project, Tags 06YS, 0G7E, 0D6D and 09B1.
(blueprint: lem-weil-pbc-comparison-normalization-reflects-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Comparison reflects universality of a coefficient arrow between bounded complexes.

Source: `sites-cohomology.tex`, K-flat resolutions (06YS), their pullback (0G7E),
and composition of derived pullbacks (0D6D); `proetale.tex`, comparison (09B1).
(blueprint: lem-weil-pbc-comparison-normalization-reflects-universal).

Proof: realize fixed-ring sheaves as modules over the constant ring sheaf. Derived
extension of coefficients is left adjoint to the exact restriction functor in this
presentation. Resolve the source by a K-flat complex with flat terms. Comparison
inverse image preserves such complexes. Its scalar-extension comparison is the
canonical isomorphism between the two sheafified balanced tensor products; the
unit in both orders sends x to 1 tensor x. Therefore the adjunct of the displayed
compared arrow is the comparison image of the original scalar adjunct, after this
isomorphism. The assumed initiality says the compared adjunct is invertible.
Comparison inverse image is exact and conservative on sheaves: its sheaf unit is
invertible. Hence it reflects acyclic cones, so it reflects isomorphisms in the
derived category. The original adjunct is consequently invertible. Transporting
the initial adjunction unit along that isomorphism proves the stated initiality.
This argument uses K-flat resolutions without a Tor bound, also for zero rings and
on the empty scheme; the boundedness assumptions on the given objects are harmless.
-/
theorem comparisonNormalization_reflects_universal (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (q : R →+* S)
    {C : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {C' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (_hC : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C))
    (_hC' : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C'))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology q).obj C')
    (h : Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory.map δ ≫
          (localIsomorphismComparisonCoefficients q).hom.app C') :
        StructuredArrow _ (normalizationRestrict (ProEt.topology Z) q)))) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk δ : StructuredArrow _
        (normalizationRestrict Z.smallEtaleTopology q))) := by
  sorry

end AlgebraicGeometry.Scheme
