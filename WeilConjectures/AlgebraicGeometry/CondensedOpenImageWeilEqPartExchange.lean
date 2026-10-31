/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs

/-! Raw derived-boundary compatibility of the canonical condensed Weil maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The raw homology boundary commutes with the canonical derived Weil maps.
Source: latest blueprint, p-dl-a1-exact, Step 1
(blueprint: new-dl-a1-weil-eq-part-exchange).
Proof: exact inverse image carries the single triangle of S to the single triangle
of its image, via the canonical single comparison. The three Weil maps define a
morphism from that image short complex to S. Apply derived direct image, and paste
with the canonical exchange triangle morphism. Its components are the maps used
in dlOpenImageDerivedWeilMap. Naturality of the homology ladder, together with the
exact inverse-image homology comparison, gives the displayed boundary equation.
No ordinary direct image or degree-zero identification is used in this step. -/
theorem condensedOpenImage_weil_boundary
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC)
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact)
    (φ₁ : (upperStar Λ gU).obj S.X₁ ≅ S.X₁)
    (φ₂ : (upperStar Λ gU).obj S.X₂ ≅ S.X₂)
    (φ₃ : (upperStar Λ gU).obj S.X₃ ≅ S.X₃)
    (hf : (upperStar Λ gU).map S.f ≫ φ₂.hom = φ₁.hom ≫ S.f)
    (hg : (upperStar Λ gU).map S.g ≫ φ₃.hom = φ₂.hom ≫ S.g) :
    (upperStar Λ gC).map
        (DerivedCategory.HomologySequence.δ
          ((lowerStar Λ j).rightDerivedFunctor.mapTriangle.obj hS.singleTriangle) 0 1 rfl) ≫
        dlOpenImageHomologyWeilMap Λ j sq S.X₁ φ₁ 1 =
      dlOpenImageHomologyWeilMap Λ j sq S.X₃ φ₃ 0 ≫
        DerivedCategory.HomologySequence.δ
          ((lowerStar Λ j).rightDerivedFunctor.mapTriangle.obj hS.singleTriangle) 0 1 rfl := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
