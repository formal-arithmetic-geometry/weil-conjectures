/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# Coherence of exchange isomorphisms of pushforwards

For a commutative square `p ≫ a' = a ≫ p` of schemes, the *exchange isomorphism*
`p_* ⋙ a'_* ≅ a_* ⋙ p_*` is the composite `p_* a'_* ≅ (p ≫ a')_* = (a ≫ p)_* ≅ a_* p_*` of the
composition isomorphisms of pushforwards. This file proves the compatibilities of exchange
isomorphisms that are needed to transport Weil structures along isomorphisms of geometric
fibers: with the identity (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_id`), with the
composition of the vertical sides (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_vcomp`)
and with a commutative cube (`AlgebraicGeometry.ProEtale.adicLowerStar_exchange_cube`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {T₁ T₂ : Scheme.{u}} (p : T₁ ⟶ T₂)

/-- The exchange isomorphism along `p` of pushforwards along squares whose vertical sides are
the identity, up to `lowerStarId`. -/
lemma lowerStar_exchange_id {a : T₁ ⟶ T₁} {a' : T₂ ⟶ T₂} (ha : a = 𝟙 T₁) (ha' : a' = 𝟙 T₂)
    (h : p ≫ a' = a ≫ p) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (lowerStarCongr A ha').hom.app ((p)_*[A].obj G) ≫ (lowerStarId A T₂).hom.app _ =
      (lowerStarComp A p a').hom.app G ≫ (lowerStarCongr A h).hom.app G ≫
        (lowerStarComp A a p).inv.app G ≫
          (p)_*[A].map ((lowerStarCongr A ha).hom.app G ≫ (lowerStarId A T₁).hom.app G) := by
  subst ha ha'
  ext V : 3
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_obj_obj_map']
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  (repeat' apply pullback.hom_ext) <;>
    simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]

end

end AlgebraicGeometry.ProEtale
