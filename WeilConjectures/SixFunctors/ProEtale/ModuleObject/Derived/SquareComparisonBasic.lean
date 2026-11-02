/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!
# The components of the pullback comparisons of derived pullbacks

For a commutative square `g' ≫ p = p' ≫ g` of schemes, the pullback comparison
`θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` (`ProEtale.CondensedRing.pullbackSquareComparison`) of the
derived pullbacks of module objects is unfolded
(`ProEtale.CondensedRing.pullbackSquareComparison_eq`) and its components are computed
(`ProEtale.CondensedRing.pullbackSquareComparison_hom_app`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- The components of `α ≪≫ eqToIso h ≪≫ β`. -/
private lemma trans_eqToIso_trans_hom_app {C D : Type*} [Category C] [Category D]
    {F F' G H : C ⥤ D} (α : G ≅ F) (h : F = F') (β : F' ≅ H) (K : C) :
    (α ≪≫ eqToIso h ≪≫ β).hom.app K =
      α.hom.app K ≫ eqToHom (Functor.congr_obj h K) ≫ β.hom.app K := by
  subst h
  simp

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- `ProEtale.CondensedRing.pullbackSquareComparison` unfolded. -/
lemma pullbackSquareComparison_eq (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq = (leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (by rw [sq.w]) ≪≫ leftDerivedUpperStarComp Λ g' p :=
  rfl

/-- The components of the pullback comparison. -/
lemma pullbackSquareComparison_hom_app (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        eqToHom (by rw [sq.w] : L((p' ≫ g)^*⟦Λ⟧).obj K = L((g' ≫ p)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K :=
  (congrArg (fun θ ↦ θ.hom.app K) (pullbackSquareComparison_eq Λ sq)).trans
    (trans_eqToIso_trans_hom_app _ _ _ K)

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
