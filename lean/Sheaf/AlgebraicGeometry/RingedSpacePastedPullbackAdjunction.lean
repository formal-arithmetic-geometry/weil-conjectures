/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Algebra.Homology.KFlat

/-! # Compatible pasted tensor-pullback adjunction

Source: Stacks Project, Cohomology, Tags 079W, 0D5S, and 0D5T.
(blueprint: lem-pc-ringed-space-pasted-pullback-adjunction).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-- Successive tensor pullbacks and their derived functors have compatible
adjunctions; the left comparison is invertible on K-flat complexes.
Source: Stacks Project, Cohomology, lemma-adjoint (079W),
lemma-derived-pullback-composition (0D5S), and
lemma-derived-pushforward-composition (0D5T).
(blueprint: lem-pc-ringed-space-pasted-pullback-adjunction).

Proof: choose the concrete tensor module pullbacks P_g and P_f, with the
underived adjunctions induced by inverse image and extension of scalars.
On homotopy categories set G = P_g ⋙ P_f. Its right adjoint is f_* ⋙ g_*.
Choose the absolute left derived tensor pullbacks L_g and L_f computed on
K-flat complexes. Set L = L_g ⋙ L_f and derive each underived adjunction
using the right-derived units already specified in the statement. Compose
the resulting adjunctions. The left comparison at T is L_f(α_g(T)), followed
by α_f(P_g T), with the functor associators. For a K-flat K, α_g(K) is invertible;
P_g K is K-flat by pullback preservation, so α_f(P_g K) is invertible as well.
Thus α(K) is invertible. To check the unit equation, write η'_g, η'_f for
the two derived adjunction units and η_g, η_f for their underived units.
The composite unit is η'_g(QT) followed by Rg_*(η'_f(L_g QT)). Expand R(α(T))
and use naturality of η'_f at α_g(T). The inner composition becomes
α_g(T) followed by η'_f(Q(P_g T)) and Rf_*(α_f(P_g T)). Apply
Adjunction.derivedη_fac_app for f to the last two factors, and for g to
η'_g(QT) followed by Rg_*(α_g(T)). The result is Q(η_g(T)), β_g(P_g T),
Rg_*(Q(η_f(P_g T))), and Rg_*(β_f(P_f P_g T)), in that order.
Naturality of β_g at η_f(P_g T) moves the middle factors to
Q(g_*(η_f(P_g T))) followed by β_g(f_*P_f P_g T).
Combining the two Q-maps gives the underived composite adjunction unit;
the remaining factors are precisely β at G(T). This constructs the compatible
adjunction, rather than choosing an arbitrary adjunction of the same functors.
No direct image is assumed to preserve K-injectivity. -/
theorem exists_pasted_tensorPullback_adjunction
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    let F := (moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)
    let R := derivedModuleDirectImage f ⋙ derivedModuleDirectImage g
    let β : F ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R :=
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
          (moduleDirectImage g).rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit
          (derivedModuleDirectImage g) ≫ (Functor.associator _ _ _).hom
    ∃ (G : HomotopyCategory (SheafOfModules.{u} (moduleRings Z)) (ComplexShape.up ℤ) ⥤
        HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ))
      (adj : G ⊣ F)
      (L : DerivedCategory (SheafOfModules.{u} (moduleRings Z)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (adj' : L ⊣ R)
      (α : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh),
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ,
        K.IsKFlat → IsIso
          (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
      ∀ K, adj'.unit.app (DerivedCategory.Qh.obj K) ≫ R.map (α.app K) =
        DerivedCategory.Qh.map (adj.unit.app K) ≫ β.app (G.obj K) := by sorry

end AlgebraicGeometry.RingedSpace
