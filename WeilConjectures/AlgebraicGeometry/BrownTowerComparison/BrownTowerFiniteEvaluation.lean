/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerRealization

/-! # Finite evaluation and exceptional coefficient mates

Source: Zheng Construction 4.1 and Lemmas 4.10, 5.16, 5.22
(blueprint: def-pur-brown-finite-evaluation).

These are comparison data, without any existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The ordinary finite exceptional adjoint furnished by the recorded existence theorem.
Source: thm-amb-etale-exceptional-adjoint
(blueprint: def-pur-brown-finite-evaluation). -/
def ordinaryFiniteRight (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  haveI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- Unit and counit of the ordinary finite exceptional adjunction just selected.
Source: thm-amb-etale-exceptional-adjoint
(blueprint: def-pur-brown-finite-evaluation). -/
def ordinaryFiniteAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      ordinaryFiniteRight A c :=
  haveI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint _

/-- Finite evaluation of the given Brown adjunction, including the actual quotient
mates. The extension comparison is normalized by its evaluation-adjunction transpose;
the quotient projection by the recorded restriction square. The mate cocycles and
transition equation are equations of natural transformations on entire derived systems.
Source: Zheng Lemmas 5.16 and 5.22; node proof Steps 1--6
(blueprint: def-pur-brown-finite-evaluation). -/
structure FiniteEvaluation (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) where
  [finite : ∀ n : ℕ, Finite (Ring O t n)]
  realizationX : ∀ n, Realization X.smallEtaleTopology O t n
  realizationY : ∀ n, Realization Y.smallEtaleTopology O t n
  lower : ∀ n, S.levelFunctor n ⋙ (realizationY n).derived ≅
    (realizationX n).derived ⋙
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring O t n)) c
  right : ∀ n, DerivedCategory (strictEtaleLevel Y O t n) ⥤
    DerivedCategory (strictEtaleLevel X O t n)
  adjunction : ∀ n, S.levelFunctor n ⊣ right n
  finiteRight : ∀ n, right n ⋙ (realizationX n).derived ≅
    (realizationY n).derived ⋙ ordinaryFiniteRight (Ring O t n) c
  finite_counit : ∀ n Q,
    (lower n).hom.app ((right n).obj Q) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (Ring O t n)) c).map ((finiteRight n).hom.app Q) ≫
      (ordinaryFiniteAdjunction (Ring O t n) c).counit.app
        ((realizationY n).derived.obj Q) =
    (realizationY n).derived.map ((adjunction n).counit.app Q)
  chi : ∀ n, S.levelFunctor n ⋙ S.PY.derivedExtension n ≅
    S.PX.derivedExtension n ⋙ S.functor
  chi_transpose : ∀ n P,
    (S.PY.derivedAdj n).homEquiv _ _ ((chi n).hom.app P) =
      (S.levelFunctor n).map
        (((S.PX.derivedBelow (Nat.le_refl n)) ≪≫ S.PX.derivedUnit n).inv.app P) ≫
      (S.evaluation n).inv.app ((S.PX.derivedExtension n).obj P)
  evaluation : ∀ n, G.right ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ right n
  counit : ∀ n Q,
    (S.levelFunctor n).map ((evaluation n).hom.app Q) ≫
      (adjunction n).counit.app ((S.PY.evaluation n).obj Q) =
    (S.evaluation n).inv.app (G.right.obj Q) ≫
      (S.PY.evaluation n).map (G.adjunction.counit.app Q)
  projection : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelFunctor n ≅
      S.levelFunctor m ⋙ (S.PY.scalar h).derived
  projection_mate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (S.PX.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
      (.mk _ _ _ _ (projection h).inv)).natTrans =
      (etaleTowerBrownRestriction S G.openRestriction h).hom
  mate : ∀ {m n : ℕ} (h : n ≤ m),
    right m ⋙ (S.PX.scalar h).derived ⟶ (S.PY.scalar h).derived ⋙ right n
  mate_def : ∀ {m n : ℕ} (h : n ≤ m),
    mate h = (mateEquiv (adjunction m) (adjunction n)
      (.mk _ _ _ _ (projection h).hom)).natTrans
  transition : ∀ {m n : ℕ} (h : n ≤ m) Q,
    (S.PX.scalar h).derived.map ((evaluation m).hom.app Q) ≫
      (mate h).app ((S.PY.evaluation m).obj Q) ≫
      (right n).map (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PY.transition h).app Q)) =
    ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
      ((S.PX.transition h).app (G.right.obj Q)) ≫ (evaluation n).hom.app Q
  mate_identity : ∀ n Q,
    (mate (Nat.le_refl n)).app Q ≫ (right n).map ((S.PY.derivedUnit n).hom.app Q) =
      (S.PX.derivedUnit n).hom.app ((right n).obj Q)
  mate_composition : ∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) Q,
    (S.PX.derivedAssoc h₁ h₂).hom.app ((right r).obj Q) ≫
      (mate (h₂.trans h₁)).app Q =
    (S.PX.scalar h₂).derived.map ((mate h₁).app Q) ≫
      (mate h₂).app ((S.PY.scalar h₁).derived.obj Q) ≫
      (right n).map ((S.PY.derivedAssoc h₁ h₂).hom.app Q)

end BrownTowerComparison
end AlgebraicGeometry
