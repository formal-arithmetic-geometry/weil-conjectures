module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

lemma upperStarCongr_hom_app {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (F : Sheaf (ProEt.topology W) A) :
    (ProEtale.upperStarCongr A h).hom.app F = eqToHom (by rw [h]) := by
  subst h
  simp [ProEtale.upperStarCongr]

lemma w1 {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (F : Sheaf (ProEt.topology W) A) :
    (ProEtale.upperStarCongr A h).hom.app F = eqToHom (by rw [h]) := by
  simp only [ProEtale.upperStarCongr, eqToIso.hom, eqToHom_app]

lemma w2 {Z Z₁ Z₂ W : Scheme.{u}} {a : Z ⟶ Z₁} {b : Z₁ ⟶ W}
    {c : Z ⟶ Z₂} {d : Z₂ ⟶ W} (h : a ≫ b = c ≫ d) :
    (ProEtale.upperStarCompIso A h).hom =
      (ProEtale.upperStarComp A a b).inv ≫ (upperStarCongr A h).hom ≫
        (ProEtale.upperStarComp A c d).hom := rfl

variable {Z Z₁ Z₂ W : Scheme.{u}} {a : Z ⟶ Z₁} {b : Z₁ ⟶ W}
    {c : Z ⟶ Z₂} {d : Z₂ ⟶ W} (h : a ≫ b = c ≫ d) (F : Sheaf (ProEt.topology W) A)

lemma w3a : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ (upperStarCongr A h).hom.app F ≫
        (ProEtale.upperStarComp A c d).hom.app F := by rw [w2]; rfl

lemma w3b : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ (upperStarCongr A h).hom.app F ≫
        (ProEtale.upperStarComp A c d).hom.app F := by rw [w2, NatTrans.comp_app, NatTrans.comp_app]

lemma w3c : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ (upperStarCongr A h).hom.app F ≫
        (ProEtale.upperStarComp A c d).hom.app F := by
  simp only [upperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

lemma w4a : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ eqToHom (by rw [h]) ≫
        (ProEtale.upperStarComp A c d).hom.app F := by
  rw [w3b, w1]

lemma w4c : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ eqToHom (by rw [h]) ≫
        (ProEtale.upperStarComp A c d).hom.app F := by
  rw [w3b]; exact congrArg (fun x ↦ _ ≫ x ≫ _) (w1 A h F)

lemma w4d : (ProEtale.upperStarCompIso A h).hom.app F =
      (ProEtale.upperStarComp A a b).inv.app F ≫ eqToHom (by rw [h]) ≫
        (ProEtale.upperStarComp A c d).hom.app F :=
  (w3b A h F).trans (congrArg (fun x ↦ _ ≫ x ≫ _) (w1 A h F))

end AlgebraicGeometry.ProEtale
