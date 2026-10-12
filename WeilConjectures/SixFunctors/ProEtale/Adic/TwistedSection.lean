/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierInertia
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# A sheaf trivialised with a twisted deck action does not embed into a constant sheaf

Let `N` be an `ℓ`-adic sheaf on `Y`, and `w : Y' ⟶ Y` a morphism with an automorphism `g` over
`Y` (`g ≫ w = w`), such that `w^* N` is trivialised, `θ : ℚ̄_ℓ ≅ w^* N`, and `g` acts on the
trivialising section by a scalar `χ ≠ 1`. Let `z : S ⟶ Y` be a point which, after a base change
`π : Spec L ⟶ S` to a field, lifts along `w` to `z' : Spec L ⟶ Y'`, and suppose that `g`
restricts on `z'` to an automorphism `σ` of `Spec L` over `S`. Then `z^* N` does not embed into
a constant sheaf `ℚ̄_ℓⁿ` on `S`.

Indeed `σ` acts on the sections of `π^* z^* N` (the germs along `σ ≫ π = π`) and on those of
`π^* ℚ̄_ℓ`; a section of `π^* z^* N` coming from `θ` is multiplied by `χ`, while all sections of
`π^* ℚ̄_ℓ` are pulled back from `S` and so are fixed. Hence every morphism `z^* N ⟶ ℚ̄_ℓ`
kills that section after pullback, and a monomorphism into `ℚ̄_ℓⁿ` would kill it too.

This is the sheaf-theoretic content of "inertia acts on the fibre of `N` through the nontrivial
character `χ`", used for the Artin–Schreier sheaves at infinity (blueprint
`lem-a1-artin-schreier-ramified-infinity`).

## Main statements

- `AlgebraicGeometry.ProEtale.germ_eq_globalSectionsTransport`: germs are transports along
  squares with trivial base change.
- `AlgebraicGeometry.ProEtale.not_mono_upperStar_biproduct_unit_of_twist`: the main statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

lemma upperStarCongr_inv_app {P Y : Scheme.{u}} {a b : P ⟶ Y} (p : a = b)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A p).inv.app F = (upperStarCongr A p.symm).hom.app F := by
  subst p
  simp [upperStarCongr]

lemma upperStarCongr_hom_app_trans {P Y : Scheme.{u}} {a b c : P ⟶ Y} (p : a = b) (q : b = c)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A p).hom.app F ≫ (upperStarCongr A q).hom.app F =
      (upperStarCongr A (p.trans q)).hom.app F := by
  subst p q
  simp [upperStarCongr]

/-- The restriction of global sections along equal morphisms. -/
lemma globalSectionsToUpperStar_app_comp_upperStarCongr {P Y : Scheme.{u}} {a b : P ⟶ Y}
    (p : a = b) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (globalSectionsToUpperStar A a).app F ≫ (Sheaf.Γ _ A).map ((upperStarCongr A p).hom.app F) =
      (globalSectionsToUpperStar A b).app F := by
  subst p
  simp [upperStarCongr]

/-- A germ is the transport along the square `y ≫ w = s ≫ 𝟙` with the trivial base change. -/
lemma germ_eq_globalSectionsTransport {P W Y : Scheme.{u}} {w : W ⟶ Y} {y : P ⟶ W}
    {s : P ⟶ Y} (h : y ≫ w = s) (h' : y ≫ w = s ≫ 𝟙 Y) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    germ A h F = globalSectionsTransport A h' ((upperStarId A Y).hom.app F) := by
  rw [germ, globalSectionsTransport]
  congr 2
  rw [upperStarCompIso_hom_app, upperStarComp_id_right]
  simp only [upperStarFactor, Iso.trans_inv, NatTrans.comp_app, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.assoc, Category.id_comp]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    upperStarCongr_inv_app]
  congr 1
  rw [← Category.assoc, upperStarCongr_hom_app_trans]
  exact (Category.comp_id _).symm

/-- Restricting a global section of `F` along `s` and then taking its germ along `y ≫ s = s` gives
the restriction along `s`. -/
lemma globalSectionsToUpperStar_app_comp_germ {P Y : Scheme.{u}} {s : P ⟶ Y} {y : P ⟶ P}
    (h : y ≫ s = s) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (globalSectionsToUpperStar A s).app F ≫ germ A h F = (globalSectionsToUpperStar A s).app F := by
  rw [germ, ← Category.assoc, ← globalSectionsToUpperStar_comp, Category.assoc,
    ← Functor.map_comp]
  simp only [upperStarFactor, Iso.trans_inv, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
    upperStarCongr_inv_app]
  exact globalSectionsToUpperStar_app_comp_upperStarCongr A _ F

end Coherence

variable {l : ℕ} [Fact l.Prime]

/-- **A sheaf trivialised with a twisted deck action does not embed into a constant sheaf.**
Let `N` be an `ℓ`-adic sheaf on `Y`, `w : Y' ⟶ Y`, `g : Y' ⟶ Y'` with `g ≫ w = w`, and
`θ : ℚ̄_ℓ ≅ w^* N` a trivialisation whose section is multiplied by `χ ≠ 1` under the germ along
`g`. Let `z : S ⟶ Y`, `π : Spec L ⟶ S` for a field `L`, `z' : Spec L ⟶ Y'` with
`z' ≫ w = π ≫ z`, and `σ : Spec L ⟶ Spec L` with `σ ≫ π = π` and `σ ≫ z' = z' ≫ g`. Then there
is no monomorphism `z^* N ⟶ ℚ̄_ℓⁿ`. -/
theorem not_mono_upperStar_biproduct_unit_of_twist {S Y Y' : Scheme.{u}} {L : Type u} [Field L]
    {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    {w : Y' ⟶ Y} {g : Y' ⟶ Y'} (hg : g ≫ w = w)
    {z : S ⟶ Y} {z' : Spec (.of L) ⟶ Y'} (hz : z' ≫ w = π ≫ z) (hσz : σ ≫ z' = z' ≫ g)
    {N : AdicSheaf l Y} (θ : AdicSheaf.unit l Y' ≅ (w)^*ᵃ[l].obj N) {χ : PadicAlgCl l}
    (hχ : χ ≠ 1)
    (hθ : (germ (WeilCoefficients.{u} l) hg N.X).hom (globalSectionOfModHom θ.hom) =
      ULift.up χ • globalSectionOfModHom θ.hom)
    {n : ℕ} (m : (z)^*ᵃ[l].obj N ⟶ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l S) [Mono m] : False := by
  let A := WeilCoefficients.{u} l
  have hσ' : σ ≫ π = π ≫ 𝟙 S := by rw [hσ, Category.comp_id]
  have hg' : g ≫ w = w ≫ 𝟙 Y := by rw [hg, Category.comp_id]
  -- the transport `Γ(Y', w^* N) ⟶ Γ(Spec L, π^* z^* N)` along `z' ≫ w = π ≫ z`
  let Te := globalSectionsTransport A hz (𝟙 ((z)^*[A].obj N.X))
  let θs := globalSectionOfModHom θ.hom
  let e' := Te.hom θs
  -- the germ along `σ` of the transported section is the transport of the germ along `g`
  have hcomp : Te ≫ germ A hσ ((z)^*[A].obj N.X) = germ A hg N.X ≫ Te := by
    rw [germ_eq_globalSectionsTransport A hσ hσ', germ_eq_globalSectionsTransport A hg hg']
    have h₁ : (σ ≫ z') ≫ w = π ≫ (𝟙 S ≫ z) := by
      rw [Category.assoc, hz, ← Category.assoc, hσ, Category.id_comp]
    have h₂ : (z' ≫ g) ≫ w = π ≫ (z ≫ 𝟙 Y) := by
      rw [Category.assoc, hg, hz, Category.comp_id]
    rw [globalSectionsTransport_comp A hz hσ' h₁, globalSectionsTransport_comp A hg' hz h₂,
      globalSectionsTransport_congr A h₁ (Category.id_comp z) _ (𝟙 _) ?_,
      globalSectionsTransport_congr A h₂ (Category.comp_id z) _ (𝟙 _) ?_,
      globalSectionsTransport_congr_left A _ hσz]
    · rw [upperStarComp_id_left]
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.assoc, Category.id_comp,
        CategoryTheory.Functor.map_id, Iso.inv_hom_id_app, Category.comp_id]
    · rw [upperStarComp_id_right]
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.assoc, Category.id_comp,
        Category.comp_id]
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
  have he' : (germ A hσ ((z)^*[A].obj N.X)).hom e' = ULift.up χ • e' := by
    have := congrArg (fun f ↦ f.hom θs) hcomp
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this.trans ((congrArg Te.hom hθ).trans (map_smul _ _ _))
  sorry

end AlgebraicGeometry.ProEtale
