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

/-- The global section of a composite `v ≫ g` is the image under `g` of the global section
of `v`. -/
lemma globalSectionOfModHom_comp {Z : Scheme.{u}} {M M' : AdicSheaf l Z}
    (v : AdicSheaf.unit l Z ⟶ M) (g : M ⟶ M') :
    globalSectionOfModHom (v ≫ g) = ((Sheaf.Γ _ _).map g.hom).hom (globalSectionOfModHom v) := by
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq, Mod.comp_hom', Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply]

lemma globalSectionOfModHom_zero {Z : Scheme.{u}} {M : AdicSheaf l Z} :
    globalSectionOfModHom (0 : AdicSheaf.unit l Z ⟶ M) = 0 := by
  rw [globalSectionOfModHom_eq]
  erw [Mod.zero_hom, Functor.map_zero]
  rfl

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
  obtain ⟨e', he'def⟩ : ∃ e', e' = Te.hom (globalSectionOfModHom θ.hom) := ⟨_, rfl⟩
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
    · rw [upperStarComp_id_right]
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.assoc, Category.id_comp,
        Category.comp_id]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      simp
    · rw [upperStarComp_id_left]
      simp
  have he' : (germ A hσ ((z)^*[A].obj N.X)).hom e' = ULift.up χ • e' := by
    rw [he'def, ← ModuleCat.comp_apply, hcomp, ModuleCat.comp_apply, hθ, map_smul]
  -- `e'` corresponds to a morphism `v' : ℚ̄_ℓ ⟶ π^* z^* N`
  obtain ⟨v', hv'⟩ :=
    (bijective_globalSectionOfModHom ((π)^*ᵃ[l].obj ((z)^*ᵃ[l].obj N))).2 e'
  -- the germ along `σ` fixes the sections of `π^* ℚ̄_ℓ`, so it has no eigenvector for `χ`
  have hfix (v : (Sheaf.Γ _ A).obj ((π)^*[A].obj (adicConstantSheaf l S)))
      (hv : (germ A hσ (adicConstantSheaf l S)).hom v = ULift.up χ • v) : v = 0 := by
    obtain ⟨c, rfl⟩ := exists_eq_smul_globalSectionsToUpperStar_oneGlobalSection π v
    have hr : (germ A hσ (adicConstantSheaf l S)).hom
        (((globalSectionsToUpperStar A π).app (adicConstantSheaf l S)).hom
          (oneGlobalSection (l := l) S)) =
        ((globalSectionsToUpperStar A π).app (adicConstantSheaf l S)).hom
          (oneGlobalSection (l := l) S) := by
      rw [← ModuleCat.comp_apply, globalSectionsToUpperStar_app_comp_germ]
    rw [map_smul, hr] at hv
    have h1 : (ULift.up χ - 1) • c • ((globalSectionsToUpperStar A π).app
        (adicConstantSheaf l S)).hom (oneGlobalSection S) = 0 := by
      rw [sub_smul, one_smul, ← hv, sub_self]
    refine (smul_eq_zero.1 h1).resolve_left fun h ↦ hχ ?_
    exact congrArg ULift.down (sub_eq_zero.1 h)
  -- every morphism `z^* N ⟶ ℚ̄_ℓ` kills `v'` after pullback
  have hA (f : (z)^*ᵃ[l].obj N ⟶ AdicSheaf.unit l S) : v' ≫ (π)^*ᵃ[l].map f = 0 := by
    apply (bijective_globalSectionOfModHom _).1
    rw [globalSectionOfModHom_comp, hv', globalSectionOfModHom_zero]
    refine hfix _ ?_
    have n := congrArg (fun φ ↦ φ.hom e') (germ_naturality A hσ f.hom)
    dsimp only at n
    refine n.trans ?_
    rw [ModuleCat.comp_apply, he']
    exact map_smul _ _ _
  -- hence `v' ≫ π^* m = 0`, and `v' = 0` since `π^* m` is a monomorphism
  have hB : v' ≫ (π)^*ᵃ[l].map m = 0 := by
    rw [← Category.comp_id m, ← biproduct.total, Preadditive.comp_sum, Functor.map_sum,
      Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Category.assoc, Functor.map_comp, ← Category.assoc, hA, zero_comp]
  have hv'0 : v' = 0 := (cancel_mono ((π)^*ᵃ[l].map m)).1 (by rw [hB, zero_comp])
  -- but `e'` is the transport of the section of an isomorphism, hence nonzero
  have he'0 : e' = 0 := by rw [← hv', hv'0, globalSectionOfModHom_zero]
  let E := (adicUpperStarUnitIso l z').symm ≪≫ (z')^*ᵃ[l].mapIso θ
  have hres : ((globalSectionsToUpperStar A z').app ((w)^*[A].obj N.X)).hom
      (globalSectionOfModHom θ.hom) = globalSectionOfModHom E.hom :=
    globalSectionsToUpperStar_globalSectionOfModHom z' θ.hom
  have hinj : Function.Injective ((Sheaf.Γ _ A).map
      ((upperStarCompIso A hz).hom.app N.X ≫
        (π)^*[A].map (𝟙 ((z)^*[A].obj N.X)))).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have h0 : globalSectionOfModHom E.hom = globalSectionOfModHom 0 := by
    rw [globalSectionOfModHom_zero, ← hres]
    refine hinj ?_
    rw [map_zero, ← he'0, he'def]
    rfl
  have hφ : E.hom = 0 := (bijective_globalSectionOfModHom _).1 h0
  have hone : 𝟙 (AdicSheaf.unit l (Spec (.of L))) = 0 := by
    rw [← E.hom_inv_id, hφ, zero_comp]
  refine oneGlobalSection_ne_zero (l := l) (Spec (.of L)) ?_
  have h := globalSectionOfModHom_eq (𝟙 (AdicSheaf.unit l (Spec (.of L))))
  rw [Mod.id_hom', CategoryTheory.Functor.map_id, hone, globalSectionOfModHom_zero] at h
  exact h.symm
