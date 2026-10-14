/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverLoop
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverContinuity
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Lisse sheaves attached to representations, by descent along universal covers

Let `p : Ỹ_t ⟶ Y` be the universal cover at a geometric point `t` and `ρ` a continuous
finite-dimensional `ℚ̄_ℓ`-representation of `π₁(Y, t)`. Composing the matrix of `ρ` with the loop
map `Ỹ_t ×_Y Ỹ_t ⟶ π₁(Y, t)` (`AlgebraicGeometry.Scheme.UniversalCovers.loop`) gives a cocycle
of invertible matrices of locally finite functions on `Ỹ_t ×_Y Ỹ_t`; descending the trivial
sheaf `ℚ̄_ℓⁿ` on `Ỹ_t` along it gives a lisse sheaf on `Y` whose monodromy is `ρ`.

## Main statements

- `AlgebraicGeometry.ProEtale.AdicSheaf.exists_iso_transitionMatrix_eq`: descent of trivial
  `ℓ`-adic sheaves along a single-morphism pro-étale cover, for a cocycle of matrices of
  locally finite functions (the stack property of sheaves).
- `AlgebraicGeometry.ProEtale.AdicSheaf.resOver_freeSection`: the restriction of sections of a
  trivialised sheaf along an endomorphism of the cover acts through the transition matrix.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace AdicSheaf

section FreeSections

variable {V W : Scheme.{u}} {n : ℕ}

/-- The global section of `ℚ̄_ℓ,Vⁿ` given by a column of locally finite functions. -/
noncomputable def freeSection (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    (Sheaf.Γ (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)).obj
      (⨁ fun _ : Fin n ↦ unit l V).X :=
  ∑ i, ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom).hom
    (adicConstantGlobalSection (f i))

/-- The section of `ℚ̄_ℓ,V` given by a function is additive in the function. -/
lemma adicConstantGlobalSection_add (a b : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantGlobalSection (a + b) =
      adicConstantGlobalSection a + adicConstantGlobalSection b := by
  rw [adicConstantGlobalSection, adicConstantGlobalSection, adicConstantGlobalSection,
    ← map_add]
  rfl

/-- The section of `ℚ̄_ℓ,V` given by a sum of functions. -/
lemma adicConstantGlobalSection_sum {ι : Type*} (s : Finset ι)
    (a : ι → PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantGlobalSection (∑ i ∈ s, a i) = ∑ i ∈ s, adicConstantGlobalSection (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, adicConstantGlobalSection]
    exact map_zero _
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, adicConstantGlobalSection_add, ih]

/-- An endomorphism of the unit module multiplies sections by its function. -/
lemma Γ_map_adicConstantGlobalSection (ψ : unit l V ⟶ unit l V)
    (a : PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map ψ.hom).hom (adicConstantGlobalSection a) =
      adicConstantGlobalSection (a * unitEndFun ψ) := by
  have n := congrArg (fun φ ↦ φ.hom (ULift.up a : (adicConstantSheaf l V).obj.obj
    (op (Scheme.ProEt.mk (𝟙 V))))) ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).inv.naturality ψ.hom)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n
  refine n.symm.trans ?_
  rw [adicConstantGlobalSection]
  congr 1
  exact adicConstantSheaf_app_eq_mul ψ.hom (unit_hom_linear ψ) _ _

/-- **A morphism of free modules acts on free sections through its matrix.** -/
lemma Γ_map_freeSection (T : (⨁ fun _ : Fin n ↦ unit l V) ⟶ ⨁ fun _ : Fin n ↦ unit l V)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map T.hom).hom (freeSection f) = freeSection (unitMatrix T *ᵥ f) := by
  let F := AdicSheaf.forget V ⋙ Sheaf.Γ (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)
  have hF {M N : AdicSheaf l V} (φ : M ⟶ N) : (Sheaf.Γ _ _).map φ.hom = F.map φ := rfl
  have hι (i : Fin n) : biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T =
      ∑ k, (biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T ≫
        biproduct.π (fun _ : Fin n ↦ unit l V) k) ≫ biproduct.ι (fun _ : Fin n ↦ unit l V) k := by
    conv_lhs => rw [← Category.comp_id T, ← biproduct.total, Preadditive.comp_sum,
      Preadditive.comp_sum]
    simp only [Category.assoc]
  have step (i : Fin n) : ((Sheaf.Γ _ _).map T.hom).hom (((Sheaf.Γ _ _).map
      (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom).hom (adicConstantGlobalSection (f i))) =
      ∑ k, ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) k).hom).hom
        (adicConstantGlobalSection (unitMatrix T k i * f i)) := by
    rw [hF, hF, ← ConcreteCategory.comp_apply, ← F.map_comp, hι, F.map_sum]
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [F.map_comp, ConcreteCategory.comp_apply]
    change ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) k).hom).hom
      (((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T ≫
        biproduct.π (fun _ : Fin n ↦ unit l V) k).hom).hom (adicConstantGlobalSection (f i))) = _
    rw [Γ_map_adicConstantGlobalSection, mul_comm]
    rfl
  simp only [freeSection, map_sum, step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← map_sum, Matrix.mulVec, dotProduct, adicConstantGlobalSection_sum]

/-- The pullback of the inclusion of a summand into a free module. -/
lemma adicUpperStar_map_ι_freeUpperStarIso_hom (g : W ⟶ V) (i : Fin n) :
    (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l V) i) ≫
        (freeUpperStarIso l (Fin n) g).hom =
      (adicUpperStarUnitIso l g).hom ≫ biproduct.ι (fun _ : Fin n ↦ unit l W) i := by
  have h1 : biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ (freeUpperStarIso l (Fin n) g).inv =
      (adicUpperStarUnitIso l g).inv ≫ (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l V) i) := by
    simp [freeUpperStarIso]
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← h1, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Restriction of free sections**: the restriction along `g : W ⟶ V` of the free section of a
column of functions, identified with a section of `ℚ̄_ℓ,Wⁿ`, is the free section of the
pulled back column. -/
lemma globalSectionsToUpperStar_freeSection (g : W ⟶ V)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) g).hom.hom).hom
        (((globalSectionsToUpperStar _ g).app (⨁ fun _ : Fin n ↦ unit l V).X).hom
          (freeSection f)) =
      freeSection fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom (f i) := by
  simp only [freeSection, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have key : (Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom ≫
      (globalSectionsToUpperStar _ g).app (⨁ fun _ : Fin n ↦ unit l V).X ≫
        (Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) g).hom.hom =
      (globalSectionsToUpperStar _ g).app (adicConstantSheaf l V) ≫
        (Sheaf.Γ _ _).map (adicUpperStarUnitIso l g).hom.hom ≫
          (Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l W) i).hom := by
    have n := (globalSectionsToUpperStar (WeilCoefficients.{u} l) g).naturality
      (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom
    rw [← Category.assoc, n, Functor.comp_map, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp]
    have e := congrArg Mod.Hom.hom (adicUpperStar_map_ι_freeUpperStarIso_hom (l := l) g i)
    rw [Mod.comp_hom', Mod.comp_hom', adicUpperStar_map_hom] at e
    rw [e]
    rfl
  have := congrArg (fun φ ↦ φ.hom (adicConstantGlobalSection (f i))) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  refine this.trans ?_
  congr 1
  exact globalSectionsToUpperStar_adicConstantGlobalSection g (f i)
end FreeSections

section Restriction

variable {Y W : Scheme.{u}} {G : AdicSheaf l Y} {p : W ⟶ Y} {n : ℕ}
  (ε : (p)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W)

/-- The trivialisation `p^* G ≅ (𝟙 ≫ p)^* G ≅ ℚ̄_ℓⁿ` obtained by pulling back `ε` along the
identity, whose restrictions along endomorphisms of `W` over `Y` are computed by transition
matrices. -/
noncomputable def trivId : (p)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W :=
  (adicUpperStarCongr l (Category.id_comp p)).symm.app G ≪≫ trivPull p ε (𝟙 W)

/-- The pullback along a morphism `c` of a congruence isomorphism, conjugated by the composition
isomorphisms. -/
lemma adicUpperStarComp_hom_app_comp_map_congr_comp_inv_app {Q X Z : Scheme.{u}} (c : Q ⟶ X)
    {x y : X ⟶ Z} (q : x = y) (q' : c ≫ x = c ≫ y) (M : AdicSheaf l Z) :
    (adicUpperStarComp l c x).hom.app M ≫ (c)^*ᵃ[l].map ((adicUpperStarCongr l q).hom.app M) ≫
        (adicUpperStarComp l c y).inv.app M =
      (adicUpperStarCongr l q').hom.app M := by
  rw [← adicUpperStarComp_inv_app_comp_congr_comp_hom_app c q q' M]
  simp

/-- **The restriction along an endomorphism `h` of `W` over `Y`**, in the trivialisation
`trivId ε`, is the pullback along `h` followed by the transition morphism of `h, 𝟙`. -/
lemma trivId_conj (h : W ⟶ W) (e : h ≫ p = p) :
    (freeUpperStarIso l (Fin n) h).inv ≫ (h)^*ᵃ[l].map (trivId ε).inv ≫
        (adicUpperStarComp l h p).inv.app G ≫ (adicUpperStarCongr l e).hom.app G ≫
          (trivId ε).hom =
      transitionHom ε (h ≫ 𝟙 W) (𝟙 W) (by rw [Category.comp_id, e, Category.id_comp]) := by
  have h₁ := trivPull_comp_hom ε h (𝟙 W)
  have hε₁ : (trivId ε).inv = (trivPull p ε (𝟙 W)).inv ≫
      (adicUpperStarCongr l (Category.id_comp p)).hom.app G := rfl
  have hε₂ : (trivId ε).hom = (adicUpperStarCongr l (Category.id_comp p)).inv.app G ≫
      (trivPull p ε (𝟙 W)).hom := rfl
  rw [transitionHom_eq, ← cancel_epi (trivPull p ε (h ≫ 𝟙 W)).hom, Iso.hom_inv_id_assoc, h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hε₁, Functor.map_comp]
  simp only [Category.assoc]
  rw [Iso.map_hom_inv_id_assoc, reassoc_of% (adicUpperStarComp_hom_app_comp_map_congr_comp_inv_app h
      (Category.id_comp p) (by rw [Category.id_comp]) G), hε₂,
    adicUpperStarCongr_inv_app (Category.id_comp p) (Category.id_comp p).symm,
    reassoc_of% adicUpperStarCongr_hom_app_trans, reassoc_of% adicUpperStarCongr_hom_app_trans,
    reassoc_of% adicUpperStarCongr_hom_app_trans]
  all_goals simp [e]

/-- **Restriction of sections in a trivialisation.** The restriction of sections of `p^* G`
along an endomorphism `h` of `W` over `Y`, in the coordinates of `trivId ε`, pulls back the
column of functions along `h` and multiplies it by the transition matrix of `h, 𝟙`. -/
lemma resOver_freeSection (h : W ⟶ W) (e : h ≫ p = p)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l W) :
    ((Sheaf.Γ _ _).map (trivId ε).hom.hom).hom (((resOver _ h e).app G.X).hom
      (((Sheaf.Γ _ _).map (trivId ε).inv.hom).hom (freeSection f))) =
      freeSection (unitMatrix (transitionHom ε (h ≫ 𝟙 W) (𝟙 W)
        (by rw [Category.comp_id, e, Category.id_comp])) *ᵥ
          fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l h.base.hom (f i)) := by
  rw [← trivId_conj ε h e, ← Γ_map_freeSection, ← globalSectionsToUpperStar_freeSection]
  have nat : (Sheaf.Γ _ _).map (trivId ε).inv.hom ≫ (globalSectionsToUpperStar _ h).app
      ((p)^*[WeilCoefficients.{u} l].obj G.X) =
      (globalSectionsToUpperStar _ h).app (⨁ fun _ : Fin n ↦ unit l W).X ≫
        ((h)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _).map (trivId ε).inv.hom :=
    (globalSectionsToUpperStar (WeilCoefficients.{u} l) h).naturality (trivId ε).inv.hom
  have key : (Sheaf.Γ _ _).map (trivId ε).inv.hom ≫ (resOver _ h e).app G.X ≫
      (Sheaf.Γ _ _).map (trivId ε).hom.hom =
      (globalSectionsToUpperStar _ h).app (⨁ fun _ : Fin n ↦ unit l W).X ≫
        (Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) h).hom.hom ≫
          (Sheaf.Γ _ _).map ((freeUpperStarIso l (Fin n) h).inv ≫ (h)^*ᵃ[l].map (trivId ε).inv ≫
            (adicUpperStarComp l h p).inv.app G ≫ (adicUpperStarCongr l e).hom.app G ≫
              (trivId ε).hom).hom := by
    rw [resOver_app, upperStarFactor_inv_app]
    simp only [Category.assoc]
    rw [reassoc_of% nat]
    refine congrArg (_ ≫ ·) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (Sheaf.Γ _ _).map ?_
    rw [← Mod.comp_hom' (freeUpperStarIso l (Fin n) h).hom, Iso.hom_inv_id_assoc]
    simp only [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarComp_inv_app_hom,
      adicUpperStarCongr_hom_app_hom, Category.assoc]
  exact congrArg (fun φ ↦ φ.hom (freeSection f)) key

end Restriction

end AdicSheaf

end AlgebraicGeometry.ProEtale
