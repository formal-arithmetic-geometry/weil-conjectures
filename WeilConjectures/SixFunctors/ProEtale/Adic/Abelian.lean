/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Kernels and cokernels of constructible `ℓ`-adic sheaves

A morphism `ψ : ℚ̄_ℓ,Tⁿ ⟶ ℚ̄_ℓ,Tᵐ` of finite free modules is a matrix of locally finite continuous
functions on `T` (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix`). If its rank at the points
of `T` is constant, then locally on `T` it is equivalent to `[[1, 0], [0, 0]]`, so its kernel and
cokernel are lisse (`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_rank_eq`).
-/

@[expose] public section

open CategoryTheory Limits

lemma CategoryTheory.conj_eq_comp_conj {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} (c : F₁ ≅ F₂) {X Y : C} (φ : X ⟶ Y) {A B A' B' : D}
    (t₁ : F₁.obj X ≅ A) (s₁ : F₁.obj Y ≅ B) (t₂ : F₂.obj X ≅ A') (s₂ : F₂.obj Y ≅ B') :
    t₁.inv ≫ F₁.map φ ≫ s₁.hom =
      (t₁.symm ≪≫ c.app X ≪≫ t₂).hom ≫ (t₂.inv ≫ F₂.map φ ≫ s₂.hom) ≫
        (s₂.symm ≪≫ (c.app Y).symm ≪≫ s₁).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.hom_inv_id_assoc, NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]

universe u

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AdicSheaf

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A finite free module over a finite index type is a free module over `Fin n`. -/
noncomputable def freeFinIso (ι : Type) [Fintype ι] (V : Scheme.{u}) :
    (⨁ fun _ : ι ↦ unit l V) ≅ ⨁ fun _ : Fin (Fintype.card ι) ↦ unit l V :=
  biproduct.whiskerEquiv (g := fun _ : Fin (Fintype.card ι) ↦ unit l V) (Fintype.equivFin ι)
    fun _ ↦ Iso.refl (unit l V)

/-- **Kernels and cokernels of constant rank are lisse.** A morphism of finite free
`ℚ̄_ℓ,T`-modules whose matrix of functions has the same rank at every point of `T` has lisse
kernel and cokernel. -/
theorem isAdicLisseSheaf_kernel_cokernel_of_rank_eq
    (ψ : (⨁ fun _ : ι ↦ unit l T) ⟶ ⨁ fun _ : κ ↦ unit l T) (r : ℕ)
    (hr : ∀ t, ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank = r) :
    IsAdicLisseSheaf (kernel ψ) ∧ IsAdicLisseSheaf (cokernel ψ) := by
  classical
  choose U ρ γ hρ hγ hU ht hfac using
    fun t ↦ PadicAlgCl.exists_isOpen_eq_mul (unitMatrix ψ) r hr t
  let O (t : T) : T.Opens := ⟨U t, hU t⟩
  have hR : Presieve.ofArrows (fun t ↦ (O t).toScheme) (fun t ↦ (O t).ι) ∈
      Scheme.proetalePrecoverage T :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2 ⟨fun x ↦ ⟨x, by simpa [O] using ht x⟩,
        fun _ ↦ inferInstance⟩)
  have key (t : T) : ∃ (P : Matrix κ κ _) (Q : Matrix ι ι _), IsUnit P.det ∧ IsUnit Q.det ∧
      unitMatrix ((freeUpperStarIso l ι (O t).ι).inv ≫ ((O t).ι)^*ᵃ[l].map ψ ≫
        (freeUpperStarIso l κ (O t).ι).hom) = P * (Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range (ρ t)}) (Fin r ⊕ {j // j ∉ Set.range (γ t)}) _).reindex
            (PadicAlgCl.sumComplEquiv (ρ t) (hρ t)).symm
            (PadicAlgCl.sumComplEquiv (γ t) (hγ t)).symm * Q := by
    obtain ⟨P, Q, hP, hQ, h⟩ := hfac t (O t).ι.base.hom (by simp [O])
    exact ⟨P, Q, hP, hQ, (unitMatrix_adicUpperStar _ ψ).trans h⟩
  refine ⟨⟨_, hR, ?_⟩, ⟨_, hR, ?_⟩⟩ <;> rintro _ _ ⟨t⟩ <;>
    obtain ⟨P, Q, hP, hQ, h⟩ := key t <;>
    have hconj := eq_blockMap_of_unitMatrix_eq _ P Q h <;>
    have := isIso_ofUnitMatrix P hP <;> have := isIso_ofUnitMatrix Q hQ
  · exact ⟨_, ⟨PreservesKernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (kernelIsIsoComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ kernelCompMono _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ kernelIsoOfEq hconj ≪≫
      kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _ ≪≫ kernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩
  · exact ⟨_, ⟨PreservesCokernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (cokernelEpiComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ cokernelCompIsIso _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ cokernelIsoOfEq hconj ≪≫
      cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ cokernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩

section Rank

variable {P : Scheme.{u}} {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- The pointwise rank of a morphism of finite free modules is invariant under composition with
isomorphisms. -/
lemma rank_unitMatrix_eq_of_eq_comp
    (ψ₁ : (⨁ fun _ : ι ↦ unit l P) ⟶ ⨁ fun _ : κ ↦ unit l P)
    (ψ₂ : (⨁ fun _ : ι' ↦ unit l P) ⟶ ⨁ fun _ : κ' ↦ unit l P)
    (α : (⨁ fun _ : ι' ↦ unit l P) ≅ ⨁ fun _ : ι ↦ unit l P)
    (β : (⨁ fun _ : κ ↦ unit l P) ≅ ⨁ fun _ : κ' ↦ unit l P)
    (h : ψ₂ = α.hom ≫ ψ₁ ≫ β.hom) (t : P) :
    ((unitMatrix ψ₂).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank =
      ((unitMatrix ψ₁).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank := by
  have h' : ψ₁ = α.inv ≫ ψ₂ ≫ β.inv := by
    rw [h, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine le_antisymm ?_ ?_
  · rw [h, unitMatrix_comp, unitMatrix_comp,
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t),
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [h', unitMatrix_comp, unitMatrix_comp,
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t),
      Matrix.map_mul (f := PadicAlgCl.locallyFiniteFunctionsEval t)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

section Transport

variable {Y V : Scheme.{u}} {n : ℕ}

/-- Transport of a trivialisation `h^* F ≅ ℚ̄_ℓⁿ` along a morphism `g`. -/
noncomputable def trivPull {F : AdicSheaf l Y} (h : V ⟶ Y)
    (e : (h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V) (g : P ⟶ V) :
    (g ≫ h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l P :=
  (adicUpperStarComp l g h).app F ≪≫ (g)^*ᵃ[l].mapIso e ≪≫ freeUpperStarIso l (Fin n) g

lemma trivPull_conj {F G : AdicSheaf l Y} (φ : F ⟶ G) (h : V ⟶ Y) {m : ℕ}
    (e : (h)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V)
    (e' : (h)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m ↦ unit l V) (g : P ⟶ V) :
    (trivPull h e g).inv ≫ (g ≫ h)^*ᵃ[l].map φ ≫ (trivPull h e' g).hom =
      (freeUpperStarIso l (Fin n) g).inv ≫ (g)^*ᵃ[l].map (e.inv ≫ (h)^*ᵃ[l].map φ ≫ e'.hom) ≫
        (freeUpperStarIso l (Fin m) g).hom := by
  have := (adicUpperStarComp l g h).hom.naturality φ
  simp only [Functor.comp_map] at this
  simp only [trivPull, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, Functor.map_comp]
  rw [reassoc_of% this, Iso.inv_hom_id_app_assoc]

end Transport

section Descent

variable {Y V V' : Scheme.{u}} {F G : AdicSheaf l Y} (φ : F ⟶ G) {n m n' m' : ℕ}

/-- **The pointwise rank of a morphism of lisse sheaves descends.** Trivialising a morphism of
sheaves over two weakly étale maps, the matrices of functions have the same rank at points with
the same image. -/
lemma rank_eq_of_apply_eq (f : V ⟶ Y) (f' : V' ⟶ Y) [WeaklyEtale f] [WeaklyEtale f']
    (e : (f)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V)
    (e₂ : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m ↦ unit l V)
    (e' : (f')^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n' ↦ unit l V')
    (e₂' : (f')^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin m' ↦ unit l V')
    (v : V) (v' : V') (hvv' : f v = f' v') :
    ((unitMatrix (e.inv ≫ (f)^*ᵃ[l].map φ ≫ e₂.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval v)).rank =
      ((unitMatrix (e'.inv ≫ (f')^*ᵃ[l].map φ ≫ e₂'.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval v')).rank := by
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback v v' hvv'
  have key := conj_eq_comp_conj (adicUpperStarCongr l (pullback.condition (f := f) (g := f'))) φ
    (trivPull f e (pullback.fst f f')) (trivPull f e₂ (pullback.fst f f'))
    (trivPull f' e' (pullback.snd f f')) (trivPull f' e₂' (pullback.snd f f'))
  rw [trivPull_conj, trivPull_conj] at key
  have hX := rank_unitMatrix_eq_of_eq_comp _ _ _ _ key w
  rw [unitMatrix_adicUpperStar, unitMatrix_adicUpperStar] at hX
  have e1 {W P' : Scheme.{u}} {a b : ℕ} (M : Matrix (Fin a) (Fin b) _) (g : P' ⟶ W) (w : P') :
      (M.map (PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval w) =
        M.map (PadicAlgCl.locallyFiniteFunctionsEval (g w)) := by
    ext; rfl
  rw [e1, e1, hw, hw'] at hX
  exact hX

end Descent

end Rank

end AdicSheaf

end AlgebraicGeometry.ProEtale
