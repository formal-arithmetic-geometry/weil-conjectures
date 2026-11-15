/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechDegreewiseProjection
import WeilConjectures.AlgebraicGeometry.SignedCechExtension
import WeilConjectures.Topology.Sheaves.CechComparison
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates

/-! # Differential compatibility of degreewise signed projection

## References

* [Stacks, Tags 01FK and 01FM]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem filtered_signed_extension (X : Scheme.{u}) {I : Type*} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (a : S.cochains F p) (t : Fin (p + 1) → I) :
    (∑ σ : Equiv.Perm (Fin (p + 1)),
      if _h : StrictMono (t ∘ σ) then
        (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (a (t ∘ σ))
      else 0) = signedCechExtension X U F S p (fun b ↦ a b.1) t := by
  classical
  change _ = signedCechExtensionValue X U F S p (fun b ↦ a b.1) t
  by_cases ht : Function.Injective t
  · have hm : StrictMono (t ∘ Tuple.sort t) :=
      (Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)
    rw [signedCechExtensionValue, dite_eq_left ht]
    rw [Finset.sum_eq_single (Tuple.sort t)]
    · simp only [dite_eq_left hm]
    · intro σ _ hσ
      have hn : ¬ StrictMono (t ∘ σ) := by
        intro h
        apply hσ
        apply Equiv.ext
        intro i
        apply ht
        exact congrFun (Tuple.unique_monotone h.monotone (Tuple.monotone_sort t)) i
      simp only [dite_eq_right hn]
    · simp
  · rw [signedCechExtensionValue, dite_eq_right ht]
    apply Finset.sum_eq_zero
    intro σ _
    have hn : ¬ StrictMono (t ∘ σ) := by
      intro h
      apply ht
      intro a b hab
      have he := h.injective (show (t ∘ σ) (σ.symm a) = (t ∘ σ) (σ.symm b) by
        simpa using hab)
      simpa using congrArg σ he
    simp only [dite_eq_right hn]

private theorem signed_projection_differential (X : Scheme.{u}) {I : Type*} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (a : S.cochains F p) :
    S.differentialValue F p (signedCechExtension X U F S p (fun b ↦ a b.1)) =
      signedCechExtension X U F S (p + 1)
        (fun b ↦ S.differentialValue F p a b.1) := by
  rw [signedCechExtension_differential]
  congr 1
  funext t
  unfold SiteCechComplex.differentialValue
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact signedCechExtension_increasing X U F S p (fun b ↦ a b.1)
    ⟨t.1 ∘ j.succAbove, t.2.comp j.strictMono_succAbove⟩

/-- The intersection model on the base open `B` (Stacks, Tag 01FJ). -/
private noncomputable def naturalCechSectionSite {X : Scheme.{u}} {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) :
    SiteCechComplex (fun i : Fin r ↦ W ⟨i⟩ ⊓ B)
      (fun i ↦ homOfLE (le_top : W ⟨i⟩ ⊓ B ≤ ⊤)) where
  W p t := ⨅ k : Fin (p + 1), W ⟨t k⟩ ⊓ B
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k; exact Subsingleton.elim _ _
    · intro b _; exact Subsingleton.elim _ _
  W_zero := by intro t; simp
  pr_zero := by intro t; exact Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

/-- Restriction from the chosen product to the intersection model (Stacks, Tag 01FJ). -/
private noncomputable def naturalCechSectionMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    (naturalCechSectionSite W B).W p t ⟶ (∏ᶜ fun k ↦ W ⟨t k⟩) ⨯ B :=
  prod.lift (Pi.lift fun k ↦ homOfLE ((iInf_le _ k).trans inf_le_left))
    (homOfLE ((iInf_le _ 0).trans inf_le_right))

private theorem naturalCechSectionMap_isIso {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    IsIso (naturalCechSectionMap W B t) := by
  apply (PartialOrder.isIso_iff_eq _).mpr
  apply le_antisymm (naturalCechSectionMap W B t).le
  apply le_iInf
  intro k
  exact le_inf (prod.fst ≫ Pi.π (fun l ↦ W ⟨t l⟩) k).le prod.snd.le

/-- All tuple coordinates, transported by actual restriction maps (Stacks, Tag 01FJ). -/
private noncomputable def naturalCechSectionCochain {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    (naturalCechSectionSite W B).cochains M.presheaf p :=
  fun t ↦ M.presheaf.map (naturalCechSectionMap W B t).op
    (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t k⟩) s)

set_option backward.isDefEq.respectTransparency false in
private theorem naturalCechSectionCochain_projection {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (Q : ∀ p : ℕ, D.X p ⟶ D.X p)
    (hQ : IsOrderedCechNaturalProjection M W D e Q)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    naturalCechSectionCochain M W D e p B ((Q p).app B s) =
      signedCechExtension X (fun i : Fin r ↦ W ⟨i⟩ ⊓ B) M.presheaf
        (naturalCechSectionSite W B) p
        (fun t ↦ naturalCechSectionCochain M W D e p B s t.1) := by
  classical
  funext t
  rw [← filtered_signed_extension]
  unfold naturalCechSectionCochain
  rw [hQ, orderedCechNaturalProjectionValue, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Function.comp_apply]
  split_ifs with h h'
  · rw [map_zsmul]
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (σ k)⟩) s) =
      (M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (σ k)⟩) s)
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp]
    congr 2
  · exact False.elim (h' h)
  · rename_i h'
    exact False.elim (h h')
  · simp only [map_zero]

private theorem naturalCechSectionCochain_injective {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) :
    Function.Injective (naturalCechSectionCochain M W D e p B) := by
  intro s z h
  apply (ConcreteCategory.bijective_of_isIso ((e p).hom.app (op B))).injective
  apply Concrete.isLimit_ext _
    (isLimitOfPreserves ((evaluation _ _).obj (op B))
      (limit.isLimit (Discrete.functor (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
            (op (∏ᶜ fun k ↦ W (y k)))))))
  intro y
  let t : Fin (p + 1) → Fin r := fun k ↦ (y.as k).down
  have ht := congrFun h t
  have : IsIso (naturalCechSectionMap W B t) := naturalCechSectionMap_isIso W B t
  apply (ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (naturalCechSectionMap W B t).op)).injective
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate transport identifies the given differential with the alternating face sum
(Stacks, Tags 01FJ and 01FK). -/
private theorem naturalCechSectionCochain_differential {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).d p (p + 1))
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    naturalCechSectionCochain M W D e (p + 1) B ((D.d p (p + 1)).app B s) =
      (naturalCechSectionSite W B).differentialValue M.presheaf p
        (naturalCechSectionCochain M W D e p B s) := by
  classical
  funext t
  let F := (prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat
  have h := congrArg
    (fun f ↦ ((f ≫ TopCat.Presheaf.cechComplexFunctorπ W F (p + 1)
      (fun k ↦ ⟨t k⟩)).app (op B)) s) (hd p)
  simp only [Category.assoc] at h
  rw [TopCat.Presheaf.cechComplexFunctor_d_π W F] at h
  change orderedCechNaturalCoordinate M W D e (p + 1) B (fun k ↦ ⟨t k⟩)
    ((D.d p (p + 1)).app B s) = _ at h
  unfold naturalCechSectionCochain
  rw [h]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, NatTrans.app_sum, NatTrans.app_zsmul,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  unfold SiteCechComplex.differentialValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s) =
    (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s)
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

/-- The degreewise signed formula commutes with the Čech differential
(Stacks, Tags 01FK and 01FM). -/
theorem orderedCech_degreewise_projection_comm {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (Q : ∀ p : ℕ, D.X p ⟶ D.X p)
    (hQ : IsOrderedCechNaturalProjection M W₀ D e Q) (p : ℕ) :
    Q p ≫ D.d p (p + 1) = D.d p (p + 1) ≫ Q (p + 1) := by
  classical
  apply Modules.hom_ext
  intro B
  ext s
  apply naturalCechSectionCochain_injective M W₀ D e (p + 1) B
  change naturalCechSectionCochain M W₀ D e (p + 1) B
      ((D.d p (p + 1)).app B ((Q p).app B s)) =
    naturalCechSectionCochain M W₀ D e (p + 1) B
      ((Q (p + 1)).app B ((D.d p (p + 1)).app B s))
  rw [naturalCechSectionCochain_differential M W₀ D e hd,
    naturalCechSectionCochain_projection M W₀ D e Q hQ,
    signed_projection_differential,
    naturalCechSectionCochain_projection M W₀ D e Q hQ,
    naturalCechSectionCochain_differential M W₀ D e hd]

end AlgebraicGeometry.Scheme.Modules
