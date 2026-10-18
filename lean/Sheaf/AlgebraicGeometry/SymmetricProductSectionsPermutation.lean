/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductSections
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.Data.List.FinRange
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Permutation isomorphisms for symmetric-product coefficient sections

Construct the tensor permutation isomorphism together with its action on pure sections,
then reindex the coefficient sums. Source: symmetric-product-properties, proof step 5;
Stacks Tag 0A4F.
-/

@[expose] public section
universe v
open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use the pullback API without unfolding its sheafification construction.
attribute [local irreducible] tensorPullback

private noncomputable def listTensor {X : Scheme.{v}} {ι : Type*}
    (L : ι → X.Modules) : List ι → X.Modules
  | [] => 𝟙_ X.Modules
  | i :: l => L i ⊗ listTensor L l

private noncomputable def listTensorValue {X : Scheme.{v}} {ι : Type*}
    (L : ι → X.Modules) (t : ∀ i, Γ(L i, ⊤)) : (l : List ι) → Γ(listTensor L l, ⊤)
  | [] => unitSectionsEquiv ⊤ 1
  | i :: l => tmulSection (t i) (listTensorValue L t l)

private theorem listTensor_perm {X : Scheme.{v}} {ι : Type*} (L : ι → X.Modules)
    {l l' : List ι} (h : l.Perm l') :
    ∃ e : listTensor L l ≅ listTensor L l',
      ∀ t : ∀ i, Γ(L i, ⊤), e.hom.app ⊤ (listTensorValue L t l) =
        listTensorValue L t l' := by
  induction h with
  | nil => exact ⟨Iso.refl _, fun _ ↦ rfl⟩
  | cons i h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨Iso.refl (L i) ⊗ᵢ e, ?_⟩
    intro t
    change ((𝟙 (L i)) ⊗ₘ e.hom).app ⊤ (tmulSection _ _) = _
    rw [tensorHom_app_tmulSection, he]
    rfl
  | swap i k l =>
    refine ⟨(α_ (L k) (L i) (listTensor L l)).symm ≪≫
      ((β_ (L k) (L i)) ⊗ᵢ Iso.refl _) ≪≫ (α_ (L i) (L k) (listTensor L l)), ?_⟩
    intro t
    change (α_ (L i) (L k) (listTensor L l)).hom.app ⊤
      (((β_ (L k) (L i)).hom ⊗ₘ (𝟙 _)).app ⊤
        ((α_ (L k) (L i) (listTensor L l)).inv.app ⊤ (tmulSection _ (tmulSection _ _)))) = _
    rw [associator_inv_app_tmulSection, tensorHom_app_tmulSection,
      braiding_hom_app_tmulSection, associator_hom_app_tmulSection]
    rfl
  | trans h h' ih ih' =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := ih'
    refine ⟨e ≪≫ e', ?_⟩
    intro t
    change e'.hom.app ⊤ (e.hom.app ⊤ _) = _
    rw [he, he']

private theorem listTensor_snoc {X : Scheme.{v}} {ι : Type*} (L : ι → X.Modules)
    (l : List ι) (i : ι) :
    ∃ e : listTensor L (l ++ [i]) ≅ listTensor L l ⊗ L i,
      ∀ t : ∀ i, Γ(L i, ⊤), e.hom.app ⊤ (listTensorValue L t (l ++ [i])) =
        tmulSection (listTensorValue L t l) (t i) := by
  induction l with
  | nil =>
    refine ⟨(ρ_ (L i)) ≪≫ (λ_ (L i)).symm, ?_⟩
    intro t
    change (λ_ (L i)).inv.app ⊤ ((ρ_ (L i)).hom.app ⊤
      (tmulSection (t i) (unitSectionsEquiv ⊤ 1))) = _
    rw [rightUnitor_hom_app_tmulSection, one_smul, leftUnitor_inv_app]
    rfl
  | cons k l ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(Iso.refl (L k) ⊗ᵢ e) ≪≫ (α_ (L k) (listTensor L l) (L i)).symm, ?_⟩
    intro t
    change (α_ (L k) (listTensor L l) (L i)).inv.app ⊤
      (((𝟙 (L k)) ⊗ₘ e.hom).app ⊤
      (tmulSection (t k) (listTensorValue L t (l ++ [i])))) = _
    rw [tensorHom_app_tmulSection, he]
    change (α_ (L k) (listTensor L l) (L i)).inv.app ⊤ (tmulSection (t k)
      (tmulSection (listTensorValue L t l) (t i))) = _
    rw [associator_inv_app_tmulSection]
    rfl

private noncomputable def positiveValue {X : Scheme.{v}} :
    (n : ℕ) → (L : Fin (n + 1) → X.Modules) →
      (∀ i, Γ(L i, ⊤)) → Γ(positiveTensorFamily n L, ⊤)
  | 0, _, t => t 0
  | n + 1, L, t => tmulSection
      (positiveValue n (fun i ↦ L i.castSucc) (fun i ↦ t i.castSucc))
      (t (Fin.last (n + 1)))

private theorem positiveValue_section {X : Scheme.{v}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) (t : ∀ i, (L i).sections) :
    ((positiveTensorFamilySection n L t).val (op ⊤)) =
      positiveValue n L (fun i ↦ (t i).val (op ⊤)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tmulSection _ _ = tmulSection _ _
    rw [ih]

private theorem positiveTensor_list {X : Scheme.{v}} {ι : Type*} (L : ι → X.Modules)
    (n : ℕ) (a : Fin (n + 1) → ι) :
    ∃ e : positiveTensorFamily n (fun i ↦ L (a i)) ≅ listTensor L (List.ofFn a),
      ∀ t : ∀ i, Γ(L i, ⊤), e.hom.app ⊤
        (positiveValue n (fun i ↦ L (a i)) (fun i ↦ t (a i))) =
          listTensorValue L t (List.ofFn a) := by
  induction n with
  | zero =>
    refine ⟨(ρ_ (L (a 0))).symm, ?_⟩
    intro t
    exact rightUnitor_inv_app (t (a 0))
  | succ n ih =>
    obtain ⟨e, he⟩ := ih (fun i ↦ a i.castSucc)
    obtain ⟨e', he'⟩ := listTensor_snoc L (List.ofFn (fun i ↦ a i.castSucc))
      (a (Fin.last (n + 1)))
    rw [List.ofFn_succ', List.concat_eq_append]
    refine ⟨(e ⊗ᵢ Iso.refl _) ≪≫ e'.symm, ?_⟩
    intro t
    change e'.inv.app ⊤ ((e.hom ⊗ₘ (𝟙 _)).app ⊤ (tmulSection _ _)) = _
    rw [tensorHom_app_tmulSection, he]
    have h := congrArg (e'.inv.app ⊤) (he' t)
    rw [inv_app_hom_app_apply_of_iso] at h
    exact h.symm

private theorem positiveTensor_perm {X : Scheme.{v}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) (π : Equiv.Perm (Fin (n + 1))) :
    ∃ e : positiveTensorFamily n (fun i ↦ L (π i)) ≅ positiveTensorFamily n L,
      ∀ t : ∀ i, Γ(L i, ⊤), e.hom.app ⊤
        (positiveValue n (fun i ↦ L (π i)) (fun i ↦ t (π i))) = positiveValue n L t := by
  obtain ⟨e₁, he₁⟩ := positiveTensor_list L n π
  have hp : (List.ofFn (fun i ↦ π i)).Perm (List.ofFn id) := π.ofFn_comp_perm id
  obtain ⟨e₂, he₂⟩ := listTensor_perm L hp
  obtain ⟨e₃, he₃⟩ := positiveTensor_list L n id
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃.symm, ?_⟩
  intro t
  change e₃.inv.app ⊤ (e₂.hom.app ⊤ (e₁.hom.app ⊤ _)) = _
  rw [he₁, he₂, ← he₃]
  exact inv_app_hom_app_apply_of_iso _ _

private theorem positiveTensor_mapIso {X : Scheme.{v}} (n : ℕ)
    (L N : Fin (n + 1) → X.Modules) (e : ∀ i, L i ≅ N i) :
    ∃ E : positiveTensorFamily n L ≅ positiveTensorFamily n N,
      ∀ t : ∀ i, Γ(L i, ⊤), E.hom.app ⊤ (positiveValue n L t) =
        positiveValue n N (fun i ↦ (e i).hom.app ⊤ (t i)) := by
  induction n with
  | zero => exact ⟨e 0, fun _ ↦ rfl⟩
  | succ n ih =>
    obtain ⟨E, hE⟩ := ih (fun i ↦ L i.castSucc) (fun i ↦ N i.castSucc)
      (fun i ↦ e i.castSucc)
    refine ⟨E ⊗ᵢ e (Fin.last (n + 1)), ?_⟩
    intro t
    change (E.hom ⊗ₘ (e _).hom).app ⊤ (tmulSection _ _) = _
    rw [tensorHom_app_tmulSection, hE]
    rfl

private theorem tensor_pullback_top {X Y : Scheme.{v}} (f : X ⟶ Y)
    (M N : Y.Modules) :
    ∃ e : (tensorPullback f).obj (M ⊗ N) ≅
        (tensorPullback f).obj M ⊗ (tensorPullback f).obj N,
      ∀ (s : Γ(M, ⊤)) (t : Γ(N, ⊤)), e.hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (M ⊗ N)).val.app (op ⊤) (tmulSection s t)) =
        tmulSection
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
            (op ⊤) s)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
            (op ⊤) t) := by
  obtain ⟨e, _, he⟩ := module_pullback_tensor f
  exact ⟨e M N, he M N ⊤⟩

private theorem compose_pullback_top {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Z ⟶ X)
    (N : Y.Modules) [N.IsInvertible] :
    ∃ e : (tensorPullback g).obj ((tensorPullback f).obj N) ≅
        (tensorPullback (g ≫ f)).obj N,
      ∀ s : Γ(N, ⊤), e.hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          ((tensorPullback f).obj N)).val.app (op ⊤)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
            (op ⊤) s)) =
        ((Classical.choose (exists_tensorPullbackAdjunction (g ≫ f))).unit.app N).val.app
          (op ⊤) s := by
  obtain ⟨e, he⟩ := (invertible_pullback_tensor f).2.2.2.1 Z g N
  exact ⟨e, he ⊤⟩

private theorem positiveTensor_pullback {X Y : Scheme.{v}} (f : X ⟶ Y) (n : ℕ)
    (L : Fin (n + 1) → Y.Modules) :
    ∃ E : (tensorPullback f).obj (positiveTensorFamily n L) ≅
        positiveTensorFamily n (fun i ↦ (tensorPullback f).obj (L i)),
      ∀ t : ∀ i, Γ(L i, ⊤), E.hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (positiveTensorFamily n L)).val.app (op ⊤) (positiveValue n L t)) =
        positiveValue n (fun i ↦ (tensorPullback f).obj (L i))
          (fun i ↦ ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
            (L i)).val.app (op ⊤) (t i)) := by
  induction n with
  | zero => exact ⟨Iso.refl _, fun _ ↦ rfl⟩
  | succ n ih =>
    obtain ⟨e', he'⟩ := ih (fun i ↦ L i.castSucc)
    obtain ⟨e, he⟩ := tensor_pullback_top f
      (positiveTensorFamily n (fun i ↦ L i.castSucc)) (L (Fin.last (n + 1)))
    refine ⟨e ≪≫ (e' ⊗ᵢ Iso.refl _), ?_⟩
    intro t
    simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
      positiveValue, positiveTensorFamily, tensorIso_hom, Iso.refl_hom]
    rw [he]
    rw [tensorHom_app_tmulSection]
    rw [he']
    rfl

/-- Evaluate a pulled-back coordinate section using the pullback adjunction unit. -/
theorem factorSection_eval {X S : Scheme.{v}} {n : ℕ}
    (pr : Fin n → (X ⟶ ℙ(ULift.{v} (Fin 2); S))) (i : Fin n) (k : Fin 2) :
    (symmetricProductFactorSection pr i k).val (op ⊤) =
      (((Classical.choose (exists_tensorPullbackAdjunction (pr i))).unit.app
        (ProjectiveSpace.twist _ S 1)).val.app (op ⊤)
          (ProjectiveSpace.twistOneSection _ S (ULift.up k))) := by
  change (homOfGlobalSection (symmetricProductFactor pr i) _).app ⊤ (1 : Γ(X, ⊤)) = _
  simpa using homOfGlobalSection_app_one (symmetricProductFactor pr i) _ ⊤

private theorem compose_eq_pullback_top {X Y Z : Scheme.{v}}
    (f : X ⟶ Y) (g : Z ⟶ X) (h : Z ⟶ Y) (hh : g ≫ f = h)
    (N : Y.Modules) [N.IsInvertible] :
    ∃ e : (tensorPullback g).obj ((tensorPullback f).obj N) ≅
        (tensorPullback h).obj N,
      ∀ s : Γ(N, ⊤), e.hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          ((tensorPullback f).obj N)).val.app (op ⊤)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
            (op ⊤) s)) =
        ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app N).val.app
          (op ⊤) s := by
  subst h
  exact compose_pullback_top f g N

private theorem factors_pullback {S X : Scheme.{v}} (m : ℕ)
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{v} (Fin 2); S))) (f : X ⟶ X)
    (π : Equiv.Perm (Fin (m + 1))) (hf : ∀ i, f ≫ pr i = pr (π i)) :
    ∃ e : ∀ i, (tensorPullback f).obj (symmetricProductFactor pr i) ≅
        symmetricProductFactor pr (π i),
      ∀ i k, (e i).hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (symmetricProductFactor pr i)).val.app (op ⊤)
            ((symmetricProductFactorSection pr i k).val (op ⊤))) =
          (symmetricProductFactorSection pr (π i) k).val (op ⊤) := by
  classical
  have h (i : Fin (m + 1)) := compose_eq_pullback_top
    (pr i) f (pr (π i)) (hf i) (ProjectiveSpace.twist _ S 1)
  choose e he using h
  refine ⟨e, ?_⟩
  intro i k
  simpa only [factorSection_eval, symmetricProductFactor] using
    he i (ProjectiveSpace.twistOneSection _ S (ULift.up k))

/-- Evaluation of a finite sum of section morphisms is the sum of their evaluations. -/
theorem unitHomEquiv_sum_eval {X : Scheme.{v}} (M : X.Modules)
    {ι : Type*} (A : Finset ι) (t : ι → M.sections) :
    (M.unitHomEquiv (∑ i ∈ A, M.unitHomEquiv.symm (t i))).val (op ⊤) =
      ∑ i ∈ A, (t i).val (op ⊤) := by
  classical
  induction A using Finset.induction_on with
  | empty => rfl
  | @insert i A hi ih =>
    simp only [Finset.sum_insert hi, SheafOfModules.unitHomEquiv_apply_coe,
      SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add,
      LinearMap.add_apply] at ih ⊢
    rw [← SheafOfModules.unitHomEquiv_apply_coe, Equiv.apply_symm_apply, ih]

/-- Reordering the factors identifies the pulled-back coefficient sections with themselves.
Source: symmetric-product-properties, proof step 5, and Stacks Tag 0A4F.
(blueprint: lem-weil-pbc-symmetric-product-sections-permutation)

Proof: Pullback commutes with the ordered tensor product. Pullback composition identifies
the pullback of the i-th factor with the π(i)-th original factor, preserving its two
coordinate sections. Reorder the resulting tensor factors using associativity and
symmetry. This composite isomorphism takes the pure tensor indexed by a subset J to
the pure tensor indexed by π(J). The map J ↦ π(J) is a bijection of the subsets of each
fixed cardinality. Additivity therefore identifies the sums defining each F_j. -/
theorem symmetricProduct_sections_permutation {S X : Scheme.{v}} (m : ℕ)
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{v} (Fin 2); S)))
    (f : X ⟶ X) (π : Equiv.Perm (Fin (m + 1)))
    (hf : ∀ i, f ≫ pr i = pr (π i)) :
    ∃ β : (Scheme.Modules.tensorPullback f).obj (symmetricProductLineBundle pr) ≅
        symmetricProductLineBundle pr,
      ∀ j : ULift.{v} (Fin (m + 2)),
        β.hom.app ⊤ (((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
            (symmetricProductLineBundle pr)).val.app (Opposite.op ⊤)
              ((symmetricProductCoordinateSection pr j).val (Opposite.op ⊤))) =
          (symmetricProductCoordinateSection pr j).val (Opposite.op ⊤) := by
  classical
  obtain ⟨e₁, he₁⟩ := positiveTensor_pullback f m (symmetricProductFactor pr)
  obtain ⟨ef, hef⟩ := factors_pullback m pr f π hf
  obtain ⟨e₂, he₂⟩ := positiveTensor_mapIso m
    (fun i ↦ (tensorPullback f).obj (symmetricProductFactor pr i))
    (fun i ↦ symmetricProductFactor pr (π i)) ef
  obtain ⟨e₃, he₃⟩ := positiveTensor_perm m (symmetricProductFactor pr) π
  let β := e₁ ≪≫ e₂ ≪≫ e₃
  let t (J : Finset (Fin (m + 1))) := positiveTensorFamilySection m
    (symmetricProductFactor pr)
    (fun i ↦ symmetricProductFactorSection pr i (if i ∈ J then 0 else 1))
  have ht (J : Finset (Fin (m + 1))) :
      β.hom.app ⊤
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (symmetricProductLineBundle pr)).val.app (op ⊤) ((t J).val (op ⊤))) =
        (t (J.map π.toEmbedding)).val (op ⊤) := by
    simp only [β, Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
      t, positiveValue_section, symmetricProductLineBundle]
    rw [he₁, he₂]
    simp_rw [hef]
    let q : ∀ i, Γ(symmetricProductFactor pr i, ⊤) := fun i ↦
      (symmetricProductFactorSection pr i (if π.symm i ∈ J then 0 else 1)).val (op ⊤)
    have hq : (fun i ↦ (symmetricProductFactorSection pr (π i)
        (if i ∈ J then 0 else 1)).val (op ⊤)) = (fun i ↦ q (π i)) := by
      funext i
      simp only [q, Equiv.symm_apply_apply]
    rw [hq, he₃]
    congr 1
    funext i
    simp only [q, Finset.mem_map_equiv]
  refine ⟨β, ?_⟩
  intro j
  have hs (k : ULift.{v} (Fin (m + 2))) :
      (symmetricProductCoordinateSection pr k).val (op ⊤) =
        ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset.filter
          (fun J ↦ J.card = k.down.val), (t J).val (op ⊤) :=
    unitHomEquiv_sum_eval _ _ _
  rw [hs, map_sum, map_sum]
  apply Finset.sum_equiv π.finsetCongr
  · intro J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Equiv.finsetCongr_apply, Finset.card_map]
  · intro J hJ
    exact ht J

end AlgebraicGeometry
