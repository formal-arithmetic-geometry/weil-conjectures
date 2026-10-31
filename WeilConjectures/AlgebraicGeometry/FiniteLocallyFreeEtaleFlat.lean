/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

/-!
# Flatness of locally free constant-coefficient sheaves
Source: Stacks Project, Modules on Sites, lemmas flatness-sheafification-refined
and flatness-local; the constant coefficient realization identifies the scalar actions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.ProEtale

private theorem finite_cover {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {U : C} {I : Type*} [Finite I]
    (S : I → Sieve U) (hS : ∀ i, S i ∈ J U) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ i, T ≤ S i := by
  classical
  have := Fintype.ofFinite I
  have h (A : Finset I) : ∃ T : Sieve U, T ∈ J U ∧ ∀ i ∈ A, T ≤ S i := by
    induction A using Finset.induction_on with
    | empty => exact ⟨⊤, J.top_mem _, by simp⟩
    | @insert i A hi ih =>
      obtain ⟨T, hT, hTS⟩ := ih
      exact ⟨S i ⊓ T, J.intersection_covering (hS i) hT,
        fun j hj ↦ by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact inf_le_left
          · exact inf_le_right.trans (hTS j hj)⟩
  simpa using h Finset.univ

private theorem local_basis_maps
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}}
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {M : SheafOfModules.{u + 1} R} {I : Type (u + 1)} [Fintype I]
    (e : SheafOfModules.free I ≅ M) (V : Cᵒᵖ) :
    ∃ (b : I → M.val.obj V)
      (c : I → M.val.obj V →ₗ[R.obj.obj V] R.obj.obj V),
      ∀ x, x = ∑ i, c i x • b i := by
  classical
  let S (i : I) : SheafOfModules.unit R ⟶ M :=
    Sigma.ι (fun _ ↦ SheafOfModules.unit R) i ≫ e.hom
  let P (i : I) : M ⟶ SheafOfModules.unit R :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = i then 𝟙 _ else 0)
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (SheafOfModules.unit R) else 0) ≫
      Sigma.ι (fun _ : I ↦ SheafOfModules.unit R) i = 𝟙 (SheafOfModules.free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, P i ≫ S i = 𝟙 M := by
    calc
      _ = e.inv ≫ (∑ i, Sigma.desc
          (fun k ↦ if k = i then 𝟙 (SheafOfModules.unit R) else 0) ≫
          Sigma.ι (fun _ : I ↦ SheafOfModules.unit R) i) ≫ e.hom := by
        simp only [P, S, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 _ := by rw [hsum, Category.id_comp, Iso.inv_hom_id]
  let Ev := SheafOfModules.evaluation R V
  have : Ev.Additive := ⟨by intros; rfl⟩
  let S' (i : I) : R.obj.obj V →ₗ[R.obj.obj V] M.val.obj V :=
    ((S i).val.app V).hom
  let P' (i : I) : M.val.obj V →ₗ[R.obj.obj V] R.obj.obj V :=
    ((P i).val.app V).hom
  refine ⟨fun i ↦ S' i 1, P', fun x ↦ ?_⟩
  have ht : Ev.map (∑ i, P i ≫ S i) = Ev.map (𝟙 M) := congrArg Ev.map htot
  rw [Functor.map_sum, Ev.map_id] at ht
  have h := congrArg (fun f ↦ f.hom x) ht
  simp only [Functor.map_comp, ModuleCat.hom_sum,
    ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at h
  change (∑ i, S' i (P' i x)) = x at h
  calc
    x = ∑ i, S' i (P' i x) := h.symm
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by
      simpa only [smul_eq_mul, mul_one] using (S' i).map_smul (P' i x) 1

private def factorSieve {C : Type (u + 1)} [Category.{u} C]
    {Λ : Type (u + 1)} [CommRing Λ] (L : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    {V : C} {n q : ℕ} (y : Fin n → L.obj (op V))
    (a : Matrix (Fin q) (Fin n) Λ) : Sieve V where
  arrows W f := ∃ (t : ℕ) (b : Matrix (Fin n) (Fin t) Λ)
    (z : Fin t → L.obj (op W)), a * b = 0 ∧
      ∀ j, L.map f.op (y j) = ∑ k, b j k • z k
  downward_closed := by
    rintro W Z f ⟨t, b, z, hb, hz⟩ g
    refine ⟨t, b, fun k ↦ L.map g.op (z k), hb, fun j ↦ ?_⟩
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      hz, map_sum, map_smul]

/-- A fixed-ring sheaf whose canonical ringed-site realization is finite locally free
is a flat object for the ordinary sheaf tensor product.

Source: Stacks Project, Modules on Sites, section Flat modules, lemmas
flatness-sheafification-refined and flatness-local; the local basis characterization
of finite locally free modules.

Proof: The local generators data give a covering on which the realization is the free
module on `Fin t`. The constant-ring sheafification unit is locally bijective; hence
on the localized site the equivalence `finiteCoefficientEtaleRealization` identifies
this free ringed module with the constant sheaf on the free Lambda-module on `Fin t`.
At every geometric point, lift the point through this cover. Applying the fibre functor
to the basis and coordinate maps identifies the fibre of L with this free Lambda-module.
Its tensor functor is the finite direct sum of the identity, hence is exact, also when
t = 0 or Lambda is the zero ring. Flatness of etale fixed-ring sheaves is detected on
these geometric fibres by `Etale.flat_iff_forall_flat_sheafFiber_obj`; therefore L is flat.
No assumption about flatness over another ring occurs.
(blueprint: lem-pur-finite-locally-free-etale-flat). -/
theorem flat_of_finiteCoefficientEtaleRealization_locallyFree
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (t : ℕ)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (R := finiteCoefficientEtaleRingSheaf X Λ)
      ((finiteCoefficientEtaleRealization X Λ).obj L) t) :
    ObjectProperty.flat L := by
  classical
  let J := X.smallEtaleTopology
  let R := finiteCoefficientEtaleRingSheaf X Λ
  let α : (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj :=
    toSheafify J ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ))
  let P := (finiteCoefficientModulePresheaf X.Etale Λ).obj L.obj
  let M := (finiteCoefficientEtaleRealization X Λ).obj L
  let η : P ⟶ (PresheafOfModules.restrictScalars α).obj M.val :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app P
  have hη : IsIso η := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify J P.presheaf)
    apply isIso_toSheafify
    exact ((sheafCompose J (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj L).property
  have ηbij (V : X.Etaleᵒᵖ) : Function.Bijective (η.app V) := by
    change Function.Bijective ((PresheafOfModules.evaluation _ V).map η)
    exact ConcreteCategory.bijective_of_isIso _
  have ηinj (V : X.Etaleᵒᵖ) := (ηbij V).1
  have ηsurj (V : X.Etaleᵒᵖ) := (ηbij V).2
  let φ (V : X.Etaleᵒᵖ) : L.obj.obj V →+ M.val.obj V :=
    { toFun := fun x ↦ η.app V x
      map_zero' := (η.app V).hom.map_zero
      map_add' := (η.app V).hom.map_add }
  have φsmul (V : X.Etaleᵒᵖ) (a : Λ) (x : L.obj.obj V) :
      φ V (a • x) = α.app V a • φ V x :=
    (η.app V).hom.map_smul a x
  have φnat {V W : X.Etaleᵒᵖ} (f : V ⟶ W) (x : L.obj.obj V) :
      M.val.map f (φ V x) = φ W (L.obj.map f x) :=
    (PresheafOfModules.naturality_apply η f x).symm
  apply (Sheaf.flat_iff_hasLocallyTrivialRelations L).mpr
  intro V n q y a ha
  obtain ⟨d, hd, hr⟩ := hL.exists_localGeneratorsData
  refine ⟨factorSieve L.obj y a, ?_, fun _ _ h ↦ h⟩
  apply J.transitive (d.coversTop V)
  rintro W f ⟨i, ⟨g⟩⟩
  let K := (d.generators i).I
  let ek : K ≃ Fin t := (hr i).some
  have : Fintype K := Fintype.ofEquiv (Fin t) ek.symm
  have : IsIso (d.generators i).π := hd.isIso i
  obtain ⟨b, c, hc⟩ := local_basis_maps (asIso (d.generators i).π) (op (Over.mk g))
  let s (j : Fin n) : M.val.obj (op W) := φ (op W) (L.obj.map f.op (y j))
  let coeff (jk : Fin n × K) : R.obj.obj (op W) := c jk.2 (s jk.1)
  obtain ⟨S, hS, hSc⟩ := finite_cover J
    (fun jk : Fin n × K ↦ Presheaf.imageSieve α (coeff jk))
    (fun _ ↦ Presheaf.imageSieve_mem J α _)
  apply J.transitive hS
  intro Z h hh
  have hcoords (j : Fin n) (k : K) : ∃ r : Λ,
      α.app (op Z) r = R.obj.map h.op (coeff (j, k)) := hSc (j, k) h hh
  choose B hB using hcoords
  let z (k : K) : L.obj.obj (op Z) :=
    (ηsurj (op Z) (M.val.map h.op (b k))).choose
  have hz (k : K) : φ (op Z) (z k) = M.val.map h.op (b k) :=
    (ηsurj (op Z) (M.val.map h.op (b k))).choose_spec
  have hs (j : Fin n) : L.obj.map (h ≫ f).op (y j) = ∑ k, B j k • z k := by
    apply ηinj (op Z)
    change φ (op Z) (L.obj.map (h ≫ f).op (y j)) =
      φ (op Z) (∑ k, B j k • z k)
    rw [map_sum]
    simp only [φsmul]
    simp only [hz, hB]
    have H := congrArg (M.val.map h.op) (hc (s j))
    simp only [map_sum, M.val.map_smul] at H
    rw [← H]
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact (φnat h.op _).symm
  have hzero (l : Fin q) (k : K) :
      α.app (op Z) (∑ j, a l j * B j k) = 0 := by
    have H : ∑ j, α.app (op W) (a l j) • s j = 0 := by
      have H := congrArg (fun x ↦ φ (op W) (L.obj.map f.op x)) (ha l)
      simpa only [map_sum, map_smul, map_zero, φsmul] using H
    have H' := congrArg (c k) H
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at H'
    have H'' := congrArg (R.obj.map h.op) H'
    simp only [map_sum, map_zero] at H''
    simp only [map_sum, map_mul, hB]
    rw [← H'']
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    congr 1
    exact α.naturality_apply h.op (a l j)
  obtain ⟨T, hT, hTc⟩ := finite_cover J
    (fun lk : Fin q × K ↦ Presheaf.equalizerSieve (F := (Functor.const
      X.Etaleᵒᵖ).obj (RingCat.of Λ)) (∑ j, a lk.1 j * B j lk.2) 0)
    (fun lk ↦ Presheaf.equalizerSieve_mem J α _ _ (by
      simpa only [map_zero] using hzero lk.1 lk.2))
  apply J.superset_covering _ hT
  intro U v hv
  refine ⟨t, fun j k ↦ B j (ek.symm k),
    fun k ↦ L.obj.map v.op (z (ek.symm k)), ?_, ?_⟩
  · ext l k
    exact hTc (l, ek.symm k) v hv
  · intro j
    have H := congrArg (L.obj.map v.op) (hs j)
    simp only [map_sum, map_smul] at H
    change L.obj.map (v ≫ h ≫ f).op (y j) = _
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rw [H]
    exact Fintype.sum_equiv ek _ _ (fun k ↦ by simp)

end AlgebraicGeometry.ProEtale
