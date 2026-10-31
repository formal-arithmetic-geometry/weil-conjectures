/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteAdicTowerCompletedTensorLimit
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Completed tensors and a cofinal quotient tower

Source: latest blueprint, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-cofinal-tower-completed-tensor-limit). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme

private theorem cofinal_quotient_limit_iso {R : Type u} [Ring R]
    {C : Type w} [Category* C] [HasLimitsOfShape ℕᵒᵖ C]
    {N : ModuleCat.{v} R} {D F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    (p : (Functor.const ℕᵒᵖ).obj N ⟶ F)
    (q : (Functor.const ℕᵒᵖ).obj N ⟶ D)
    (hp : ∀ n : ℕ, Epi (p.app (op n)))
    (hq : ∀ n : ℕ, Epi (q.app (op n)))
    (g : D ⟶ F) (hg : q ≫ g = p)
    (hfactor : ∀ n : ℕ, ∃ (m : ℕ) (_h : n ≤ m)
      (f : F.obj (op m) ⟶ D.obj (op n)), p.app (op m) ≫ f = q.app (op n))
    (K : ModuleCat.{v} R ⥤ C) : IsIso (lim.map (Functor.whiskerRight g K)) := by
  classical
  choose m hm f hf using hfactor
  have hpw {a b : ℕ} (h : b ≤ a) :
      p.app (op a) ≫ F.map (homOfLE h).op = p.app (op b) := by
    simpa using (p.naturality (homOfLE h).op).symm
  have hqw {a b : ℕ} (h : b ≤ a) :
      q.app (op a) ≫ D.map (homOfLE h).op = q.app (op b) := by
    simpa using (q.naturality (homOfLE h).op).symm
  have hgn (n : ℕ) : q.app (op n) ≫ g.app (op n) = p.app (op n) :=
    congrArg (fun t ↦ t.app (op n)) hg
  have hfg (n : ℕ) : f n ≫ g.app (op n) = F.map (homOfLE (hm n)).op := by
    let := hp (m n)
    apply (cancel_epi (p.app (op (m n)))).mp
    rw [← Category.assoc, hf, hgn, hpw]
  have hgf (n : ℕ) : g.app (op (m n)) ≫ f n = D.map (homOfLE (hm n)).op := by
    let := hq (m n)
    apply (cancel_epi (q.app (op (m n)))).mp
    rw [← Category.assoc, hgn, hf, hqw]
  let j := Functor.whiskerRight g K
  let d (n : ℕ) : limit (F ⋙ K) ⟶ K.obj (D.obj (op n)) :=
    limit.π (F ⋙ K) (op (m n)) ≫ K.map (f n)
  have hd (n : ℕ) : d n ≫ K.map (g.app (op n)) = limit.π (F ⋙ K) (op n) := by
    dsimp only [d]
    rw [Category.assoc, ← K.map_comp, hfg]
    exact limit.w (F ⋙ K) (homOfLE (hm n)).op
  let c : Cone (D ⋙ K) :=
    { pt := limit (F ⋙ K)
      π :=
        { app := fun n ↦ d n.unop
          naturality := by
            intro a b α
            let k := max (m a.unop) (m b.unop)
            have hka : m a.unop ≤ k := le_max_left _ _
            have hkb : m b.unop ≤ k := le_max_right _ _
            have hα : b.unop ≤ a.unop := leOfHom α.unop
            have hab : α = (homOfLE hα).op := Subsingleton.elim _ _
            have he : F.map (homOfLE hka).op ≫ f a.unop ≫ D.map α =
                F.map (homOfLE hkb).op ≫ f b.unop := by
              let := hp k
              apply (cancel_epi (p.app (op k))).mp
              simp only [← Category.assoc, hpw]
              rw [hf, hf, hab, hqw]
            have hwa := limit.w (F ⋙ K) (homOfLE hka).op
            have hwb := limit.w (F ⋙ K) (homOfLE hkb).op
            have hn : d a.unop ≫ (D ⋙ K).map α = d b.unop := by
              dsimp only [d, Functor.comp_map]
              rw [← hwa, ← hwb]
              simp only [Functor.comp_map, Category.assoc, ← K.map_comp]
              exact congrArg (limit.π (F ⋙ K) (op k) ≫ ·) (congrArg K.map he)
            simp only [Functor.const_obj_map]
            exact (Category.id_comp (d b.unop)).trans hn.symm } }
  let h : limit (F ⋙ K) ⟶ limit (D ⋙ K) := limit.lift (D ⋙ K) c
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply limit.hom_ext
    intro n
    calc
      (lim.map j ≫ h) ≫ limit.π (D ⋙ K) n = lim.map j ≫ d n.unop := by
        simp only [h, Category.assoc, limit.lift_π]
        rfl
      _ = (lim.map j ≫ limit.π (F ⋙ K) (op (m n.unop))) ≫
          K.map (f n.unop) := by simp only [d, Category.assoc]
      _ = (limit.π (D ⋙ K) (op (m n.unop)) ≫
          K.map (g.app (op (m n.unop)))) ≫ K.map (f n.unop) := by
        exact congrArg (· ≫ K.map (f n.unop))
          (limMap_π j (op (m n.unop)))
      _ = limit.π (D ⋙ K) (op (m n.unop)) ≫
          K.map (D.map (homOfLE (hm n.unop)).op) := by
        rw [Category.assoc, ← K.map_comp, hgf]
      _ = limit.π (D ⋙ K) n := limit.w (D ⋙ K) (homOfLE (hm n.unop)).op
      _ = 𝟙 _ ≫ limit.π (D ⋙ K) n := by simp
  · apply limit.hom_ext
    intro n
    calc
      (h ≫ lim.map j) ≫ limit.π (F ⋙ K) n =
          h ≫ (limit.π (D ⋙ K) n ≫ K.map (g.app n)) := by
        rw [Category.assoc]
        exact congrArg (h ≫ ·) (limMap_π j n)
      _ = d n.unop ≫ K.map (g.app n) := by
        simp only [h, ← Category.assoc, limit.lift_π]
        rfl
      _ = limit.π (F ⋙ K) n := hd n.unop
      _ = 𝟙 _ ≫ limit.π (F ⋙ K) n := by simp


private theorem quotient_tower_limit_iso {R : Type u} [CommRing R]
    {C : Type w} [Category* C] [HasLimitsOfShape ℕᵒᵖ C]
    (π : R) (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (hproj : ∀ n : ℕ, Function.Surjective (limit.π F (op n)))
    (hkill : ∀ (n : ℕ) (x : F.obj (op n)), π ^ (n + 1) • x = 0)
    (hcofinal : ∀ r : ℕ, 1 ≤ r → ∃ n : ℕ,
      ∀ x : (limit F : ModuleCat.{v} R),
        (limit.π F (op n)) x = 0 → ∃ z : (limit F : ModuleCat.{v} R), π ^ r • z = x)
    (K : ModuleCat.{v} R ⥤ C) :
    let I := Ideal.span ({π} : Set R)
    let N := (limit F : ModuleCat.{v} R)
    let D := Functor.ofOpSequence
      (X := fun n : ℕ ↦ ModuleCat.of R (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)))
      (fun n ↦ ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))
    Nonempty (limit (F ⋙ K) ≅ limit (D ⋙ K)) := by
  classical
  let I := Ideal.span ({π} : Set R)
  let N := (limit F : ModuleCat.{v} R)
  let D := Functor.ofOpSequence
    (X := fun n : ℕ ↦ ModuleCat.of R (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)))
    (fun n ↦ ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1)))
  let p := (limit.cone F).π
  let q : (Functor.const ℕᵒᵖ).obj N ⟶ D :=
    NatTrans.ofOpSequence
      (fun n ↦ ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule R N)))
      (by
        intro n
        simp only [Functor.const_obj_map, D,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply ModuleCat.hom_ext
        ext x
        rfl)
  have hp (n : ℕ) : Epi (p.app (op n)) :=
    (ModuleCat.epi_iff_surjective _).mpr (hproj n)
  have hq (n : ℕ) : Epi (q.app (op n)) :=
    (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  have hzero (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule R N) ≤
      LinearMap.ker (p.app (op n)).hom := by
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    intro x hx
    obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact (map_smul (p.app (op n)).hom _ _).trans (hkill n _)
  let gapp (n : ℕ) : D.obj (op n) ⟶ F.obj (op n) :=
    ModuleCat.ofHom ((I ^ (n + 1) • ⊤ : Submodule R N).liftQ
      (p.app (op n)).hom (hzero n))
  have hqg (n : ℕ) : q.app (op n) ≫ gapp n = p.app (op n) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  let g : D ⟶ F := NatTrans.ofOpSequence gapp (by
    intro n
    let := hq (n + 1)
    apply (cancel_epi (q.app (op (n + 1)))).mp
    calc
      q.app (op (n + 1)) ≫ D.map (homOfLE (Nat.le_succ n)).op ≫ gapp n =
          q.app (op n) ≫ gapp n := by
        rw [← Category.assoc]
        exact congrArg (· ≫ gapp n)
          (by simpa using (q.naturality (homOfLE (Nat.le_succ n)).op).symm)
      _ = p.app (op n) := hqg n
      _ = p.app (op (n + 1)) ≫ F.map (homOfLE (Nat.le_succ n)).op := by
        simpa using p.naturality (homOfLE (Nat.le_succ n)).op
      _ = q.app (op (n + 1)) ≫ gapp (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op := by rw [← hqg, Category.assoc])
  have hg : q ≫ g = p := by
    apply NatTrans.ext
    exact funext (fun n ↦ hqg n.unop)
  have hf (n : ℕ) : ∃ (m : ℕ) (_h : n ≤ m)
      (f : F.obj (op m) ⟶ D.obj (op n)), p.app (op m) ≫ f = q.app (op n) := by
    obtain ⟨m, hm⟩ := hcofinal (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    let k := max n m
    have hmk : m ≤ k := le_max_right _ _
    have hker : LinearMap.ker (p.app (op k)).hom ≤
        LinearMap.ker (q.app (op n)).hom := by
      intro x hx
      have hxm : (limit.π F (op m)) x = 0 := by
        have hw := ConcreteCategory.congr_hom (limit.w F (homOfLE hmk).op) x
        change (limit.π F (op k)) x = 0 at hx
        calc
          (limit.π F (op m)) x =
              (F.map (homOfLE hmk).op) ((limit.π F (op k)) x) := hw.symm
          _ = 0 := by rw [hx]; exact map_zero (F.map (homOfLE hmk).op).hom
      obtain ⟨z, hz⟩ := hm x hxm
      change Submodule.Quotient.mk x = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, trivial, hz⟩
    let e := (p.app (op k)).hom.quotKerEquivOfSurjective (hproj k)
    let f : F.obj (op k) ⟶ D.obj (op n) := ModuleCat.ofHom
      (((LinearMap.ker (p.app (op k)).hom).liftQ (q.app (op n)).hom hker).comp
        e.symm.toLinearMap)
    refine ⟨k, le_max_left _ _, f, ?_⟩
    apply ModuleCat.hom_ext
    ext x
    change ((LinearMap.ker (p.app (op k)).hom).liftQ (q.app (op n)).hom hker)
      (e.symm ((p.app (op k)) x)) = (q.app (op n)) x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  let := cofinal_quotient_limit_iso p q hp hq g hg hf K
  exact ⟨(asIso (lim.map (Functor.whiskerRight g K))).symm⟩


/-- Completed scalar extension commutes with a cofinal quotient presentation of
an adically complete finite module.
Source: blueprint latest, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-cofinal-tower-completed-tensor-limit).

Proof: the private quotient_tower_limit_iso is proved here. Surjectivity
identifies each F_n with N modulo its projection kernel J_n,
compatibly with all transitions. Annihilation gives pi^(n+1) N contained in J_n;
the cofinality hypothesis gives the reverse inclusions at sufficiently late
indices. Choose monotone cofinal indices in both directions and form the
induced quotient maps. Their composites are transitions; checking all limit
projections proves that the two sheaf-limit comparisons are inverse.
The separate standard adic-tower comparison then identifies that quotient
limit with completed scalar extension of N. Compose the two isomorphisms.
The cofinal comparison uses an arbitrary functor K and no exactness claim:
module-map identities are checked before applying K, by cancelling the
surjective quotient maps from N. This includes zero modules and torsion
summands; no freeness or finite cardinality is used. -/
theorem finite_cofinal_tower_completed_tensor_limit
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (π : A) [IsAdicComplete (Ideal.span ({π} : Set A)) A] (Y : Scheme.{u})
    (F : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (_hproj : ∀ n : ℕ, Function.Surjective (limit.π F (op n)))
    (_hkill : ∀ (n : ℕ) (x : F.obj (op n)), π ^ (n + 1) • x = 0)
    (_hcofinal : ∀ r : ℕ, 1 ≤ r → ∃ n : ℕ,
      ∀ x : (limit F : ModuleCat.{u + 1} A),
        (limit.π F (op n)) x = 0 → ∃ z : (limit F : ModuleCat.{u + 1} A), π ^ r • z = x)
    (_hN : Module.Finite A (limit F : ModuleCat.{u + 1} A)) :
    let K := adicLisseConstantModules Y A ⋙ completedConstantExtension Y
      (CompletedConstantReduction.base Y (Ideal.span ({π} : Set A)))
    Nonempty (limit (F ⋙ K) ≅ K.obj (limit F)) := by
  let K := adicLisseConstantModules Y A ⋙ completedConstantExtension Y
    (CompletedConstantReduction.base Y (Ideal.span ({π} : Set A)))
  obtain ⟨e⟩ := quotient_tower_limit_iso π F _hproj _hkill _hcofinal K
  obtain ⟨t⟩ := finite_adic_tower_completed_tensor_limit π Y (limit F) _hN
  exact ⟨e ≪≫ t⟩

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
