/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.StableImageTower
import WeilConjectures.AlgebraicGeometry.FiniteCofinalTowerCompletedTensorLimit
import WeilConjectures.NumberTheory.Padics.FiniteTowerStableImages
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Completed tensors and arbitrary finite torsion towers

Source: latest blueprint, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-tower-completed-tensor-limit). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme

private theorem eventual_image_map_limit_iso {C : Type u} [Category* C]
    {D : Type w} [Category* D] [HasLimitsOfShape ℕᵒᵖ D]
    {B F : ℕᵒᵖ ⥤ C} (ι : B ⟶ F)
    (hmono : ∀ n : ℕ, Mono (ι.app (op n)))
    (hfactor : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (f : F.obj (op m) ⟶ B.obj (op n)),
      F.map (homOfLE h).op = f ≫ ι.app (op n))
    (K : C ⥤ D) : IsIso (lim.map (Functor.whiskerRight ι K)) := by
  classical
  choose m hm f hf using hfactor
  have hgf (n : ℕ) : ι.app (op (m n)) ≫ f n = B.map (homOfLE (hm n)).op := by
    let := hmono n
    apply (cancel_mono (ι.app (op n))).mp
    rw [Category.assoc, ← hf]
    exact (ι.naturality (homOfLE (hm n)).op).symm
  let j := Functor.whiskerRight ι K
  let d (n : ℕ) : limit (F ⋙ K) ⟶ K.obj (B.obj (op n)) :=
    limit.π (F ⋙ K) (op (m n)) ≫ K.map (f n)
  have hd (n : ℕ) : d n ≫ K.map (ι.app (op n)) = limit.π (F ⋙ K) (op n) := by
    dsimp only [d]
    rw [Category.assoc, ← K.map_comp, ← hf]
    exact limit.w (F ⋙ K) (homOfLE (hm n)).op
  let c : Cone (B ⋙ K) :=
    { pt := limit (F ⋙ K)
      π :=
        { app := fun n ↦ d n.unop
          naturality := by
            intro a b α
            let k := max (m a.unop) (m b.unop)
            have hka : m a.unop ≤ k := le_max_left _ _
            have hkb : m b.unop ≤ k := le_max_right _ _
            have he : F.map (homOfLE hka).op ≫ f a.unop ≫ B.map α =
                F.map (homOfLE hkb).op ≫ f b.unop := by
              let := hmono b.unop
              apply (cancel_mono (ι.app b)).mp
              calc
                (F.map (homOfLE hka).op ≫ f a.unop ≫ B.map α) ≫ ι.app b =
                    F.map (homOfLE hka).op ≫ f a.unop ≫ (B.map α ≫ ι.app b) := by
                      simp only [Category.assoc]
                _ = F.map (homOfLE hka).op ≫ f a.unop ≫ (ι.app a ≫ F.map α) := by
                      rw [ι.naturality]
                _ = (F.map (homOfLE hka).op ≫
                    (f a.unop ≫ ι.app a)) ≫ F.map α := by simp only [Category.assoc]
                _ = (F.map (homOfLE hka).op ≫
                    F.map (homOfLE (hm a.unop)).op) ≫ F.map α := by rw [← hf]
                _ = F.map (homOfLE hkb).op ≫ F.map (homOfLE (hm b.unop)).op := by
                      rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
                      congr 1
                _ = (F.map (homOfLE hkb).op ≫ f b.unop) ≫ ι.app b := by
                      rw [hf, Category.assoc]
            have hwa := limit.w (F ⋙ K) (homOfLE hka).op
            have hwb := limit.w (F ⋙ K) (homOfLE hkb).op
            have hn : d a.unop ≫ (B ⋙ K).map α = d b.unop := by
              dsimp only [d, Functor.comp_map]
              rw [← hwa, ← hwb]
              simp only [Functor.comp_map, Category.assoc, ← K.map_comp]
              exact congrArg (limit.π (F ⋙ K) (op k) ≫ ·) (congrArg K.map he)
            simp only [Functor.const_obj_map]
            exact (Category.id_comp (d b.unop)).trans hn.symm } }
  let h : limit (F ⋙ K) ⟶ limit (B ⋙ K) := limit.lift (B ⋙ K) c
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply limit.hom_ext
    intro n
    calc
      (lim.map j ≫ h) ≫ limit.π (B ⋙ K) n = lim.map j ≫ d n.unop := by
        simp only [h, Category.assoc, limit.lift_π]
        rfl
      _ = (lim.map j ≫ limit.π (F ⋙ K) (op (m n.unop))) ≫
          K.map (f n.unop) := by simp only [d, Category.assoc]
      _ = (limit.π (B ⋙ K) (op (m n.unop)) ≫
          K.map (ι.app (op (m n.unop)))) ≫ K.map (f n.unop) := by
        exact congrArg (· ≫ K.map (f n.unop))
          (limMap_π j (op (m n.unop)))
      _ = limit.π (B ⋙ K) (op (m n.unop)) ≫
          K.map (B.map (homOfLE (hm n.unop)).op) := by
        rw [Category.assoc, ← K.map_comp, hgf]
      _ = limit.π (B ⋙ K) n := limit.w (B ⋙ K) (homOfLE (hm n.unop)).op
      _ = 𝟙 _ ≫ limit.π (B ⋙ K) n := by simp
  · apply limit.hom_ext
    intro n
    calc
      (h ≫ lim.map j) ≫ limit.π (F ⋙ K) n =
          h ≫ (limit.π (B ⋙ K) n ≫ K.map (ι.app n)) := by
        rw [Category.assoc]
        exact congrArg (h ≫ ·) (limMap_π j n)
      _ = d n.unop ≫ K.map (ι.app n) := by
        simp only [h, ← Category.assoc, limit.lift_π]
        rfl
      _ = limit.π (F ⋙ K) n := hd n.unop
      _ = 𝟙 _ ≫ limit.π (F ⋙ K) n := by simp


private theorem surjective_projections {R : Type u} [Ring R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (h : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) : Function.Surjective (limit.π F (op n)) := by
  let shift : ℕ ⥤ ℕ := (show Monotone (fun k : ℕ ↦ n + k) from
    fun _ _ h ↦ Nat.add_le_add_left h n).functor
  have hfinal : shift.Final := by
    apply (Monotone.final_functor_iff _).2
    intro k
    exact ⟨k, Nat.le_add_left k n⟩
  have hc := (Functor.Initial.isLimitWhiskerEquiv shift.op (limit.cone F)).symm
    (limit.isLimit F)
  have hs : ∀ k : ℕ, Function.Surjective
      ((shift.op ⋙ F).map (homOfLE (Nat.le_succ k)).op) := by
    intro k
    change Function.Surjective (F.map (homOfLE (Nat.le_succ (n + k))).op)
    exact h (n + k)
  exact Concrete.surjective_π_app_zero_of_surjective_map hc hs


private theorem lifted_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsAdicComplete (Ideal.span
      {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)))
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let A := ULift.{u + 1} R
  let π := Padic.coefficientExtensionUniformizer l E
  let e : R ≃+* A := ULift.ringEquiv.symm
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hπ : Ideal.span ({π} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hc : IsAdicComplete (Ideal.span ({π} : Set R)) R := by
    rw [hπ]
    exact Padic.coefficientIntegers_complete l E
  have hmap : (Ideal.span ({π} : Set R)).map e.toRingHom =
      Ideal.span ({ULift.up π} : Set A) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv (Ideal.span ({π} : Set R)) e).mpr hc


private theorem lifted_cofinal_kernels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)))
    (hfinite : ∀ n : ℕ, Finite (F.obj (op n)))
    (hkill : ∀ (n : ℕ) (x : F.obj (op n)),
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)) ^ (n + 1) • x = 0)
    (hN : Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (limit F : ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)))) :
    ∀ r : ℕ, 1 ≤ r → ∃ n : ℕ, ∀ x : (limit F : ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))),
      (limit.π F (op n)) x = 0 → ∃ z : (limit F : ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))),
        (ULift.up (Padic.coefficientExtensionUniformizer l E) : ULift.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) ^ r • z = x := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let A := ULift.{u + 1} R
  let π := Padic.coefficientExtensionUniformizer l E
  let e : R ≃+* A := ULift.ringEquiv.symm
  let U := ModuleCat.restrictScalars.{u + 1} e.toRingHom
  let G := F ⋙ U
  let : ∀ n : ℕ, Finite (G.obj (op n)) := hfinite
  let : Module.Finite A (limit F : ModuleCat.{u + 1} A) := hN
  let q : (limit F : ModuleCat.{u + 1} A) →ₛₗ[e.symm.toRingHom] U.obj (limit F) :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change a • x = e (e.symm a) • x
        rw [e.apply_symm_apply] }
  let : Module.Finite R (U.obj (limit F)) := Module.Finite.of_surjective q
    Function.surjective_id
  let t : U.obj (limit F) ≅ limit G := preservesLimitIso U F
  let : Module.Finite R (limit G : ModuleCat.{u + 1} R) :=
    Module.Finite.equiv t.toLinearEquiv
  have hGkill (n : ℕ) (x : G.obj (op n)) : π ^ (n + 1) • x = 0 := by
    change e.toRingHom (π ^ (n + 1)) • x = 0
    rw [map_pow]
    exact hkill n x
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hπ : Ideal.span ({π} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let τ : TopologicalSpace (limit G : ModuleCat.{u + 1} R) :=
    ⨅ n : ℕ, TopologicalSpace.induced (limit.π G (op n)) ⊥
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc⟩ :=
    Padic.finiteTower_stable_images l E π hπ G hGkill τ rfl
  intro r hr
  obtain ⟨n, hn⟩ := hc r hr
  refine ⟨n, fun x hx ↦ ?_⟩
  have htx : (limit.π G (op n)) (t.hom x) = 0 := by
    have h := ConcreteCategory.congr_hom (preservesLimitIso_hom_π U F (op n)) x
    exact h.trans hx
  have hy := hn htx
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hy
  obtain ⟨z, _, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  refine ⟨t.inv z, ?_⟩
  apply t.toLinearEquiv.injective
  have hs : (π ^ r : R) • t.inv z = (ULift.up π : A) ^ r • t.inv z := by
    change e.toRingHom (π ^ r) • t.inv z = (ULift.up π : A) ^ r • t.inv z
    rw [map_pow]
    rfl
  rw [← hs, map_smul]
  change π ^ r • t.toLinearEquiv (t.toLinearEquiv.symm z) = t.toLinearEquiv x
  rw [t.toLinearEquiv.apply_symm_apply]
  exact hz


/-- Completed scalar extension commutes with the limit of a finite torsion tower
whose inverse limit is finite over the valuation ring.
Source: blueprint latest, smooth-proper purity, Step 1, Passage to the limit
(blueprint: lem-zl-finite-tower-completed-tensor-limit).

Proof: the proved finite-module Mittag-Leffler theorem supplies a subtower B
with monic inclusion, surjective transitions, and eventual factorizations of
all transitions of F. The categorical argument below constructs the inverse
of the map on limits: compose a sufficiently late limit projection with an
eventual factorization to define each B-component, and cancel the monic
inclusions to prove naturality and both inverse identities. This transfers
finiteness of the limit to B, while componentwise injectivity transfers finite
cardinality and annihilation. Surjective transitions imply surjective limit
projections by shifting the tower. Restrict scalars along the ULift ring
equivalence, use its preservation of the limit, apply the stated stable-image
cofinality theorem, and transport divisibility back along the linear limit
isomorphism. Completeness of the coefficient ring transports along the same
ring equivalence. The comparison after applying K is proved in the same way: verify the
transition identities before applying K, using the monic inclusions in the
original category. No exactness or limit-preservation assumption on K is
needed. Apply the cofinal quotient-tower comparison to B and compose
these isomorphisms. This proves the arbitrary-transition result without any
assumption that the original transitions are surjective. -/
theorem finite_tower_completed_tensor_limit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
    (F : ℕᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)))
    (_hfinite : ∀ n : ℕ, Finite (F.obj (op n)))
    (_hkill : ∀ (n : ℕ) (x : F.obj (op n)),
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)) ^ (n + 1) • x = 0)
    (_hN : Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (limit F : ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)))) :
    let K := (Scheme.adicLisseConstantModules Y (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) ⋙ Scheme.completedConstantExtension Y
      (Scheme.CompletedConstantReduction.base Y (Ideal.span
        {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
          (Padic.coefficientExtensionIntegers l E)))))
    Nonempty (limit (F ⋙ K) ≅ K.obj (limit F)) := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let I : Ideal A := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  let a := CompletedConstantReduction.base Y I
  let K := adicLisseConstantModules Y A ⋙ completedConstantExtension Y a
  let : ∀ n : ℕ, Finite (F.obj (op n)) := _hfinite
  let : Module.Finite A (limit F : ModuleCat.{u + 1} A) := _hN
  obtain ⟨B, ι, hmono, hepi, hfactor⟩ := ModuleCat.isMittagLefflerTower_of_finite F
  let : IsIso (lim.map ι) := by
    change IsIso (lim.map (Functor.whiskerRight ι (𝟭 _)))
    exact eventual_image_map_limit_iso ι hmono hfactor (𝟭 _)
  let e : limit B ≅ limit F := asIso (lim.map ι)
  have hBfinite (n : ℕ) : Finite (B.obj (op n)) :=
    Finite.of_injective (ι.app (op n)) ((ModuleCat.mono_iff_injective _).mp (hmono n))
  have hBsurj (n : ℕ) : Function.Surjective (B.map (homOfLE (Nat.le_succ n)).op) :=
    (ModuleCat.epi_iff_surjective _).mp (hepi n)
  have hBkill (n : ℕ) (x : B.obj (op n)) :
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : A) ^ (n + 1) • x = 0 := by
    apply (ModuleCat.mono_iff_injective _).mp (hmono n)
    simpa only [map_smul, map_zero] using _hkill n ((ι.app (op n)) x)
  have hBN : Module.Finite A (limit B : ModuleCat.{u + 1} A) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    hdvr.2.2.2.2.2.2.2.1
  let : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (Padic.coefficientExtensionIntegers l E)
      ULift.ringEquiv.symm
  let j : B ⋙ K ⟶ F ⋙ K := Functor.whiskerRight ι K
  let : IsIso (lim.map j) := eventual_image_map_limit_iso ι hmono hfactor K
  let : IsAdicComplete I A := lifted_complete l E
  obtain ⟨t⟩ := finite_cofinal_tower_completed_tensor_limit
    (ULift.up (Padic.coefficientExtensionUniformizer l E) : A) Y B
    (surjective_projections B hBsurj) hBkill
    (lifted_cofinal_kernels l E B hBfinite hBkill hBN) hBN
  exact ⟨(asIso (lim.map j)).symm ≪≫ t ≪≫ K.mapIso e⟩

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
