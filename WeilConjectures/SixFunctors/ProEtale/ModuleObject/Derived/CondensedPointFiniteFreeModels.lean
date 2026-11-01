/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.TraceFormula.PointFiberFunctor

import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.CategoryTheory.Preadditive.CokernelBiproduct

/-! # Finite constant models at an algebraically closed point -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section GlobalModel
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- A finite constant model on a geometric point can be chosen globally.
Source: blueprint local boundary duality, Step 5, split-cover descent.
Proof: lift the point to a stratum and split its pro-etale trivializing cover.
Pullback composition transports its finite presented condensed model to the
point. Conversely use the trivial stratification and identity cover.
(blueprint: lem-a1-condensed-point-finite-free-models) -/
theorem point_constant_model_global_iff
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    IsConstantModelConstructible Λ (Spec (.of k)) M ↔
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ P ∧
          Nonempty (((upperStarFromPoint (Spec (.of k))).mapMod Λ).obj P ≅ M) := by
  classical
  have hqc : CompactSpace (Spec (.of k)) ∧ QuasiSeparatedSpace (Spec (.of k)) :=
    ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hqc]
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField
      (S.immersion a) (Field.toIsField k) (𝟙 _) z ha
    obtain ⟨𝒰, h𝒰⟩ := hS a
    obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isSepClosed_of_proetale y
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    let G := CondensedRing.upperStar Λ g
    let N := (CondensedRing.upperStar Λ (𝒰.f i)).obj
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)
    let e : G.obj N ≅ M :=
      G.mapIso ((CondensedRing.upperStarComp Λ (𝒰.f i) (S.immersion a)).app M).symm ≪≫
        ((CondensedRing.upperStarComp Λ g (𝒰.f i ≫ S.immersion a)).app M).symm ≪≫
        eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
          (by rw [reassoc_of% hg, hy])) ≪≫ (CondensedRing.upperStarId Λ _).app M
    exact ⟨P, hP, ⟨((CondensedRing.upperStarFromPointModComp Λ g).app P).symm ≪≫
      G.mapIso eP.symm ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    refine ⟨Scheme.Stratification.trivial _, fun a ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨P, hP, ⟨?_⟩⟩
    exact (CondensedRing.upperStarId Λ _).app _ ≪≫
      (CondensedRing.upperStarId Λ _).app _ ≪≫ eP.symm

end GlobalModel

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- On the geometric point the finite-constant-model predicate means finite free.
Source: blueprint local boundary duality, Step 5, split-cover classification.
Proof: a constructible object has a finite presented condensed model by descent
along a section of a cover. Its presentation matrix has a finite free cokernel,
since every nonzero endomorphism of the regular condensed coefficient is invertible.
The point inverse image preserves finite sums and the regular module. Conversely,
a finite power of the unit is the pullback of the finite free condensed module;
the zero matrix from rank zero presents that model. This includes rank zero.
(blueprint: lem-a1-condensed-point-finite-free-models) -/
theorem constantModelConstructible_iff_pointFiniteFree (M : PointMod ℓ k) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left M ↔
      pointFiniteFree ℓ k M := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := (upperStarFromPoint (point k).left).mapMod Λ
  let r : F.obj (Mod.regular Λ) ≅ 𝟙_ (PointMod ℓ k) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let e (n : ℕ) : F.obj (Mod.finiteFree Λ n) ≅
      ⨁ fun _ : Fin n ↦ 𝟙_ (PointMod ℓ k) :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫ biproduct.mapIso (fun _ ↦ r)
  change IsConstantModelConstructible Λ (Spec (.of k)) M ↔ _
  rw [point_constant_model_global_iff Λ k M]
  constructor
  · rintro ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩
    obtain ⟨d, ⟨ed⟩⟩ := exists_iso_biproduct_cokernel
      (Profinite.PadicAlgCl.isIso_of_ne_zero_end_regular ℓ) (Iso.refl _) (Iso.refl _) f
    exact ⟨d, ⟨eP.symm ≪≫ F.mapIso (ef ≪≫ ed) ≪≫ e d⟩⟩
  · rintro ⟨n, ⟨eM⟩⟩
    refine ⟨Mod.finiteFree Λ n, ⟨n, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩,
      ⟨e n ≪≫ eM.symm⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
