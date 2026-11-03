/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-! # Constructibility of finite free modules on the geometric point

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-free-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

private def constantFreeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n := by
  let F := upperStarFromPoint X
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : (F.mapMod Λ).Additive :=
    { map_add := by
        intros
        exact Mod.hom_ext _ _ F.map_add }
  exact Mod.finiteFreeIsoMap (F.mapMod Λ)
    (Mod.isoMk (Iso.refl _) (by simp)) n

private theorem finiteFree_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (n : ℕ) :
    Mod.IsFinitelyPresented Λ (Mod.finiteFree Λ n) := by
  exact ⟨n, 0, 0, ⟨(cokernelZeroIsoTarget).symm⟩⟩

private theorem constructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hlocal {Y : Scheme.{u}}
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := hM
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat {Y : Scheme.{u}}
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ hlocal ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)
      (hS a)⟩
  classical
  refine ⟨fun e hM ↦ ?_⟩
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · exact hstrat e hM
  · exact fun U hU ↦ hstrat ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

/-- Any module isomorphic to a finite free module on the geometric point has a finite
constant constructible model, including the free module of rank zero.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-free-constructible).

Proof: the finite free condensed module is finitely presented, being the cokernel of
the zero map from the rank-zero free module. Pullback from the condensed point is
additive and takes the regular module to the regular coefficient module, so its
finite biproduct comparison gives the desired constant model. On the trivial
stratification and identity cover this witnesses constructibility. Pulling any
isomorphism through the cover and stratum shows invariance under isomorphisms. -/
theorem point_free_constructible (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology (pointSpace D)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) (pointSpace D)))
    (e : M ≅ free D l n) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (pointSpace D) M := by
  let Λ := Profinite.padicAlgClRingObj l
  have : IsAffine (pointSpace D) := IsAffine.of_isIso
    (pullback.snd (𝟙 (Spec (.of D.k₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  have hfree : IsConstantModelConstructible Λ (pointSpace D) (free D l n) := by
    have hqc : CompactSpace (pointSpace D) ∧ QuasiSeparatedSpace (pointSpace D) :=
      ⟨inferInstance, inferInstance⟩
    rw [IsConstantModelConstructible, if_pos hqc]
    refine ⟨Scheme.Stratification.trivial _, fun a ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨Mod.finiteFree Λ n, finiteFree_finitelyPresented Λ n, ⟨?_⟩⟩
    exact (CondensedRing.upperStarId Λ _).app _ ≪≫
      (CondensedRing.upperStarId Λ _).app _ ≪≫ (constantFreeIso Λ _ n).symm
  exact (constructible_iso Λ (pointSpace D)).of_iso e.symm hfree

end WeilConjectures.CondensedWeilPointFlags
