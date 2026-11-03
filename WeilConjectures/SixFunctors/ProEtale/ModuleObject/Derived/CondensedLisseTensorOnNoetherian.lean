/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFibreLinearOperationsLisseTensor
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-! # Lisse duals and tensor products on a Noetherian scheme

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2.
(blueprint: lem-fd-condensed-lisse-tensor-noetherian).

The calculation uses the ordinary native module category and the previously specified
canonical derived-tensor comparison. It is independent of a choice of algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem localModelIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨a⟩⟩ := hU i
  exact ⟨P, hP, ⟨(upperStar Λ (U.f i)).mapIso e.symm ≪≫ a⟩⟩

-- These proof helpers are independent of the choice of algebraic closure.
private def modelPointFreeIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n := by
  let F := (upperStarFromPoint X).mapMod Λ
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let e : F.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ X) :=
    Mod.isoMk (Iso.refl _) (by simp only [Mod.act, Iso.refl_hom, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  exact F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫ biproduct.mapIso (fun _ ↦ e)

private theorem modelOfLisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hU i
  exact ⟨Mod.finiteFree Λ r, (Mod.IsFree.isFinitelyPresented ⟨r, ⟨Iso.refl _⟩⟩),
    ⟨e ≪≫ (modelPointFreeIso Λ (U.X i) r).symm⟩⟩

private theorem tensorLocalModel (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (hF : HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj l) X F)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj l) X (F ⊗ L) := by
  let Λ := Profinite.padicAlgClRingObj.{u} l
  have hraw : IsLocallyFree (condensedRingObj Λ X) L := (isLocallyFree_iff L).mpr hL
  have hfp := hraw.isLocallyFinitelyPresented_tensorObj (constantModel_lfp Λ X F hF)
  have hfp' : IsLocallyFinitelyPresented (condensedRingObj Λ X) (F ⊗ L) :=
    hfp.of_iso (β_ L F)
  exact modelOfLisse Λ _
    (lfp_lisse l (Profinite.padicAlgClCondensedRing l) X (Or.inr rfl) _ hfp')

attribute [local irreducible] upperStar upperStarFromPoint
  CondensedRing.upperStarComp CondensedRing.upperStarLowerStarAdjunction
  IsLisseCoefficientModule Mod.monoidalClosed

set_option maxHeartbeats 1200000 in
-- Native module pullback and closed-monoidal comparisons need this elaboration budget.
private theorem tensorRestrictedModel (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y] (f : Y ⟶ X)
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (hF : HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj l) Y
      ((upperStar (Profinite.padicAlgClRingObj l) f).obj F))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj l) Y
      ((upperStar (Profinite.padicAlgClRingObj l) f).obj (F ⊗ L)) := by
  exact localModelIso (Profinite.padicAlgClRingObj l)
    (Functor.Monoidal.μIso (upperStar (Profinite.padicAlgClRingObj l) f) F L)
    (tensorLocalModel l _ _ hF (lisse_pullback (Profinite.padicAlgClRingObj l) f L hL))

set_option maxHeartbeats 1200000 in
-- Native module pullback and closed-monoidal comparisons need this elaboration budget.
private theorem tensorConstructible (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X]
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X F)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X (F ⊗ L) := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hF ⊢
  obtain ⟨S, hS⟩ := hF
  refine ⟨S, fun a ↦ ?_⟩
  have : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  exact tensorRestrictedModel l (S.immersion a) F L (hS a) hL

set_option maxHeartbeats 1200000 in
-- Native module pullback and closed-monoidal comparisons need this elaboration budget.
/-- On any Noetherian scheme, a lisse module has lisse dual, and tensoring a constructible
module with it is constructible with the canonical degree-zero derived comparison invertible.
Source: latest blueprint, `lem-fd-realified-kernel-real.proof.md`, Steps 1--2;
finite-free calculations of `lem-fd-condensed-fibre-linear-operations-lisse-tensor`.
(blueprint: lem-fd-condensed-lisse-tensor-noetherian).

Proof: normalized finite-free local models are equivalent to the raw inverse-image models.
A finite-free module has its finite-free dual, so descent of the exact pairing shows that a
lisse module is dualizable, with locally free internal dual. On each original constructible
stratum, the finite constant model of F is locally finitely presented. Tensoring it with the
locally free restriction of L preserves local finite presentation. Over the condensed
algebraic closure this is locally finite free, hence has a finite constant model pulled back
from the same-rank free module at the point. The pullback tensorator identifies these local
models with the restriction of the ordinary tensor, on the original stratification. Finally
the single complex of a locally free module is K-flat. The canonical lax tensor comparison
of Q is the hom of its K-flat comparison isomorphism; composition with the two single/Q
comparisons and the single-tensor isomorphism is the specified invertible map. All formulas
include the empty scheme and rank zero. -/
theorem lisseTensor_on_noetherian (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X]
    (F L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X F)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) ((ihom L).obj (𝟙_ _)) ∧
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X (F ⊗ L) ∧
      IsIso (lisseTensorDerivedComparison F L) := by
  have hraw : IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) X) L :=
    (isLocallyFree_iff L).mpr (by simpa only [IsLisseCoefficientModule] using hL)
  refine ⟨?_, tensorConstructible l F L hF hL, ?_⟩
  · obtain ⟨_⟩ := hraw.isDualizable
    let : ExactPairing Lᘁ L := BraidedCategory.exactPairing_swap L Lᘁ
    have hd := IsLocallyFree.of_iso (MonoidalClosed.ihomObjUnitIso Lᘁ L).symm
      hraw.of_exactPairing
    exact (by simpa only [IsLisseCoefficientModule] using (isLocallyFree_iff _).mp hd)
  · let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)
    let F₀ := (CochainComplex.singleFunctor A 0).obj F
    let L₀ := (CochainComplex.singleFunctor A 0).obj L
    have hk := (CochainComplex.kFlat_single_obj_iff_flat L 0).mpr hraw.flat
    have he : (DerivedCategory.QObjTensorQObjIsoOfKFlatRight F₀ L₀ hk).hom =
        Functor.LaxMonoidal.μ DerivedCategory.Q F₀ L₀ := by
      simp only [DerivedCategory.QObjTensorQObjIsoOfKFlatRight, Iso.trans_hom, tensorIso_hom,
        Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom]
      change _ = _ ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
        DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
          (HomotopyCategory.quotient A (.up ℤ)) F₀ L₀)) ≫ _
      simp only [Category.assoc, Functor.Monoidal.μIso_hom]
      rfl
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q F₀ L₀) := he ▸ inferInstance
    unfold lisseTensorDerivedComparison
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
