/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.PseudoCoherentSummand
import WeilConjectures.AlgebraicGeometry.DerivedTensorVanishingRetract
import WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import all WeilConjectures.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude
import all WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.OpenImmersionTensorVanishingTest
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Direct summands of perfect complexes

Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A direct summand of a perfect complex is perfect, and the complementary summand
is perfect as well. First, `lem-pc-perfect-pseudo-coherent-locally-finite-tor` gives
pseudo-coherence and Tor amplitude in an interval on a neighbourhood of each point.
Second, `lem-pc-pseudo-coherent-summand` gives pseudo-coherence of both summands.
Third, both summands are retracts of K; derived pullback, derived tensor and
homology preserve these retracts. The proved
`lem-pc-derived-tensor-vanishing-retract` passes the same local Tor interval
to both summands (Tag 08CK). Finally,
`lem-pc-pseudo-coherent-locally-finite-tor-perfect` constructs perfect models
on affine subopens of the Tor neighbourhoods and gives perfectness on X.
Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand). -/
theorem perfect_of_directSum
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPerfect X K) :
    IsPerfect X L ∧ IsPerfect X M := by
  classical
  let hOpen (U : X.Opens) :
      HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    (hasDerivedCategory_of_equivalence (Modules.overEquiv U).symm).some
  let : ∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := hOpen
  obtain ⟨hpc, htor⟩ := perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension X K hK
  obtain ⟨hLpc, hMpc⟩ := pseudoCoherent_of_isIso_biproduct X K L M h hpc
  obtain ⟨e⟩ := h
  let rL : Retract L K :=
    { i := biprod.inl ≫ e.inv
      r := e.hom ≫ biprod.fst
      retract := by simp [Category.assoc] }
  let rM : Retract M K :=
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp [Category.assoc] }
  have tor_of_retract (N : schemeDerivedCategory X) (r : Retract N K) :
      HasLocallyFiniteTorDimension X N := by
    intro x
    obtain ⟨U, hx, a, b, hab, hU⟩ := htor x
    refine ⟨U, hx, a, b, hab, ?_⟩
    intro G i hi
    exact schemeDerivedTensorCohomologyVanishes_of_retract U.toScheme _ _
      (r.map (derivedPullback U.ι)) G i (hU G i hi)
  have perfect_of_pc_tor (N : schemeDerivedCategory X) (hN : IsPseudoCoherent X N)
      (hTor : HasLocallyFiniteTorDimension X N) : IsPerfect X N := by
    intro x
    obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hN x
    obtain ⟨W, hxW, a, c, hac, hW⟩ := hTor x
    obtain ⟨V, hV, hxV, hVUW⟩ :=
      exists_isAffineOpen_mem_and_subset (U := U ⊓ W) ⟨hxU, hxW⟩
    have hVU : V ≤ U := hVUW.trans inf_le_left
    have hVW : V ≤ W := hVUW.trans inf_le_right
    let F := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
    let G := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
    have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (PV.X i) := by
      obtain ⟨N, hN⟩ := hb
      exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
    have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
      obtain ⟨r, ⟨e⟩⟩ := hf i
      let ef : F.obj (SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))) ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
        (asIso (Limits.sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦
          SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
            Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso
              (R := moduleRings X.toRingedSpace) (homOfLE hVU))
      exact ⟨r, ⟨F.mapIso e ≪≫ ef⟩⟩
    have : Limits.PreservesFiniteLimits (G ⋙ F) := Limits.comp_preservesFiniteLimits _ _
    have : Limits.PreservesFiniteColimits (G ⋙ F) := Limits.comp_preservesFiniteColimits _ _
    let eV : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj N ≅
          DerivedCategory.Q.obj PV :=
      (Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE hVU))).symm.app N ≪≫
        (Functor.mapDerivedCategoryCompIso G F).symm.app N ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
          F.mapDerivedCategoryFactors.app P
    obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_finiteFree_model X V hV PV hbV hfV
    let R := X.presheaf.obj (.op V)
    let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
    have hMpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
      ⟨M, b, hMb, hMf, ⟨Iso.refl _⟩⟩
    let eKM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
    have hMtor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
        (ModuleCat.{u} R) a b (DerivedCategory.Q.obj M) := by
      let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
          (moduleRings (Spec (X.presheaf.obj (.op V))).toRingedSpace)) :=
        HasDerivedCategory.standard _
      let Z := Spec (X.presheaf.obj (.op V))
      let j : Z ⟶ W.toScheme := hV.isoSpec.inv ≫ X.homOfLE hVW
      let RW : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
        Modules.restrictFunctor W.ι
      have : RW.Additive := ⟨by intros; rfl⟩
      have : PreservesFiniteLimits RW := by
        dsimp [RW, Modules.restrictFunctor]
        infer_instance
      have : RW.IsLeftAdjoint := by
        let H : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace) := Modules.pushforward W.ι
        exact (show RW ⊣ H from Modules.restrictAdjunction W.ι).isLeftAdjoint
      let RJ : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings Z.toRingedSpace) := Modules.restrictFunctor j
      have : RJ.Additive := ⟨by intros; rfl⟩
      have : PreservesFiniteLimits RJ := by
        dsimp [RJ, Modules.restrictFunctor]
        infer_instance
      have : RJ.IsLeftAdjoint := by
        let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Modules.pushforward j
        exact (show RJ ⊣ H from Modules.restrictAdjunction j).isLeftAdjoint
      let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
      let E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ≌
          SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.overEquiv V
      have : E.functor.Additive := ⟨by intros; rfl⟩
      let T : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
        Modules.restrictFunctor hV.isoSpec.inv
      have : T.Additive := ⟨by intros; rfl⟩
      have : PreservesFiniteLimits T := by
        dsimp [T, Modules.restrictFunctor]
        infer_instance
      let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
        Modules.pushforward hV.isoSpec.inv
      have adjT : T ⊣ H := Modules.restrictAdjunction hV.isoSpec.inv
      have : T.IsLeftAdjoint := adjT.isLeftAdjoint
      let B := E.functor ⋙ T
      have : B.Additive := inferInstance
      have : PreservesFiniteLimits B := comp_preservesFiniteLimits _ _
      have : B.IsLeftAdjoint := (E.toAdjunction.comp adjT).isLeftAdjoint
      let T' : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
        Modules.restrictFunctor hV.isoSpec.hom
      have : T'.Additive := ⟨by intros; rfl⟩
      have : HasBinaryBiproducts
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) :=
        HasBinaryBiproducts.of_hasBinaryProducts
      have : PreservesBinaryBiproducts E.inverse :=
        preservesBinaryBiproducts_of_preservesBinaryProducts _
      have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
      let L : ModuleCat.{u} (X.presheaf.obj (.op V)) ⥤
          SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
        tilde.functor (X.presheaf.obj (.op V))
      have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
      have : (affinePerfectSheafification X V hV).Additive := by
        change (L ⋙ T' ⋙ E.inverse).Additive
        infer_instance
      obtain ⟨C, hC, ⟨eC⟩⟩ := AlgebraicGeometry.exists_kFlat_model X N
      obtain ⟨eCW⟩ := AlgebraicGeometry.open_pullback_model_iso W.ι C hC
      let eW : (derivedPullback W.ι).obj N ≅ RW.mapDerivedCategory.obj N :=
        (derivedPullback W.ι).mapIso eC.symm ≪≫ eCW ≪≫
          (RW.mapDerivedCategoryFactors.app C).symm ≪≫ RW.mapDerivedCategory.mapIso eC
      let θ : RW ⋙ RJ ≅ A ⋙ B := by
        exact (Modules.restrictFunctorComp j W.ι).symm ≪≫
          Modules.restrictFunctorCongr (by simp [j, Category.assoc]) ≪≫
          Modules.restrictFunctorComp hV.isoSpec.inv V.ι ≪≫
          Functor.isoWhiskerRight (Modules.overFunctorEquiv V).symm
            (Modules.restrictFunctor hV.isoSpec.inv)
      let eP := eKM
      let e : RJ.mapDerivedCategory.obj ((derivedPullback W.ι).obj N) ≅
          DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (X.presheaf.obj (.op V)))
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) _ _ _ _
              (tilde.functor (X.presheaf.obj (.op V))) ⟨fun _ _ ↦ tilde.map_zero⟩
              (ComplexShape.up ℤ)).obj M) := by
        exact RJ.mapDerivedCategory.mapIso eW ≪≫
          ((Functor.mapDerivedCategoryCompIso RW RJ).app N) ≪≫
          (Functor.mapDerivedCategoryNatIso θ).app N ≪≫
          (Functor.mapDerivedCategoryCompIso A B).symm.app N ≪≫
          B.mapDerivedCategory.mapIso eP ≪≫ B.mapDerivedCategoryFactors.app _ ≪≫
          DerivedCategory.Q.mapIso
            ((Functor.mapHomologicalComplexCompIso
              (F := affinePerfectSheafification X V hV) (G := B) (H := L)
              (affine_cancel X V hV) (.up ℤ)).app M)
      let hvan := hW
      let b := c
      have hab : a ≤ b := hac
      refine ⟨a, b, hab, (affine_torAmplitude_iff (X.presheaf.obj (.op V)) M a b hab).mp ?_⟩
      intro G i hi
      have hv := openImmersion_tensor_vanishing_test j
        ((derivedPullback W.ι).obj N) G i (hvan ((Modules.pushforward j).obj G) i hi)
      obtain ⟨D, hD, ⟨eD⟩, hz⟩ := hv
      exact ⟨D, hD, ⟨eD ≪≫ e⟩, hz⟩
    obtain ⟨E, hEb, hEf, hEp, ⟨eE⟩⟩ :=
      DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
        (DerivedCategory.Q.obj M) hMpc hMtor
    let T := (affinePerfectSheafification X V hV).mapHomologicalComplex (.up ℤ)
    obtain ⟨D, _, ⟨c⟩⟩ := affine_localized_derived_sheafification X V hV
    refine ⟨V, hxV, T.obj E, affine_projective_strictlyPerfect X V hV E hEb hEf hEp, ?_⟩
    exact ⟨eKM ≪≫ (c.app M).symm ≪≫ D.mapIso eE.symm ≪≫ c.app E⟩
  exact ⟨perfect_of_pc_tor L hLpc
      (tor_of_retract L rL),
    perfect_of_pc_tor M hMpc
      (tor_of_retract M rM)⟩

end AlgebraicGeometry.Scheme
