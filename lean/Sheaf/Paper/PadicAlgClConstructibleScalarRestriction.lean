/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all Sheaf.Paper.QcqsConstructibleIntegralLatticeTree
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.Paper.LisseFiniteCoefficientModel
import Sheaf.Paper.CoefficientFiniteDescentLisse
import all Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import Sheaf.Paper.QcqsLatticeTreeReconstruction
import Sheaf.Paper.PadicIntegersInvertEll

/-! # Constructible algebraic-closure modules after restriction to a finite subfield

Source: blueprint latest, coefficient finite descent and the finite-subextension colimit.
-/

@[expose] public section
set_option autoImplicit false
universe u vC uC
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar Mod.extendScalars
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.mapRegularIso Mod.mapRestrictedRegularIso CondensedRing.comapUpperStarIso
  CondensedRing.pullIso Functor.mapModComapIso lisseAlgClExtensionCompIso
  Mod.extendRestrictAdjunction Mod.comapComp Mod.comapCongr
  Mod.extendScalarsComp Mod.extendScalarsIsoOfEq
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction
  CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  CondensedRing.upperStarComp CondensedRing.upperStarId
  CondensedRing.comapOpenImmersionLowerShriekIso CondensedRing.comapLowerStarIso

private theorem finiteFree_comap
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {R S : C} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)]
    (a : R ⟶ S) [IsMonHom a] (n : ℕ)
    (h : Mod.IsFree R ((Mod.comap a).obj (Mod.regular S))) :
    Mod.IsFree R ((Mod.comap a).obj (Mod.finiteFree S n)) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := h
  let I := (i : Fin n) × Fin m
  refine ⟨Fintype.card I, ⟨?_⟩⟩
  exact (Mod.comap a).mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
    biproduct.mapIso (fun _ ↦ e) ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.mapIso (fun _ ↦ biproduct.isoCoproduct _) ≪≫
    sigmaSigmaIso (fun _ : Fin n ↦ Fin m) (fun _ _ ↦ Mod.regular R) ≪≫
    Sigma.whiskerEquiv (f := fun _ : I ↦ Mod.regular R)
      (g := fun _ : Fin (Fintype.card I) ↦ Mod.regular R)
      (Fintype.equivFin I) (fun _ ↦ Iso.refl (Mod.regular R)) ≪≫
    (biproduct.isoCoproduct _).symm

private theorem lisse_comap_finite
    (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (hEF : E ≤ F) (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj F) X))
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) M) :
    IsLisseCoefficientModule (Profinite.continuousMapRingObj E)
      ((Mod.comap (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEF) X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  let a := Profinite.padicSubfieldRingObjMap.{u} ℓ hEF
  let A := Profinite.continuousMapRingObj.{u} E
  let B := Profinite.continuousMapRingObj.{u} F
  obtain ⟨e⟩ := CondensedRing.point_finiteFree.{u} ℓ hEF
  have hp : Mod.IsFree A ((Mod.comap a).obj (Mod.regular B)) := ⟨_, ⟨e⟩⟩
  have hs : Mod.IsFree (condensedRingObj A (U.X i))
      ((Mod.comap (coefficientMap a (U.X i))).obj
        (Mod.regular (condensedRingObj B (U.X i)))) := by
    let G := upperStarFromPoint (U.X i)
    obtain ⟨n, ⟨en⟩⟩ := hp
    refine ⟨n, ⟨?_⟩⟩
    exact (Mod.mapRestrictedRegularIso G a).symm ≪≫
      (G.mapMod A).mapIso en ≪≫
      (G.mapMod A).mapBiproduct (fun _ : Fin n ↦ Mod.regular A) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.mapRegularIso G)
  obtain ⟨n, ⟨en⟩⟩ := hU i
  obtain ⟨m, ⟨em⟩⟩ := finiteFree_comap (coefficientMap a (U.X i)) n hs
  refine ⟨m, ⟨?_⟩⟩
  exact ((CondensedRing.comapUpperStarIso a (U.f i)).app M).symm ≪≫
    (Mod.comap (coefficientMap a (U.X i))).mapIso en ≪≫ em

private theorem lisse_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨en⟩⟩ := hU i
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨?_⟩⟩
  let G := upperStarFromPoint (U.X i)
  exact en ≪≫ ((G.mapMod Λ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.mapRegularIso G)).symm

private theorem lisse_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) : IsConstantModelConstructible Λ X M := by
  classical
  have hs (Y : Scheme.{u}) (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) (hN : IsLisseCoefficientModule Λ N) :
      IsFiniteConstantStratified Λ Y N := by
    exact ⟨Scheme.Stratification.trivial Y, fun _ ↦ lisse_model Λ Y _
      (lattice_lisse_pullback Λ (𝟙 Y) hN)⟩
  unfold IsConstantModelConstructible
  split
  · exact hs X M hM
  · intro U _
    exact hs U.toScheme _ (lattice_lisse_pullback Λ U.ι hM)

private theorem lisse_extend
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (hM : IsLisseCoefficientModule A M) :
    IsLisseCoefficientModule B ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨en⟩⟩ := hU i
  refine ⟨n, ⟨?_⟩⟩
  exact ((CondensedRing.pullIso a (U.f i)).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap a (U.X i))).mapIso en ≪≫
    (Mod.extendScalars (coefficientMap a (U.X i))).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (condensedRingObj A (U.X i))) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso _)

private theorem lisse_comap_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((Mod.comap (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).obj M) := by
  classical
  obtain ⟨F, N, hN, ⟨en⟩⟩ := exists_lisse_finiteCoefficient_model X ℓ M hM
  let H := Padic.finiteCoefficientCompositum ℓ (PadicAlgCl ℓ) E F
  have hEH : E ≤ H := by
    change E.val ≤ E.val ⊔ F.val
    exact le_sup_left
  have hFH : F ≤ H := by
    change F.val ≤ E.val ⊔ F.val
    exact le_sup_right
  let N' := (Mod.extendScalars (padicSubfieldRingObjMap X ℓ hFH)).obj N
  have hN' : IsLisseCoefficientModule (Profinite.continuousMapRingObj H) N' :=
    lisse_extend (Profinite.padicSubfieldRingObjMap ℓ hFH) X N hN
  let en' : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj N' ≅ M :=
    ((lisseAlgClExtensionCompIso X ℓ hFH).app N).symm ≪≫ en
  obtain ⟨I, b, hb, hflat, hunit⟩ :=
    CondensedRing.exists_condensedQbar_scalar_basis_sections.{u} ℓ H
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj H) X)
  let : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  let : HasCoproducts.{u + 1} C := fun J ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let a := coefficientMap (Profinite.padicSubfieldRingObjMap ℓ hEH) X
  let R : C ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X) := Mod.comap a
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
  have hn : Q (R.obj N') := ObjectProperty.le_weakSerreCoproductClosure _ _
    (lisse_constructible _ X _ (lisse_comap_finite ℓ hEH X N' hN'))
  have hcop : Q (R.obj (∐ fun _ : I ↦ N')) := by
    exact Q.prop_of_isColimit (isColimitOfPreserves R (coproductIsCoproduct (fun _ : I ↦ N')))
      (fun _ ↦ hn)
  have := hunit X N'
  let eh : (∐ fun _ : I ↦ N') ≅
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj N') :=
    asIso (Sigma.desc (fun i ↦
      (Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ H)).unit.app N' ≫
        (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ H)).map
          (Mod.qbar_scalarEndo (b X i)
            ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj N'))))
  exact Q.prop_of_iso
    (R.mapIso eh ≪≫ R.mapIso
      ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ H)).mapIso en') ≪≫
      (Mod.comapComp a (padicSubfieldRingObjToPadicAlgCl X ℓ H)).symm.app M ≪≫
      (Mod.comapCongr (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hEH)).app M) hcop

private theorem localization_shortExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (hc : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), S.ShortExact ∧ S.X₂ = M ∧
      S.X₁ = (CondensedRing.openImmersionLowerShriek Λ j).obj
        ((CondensedRing.upperStar Λ j).obj M) ∧
      S.X₃ = (CondensedRing.lowerStar Λ i).obj ((CondensedRing.upperStar Λ i).obj M) := by
  classical
  let jc := CondensedRing.upperStar Λ j
  let jp := CondensedRing.openImmersionLowerShriek Λ j
  let ic := CondensedRing.upperStar Λ i
  let ip := CondensedRing.lowerStar Λ i
  let aj := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j
  let ai := CondensedRing.upperStarLowerStarAdjunction Λ i
  have hu : IsIso aj.unit := CondensedRing.openUnitIsIso Λ j
  have hi : IsIso ai.counit := CondensedRing.moduleCounitOfAbelian Λ i
    (ProEtale.abelian_closed_support i j hc).1
  let α := aj.counit.app M
  let β := ai.unit.app M
  have hα : IsIso (jc.map α) := by
    have : IsIso (aj.unit.app (jc.obj M) ≫ jc.map α) := by
      change IsIso (aj.unit.app (jc.obj M) ≫ jc.map (aj.counit.app M))
      rw [aj.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (aj.unit.app (jc.obj M)) (jc.map α)
  have hβ : IsIso (ic.map β) := by
    have : IsIso (ic.map β ≫ ai.counit.app (ic.obj M)) := by
      change IsIso (ic.map (ai.unit.app M) ≫ ai.counit.app (ic.obj M))
      have ht : ic.map (ai.unit.app M) ≫ ai.counit.app (ic.obj M) = 𝟙 _ :=
        ai.left_triangle_components M
      rw [ht]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right (ic.map β) (ai.counit.app (ic.obj M))
  have hzj : IsZero (jc.obj (ip.obj (ic.obj M))) :=
    CondensedRing.openRestrictionPushforwardZero Λ i j hc _
  have hzi : IsZero (ic.obj (jp.obj (jc.obj M))) :=
    CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i
      (by rw [hc]; exact disjoint_compl_left) _
  have hw : α ≫ β = 0 := by
    apply (ai.homEquiv _ _).symm.injective
    exact hzi.eq_of_src _ _
  let S := ShortComplex.mk α β hw
  have hjoint := CondensedRing.isZero_of_isZero_upperStar_of_isCompl Λ i j
    (by rw [hc]; exact isCompl_compl)
  have hm : Mono α := by
    apply Preadditive.mono_of_isZero_kernel
    apply hjoint
    · exact (IsZero.of_mono (kernel.ι (ic.map α)) hzi).of_iso
        (PreservesKernel.iso ic α)
    · exact (isZero_kernel_of_mono (jc.map α)).of_iso (PreservesKernel.iso jc α)
  have he : Epi β := by
    apply Preadditive.epi_of_isZero_cokernel
    apply hjoint
    · exact (isZero_cokernel_of_epi (ic.map β)).of_iso (PreservesCokernel.iso ic β)
    · exact (IsZero.of_epi (cokernel.π (jc.map β)) hzj).of_iso
        (PreservesCokernel.iso jc β)
  have hs : S.Exact := by
    apply S.exact_iff_isZero_homology.mpr
    apply hjoint
    · have hh : (S.map ic).Exact := (ShortComplex.exact_iff_mono _
        (hzi.eq_of_src _ _)).mpr (by change Mono (ic.map β); infer_instance)
      exact ((S.map ic).exact_iff_isZero_homology.mp hh).of_iso
        (S.mapHomologyIso ic).symm
    · have hh : (S.map jc).Exact := (ShortComplex.exact_iff_epi _
        (hzj.eq_of_tgt _ _)).mpr (by change Epi (jc.map α); infer_instance)
      exact ((S.map jc).exact_iff_isZero_homology.mp hh).of_iso
        (S.mapHomologyIso jc).symm
  exact ⟨S, { exact := hs, mono_f := hm, epi_g := he }, rfl, rfl, rfl⟩

private theorem closure_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) F]
    (h : ∀ M, P M → Q (F.obj M)) (M : C)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1} P M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1} Q (F.obj M) := by
  let T := ObjectProperty.weakSerreCoproductClosure.{u + 1} Q
  exact hM (T.inverseImage F)
    (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _ (h N hN))
    inferInstance inferInstance inferInstance inferInstance (fun _ ↦ inferInstance)

private theorem field_flat
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) W)) := by
  exact (padicIntegers_invertEll W ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2

private theorem field_reconstruction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) (t : QcqsOpenClosedTree X)
    (hflat : ∀ (W : Scheme.{u}) (_p : t.Path W) (_k : Unit),
      PreservesFiniteLimits (Mod.extendScalars
        (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) W))) :
    ∀ (W : Scheme.{u}) (p : t.Path W),
      LatticeTree.PreservesModelsAndFlat (Profinite.continuousMapRingObj E) p := by
  intro W p
  exact (((LatticeTree.qcqs_lattice_tree_reconstruction ℓ).1 E X t hflat).1 W p).1

private theorem branch_model_open
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (hc : Set.range j = (Set.range i)ᶜ)
    (h : LatticeTree.PreservesModelsAndFlat A
      (QcqsOpenClosedTree.Path.openBranch j i hc (.leaf U) (.leaf Z) (.root _)))
    (M) (hM : IsConstantModelConstructible A U M) :
    IsConstantModelConstructible A X ((CondensedRing.openImmersionLowerShriek A j).obj M) := by
  exact (h M).1 hM

private theorem branch_model_closed
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (hc : Set.range j = (Set.range i)ᶜ)
    (h : LatticeTree.PreservesModelsAndFlat A
      (QcqsOpenClosedTree.Path.closedBranch j i hc (.leaf U) (.leaf Z) (.root _)))
    (M) (hM : IsConstantModelConstructible A Z M) :
    IsConstantModelConstructible A X ((CondensedRing.lowerStar A i).obj M) := by
  exact (h M).1 hM

private theorem branch_models
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    (h : ∀ (X : Scheme.{u}) (t : QcqsOpenClosedTree X) (W : Scheme.{u}) (p : t.Path W),
      LatticeTree.PreservesModelsAndFlat A p)
    {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (hc : Set.range j = (Set.range i)ᶜ) :
    (∀ M, IsConstantModelConstructible A U M →
      IsConstantModelConstructible A X ((CondensedRing.openImmersionLowerShriek A j).obj M)) ∧
    (∀ M, IsConstantModelConstructible A Z M →
      IsConstantModelConstructible A X ((CondensedRing.lowerStar A i).obj M)) := by
  let t := QcqsOpenClosedTree.split j i hc (.leaf U) (.leaf Z)
  exact ⟨branch_model_open A j i hc
      (h X t U (.openBranch j i hc (.leaf U) (.leaf Z) (.root _))),
    branch_model_closed A j i hc
      (h X t Z (.closedBranch j i hc (.leaf U) (.leaf Z) (.root _)))⟩

private theorem closed_exact_adjoint
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (hc : Set.range j = (Set.range i)ᶜ) :
    PreservesFiniteColimits (CondensedRing.lowerStar A i) ∧
      Nonempty (CondensedRing.lowerStar A i).IsLeftAdjoint := by
  let ic := CondensedRing.upperStar A i
  let ip := CondensedRing.lowerStar A i
  let jc := CondensedRing.upperStar A j
  let jp := CondensedRing.lowerStar A j
  let ai := CondensedRing.upperStarLowerStarAdjunction A i
  let aj := CondensedRing.upperStarLowerStarAdjunction A j
  have hi : IsIso ai.counit := CondensedRing.moduleCounitOfAbelian A i
    (ProEtale.abelian_closed_support i j hc).1
  have hzero (N) : IsZero (jc.obj (ip.obj N)) :=
    CondensedRing.openRestrictionPushforwardZero A i j hc N
  have hsupport (N) (hN : IsZero (jc.obj N)) : IsIso (ai.unit.app N) := by
    apply CondensedRing.moduleUnitOfAbelian A i N
    apply (ProEtale.abelian_closed_support i j hc).2
    exact ((Mod.forget _).map_isZero hN).of_iso
      ((profinitePointModuleForgetPullbackIso A j).app N).symm
  have hjoint (N) (hiN : IsZero (ic.obj N)) (hjN : IsZero (jc.obj N)) :
      IsZero N := by
    have := hsupport N hjN
    exact (ip.map_isZero hiN).of_iso (asIso (ai.unit.app N))
  have hclosed : PreservesFiniteColimits ip :=
    CondensedRing.exactClosedOfDetection ic ip jc ai hzero hjoint
  have hj : IsIso aj.counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit
      ⟨CondensedRing.openImmersionLowerShriekUpperStarAdjunction A j, aj⟩).1
      (CondensedRing.openUnitIsIso A j)
  have ff := ai.fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  obtain ⟨ir, ⟨ash⟩⟩ :=
    CondensedRing.exceptionalAdjointOfSupport ic ip jc jp ai aj hzero hsupport
  exact ⟨hclosed, ⟨ash.isLeftAdjoint⟩⟩

private theorem open_closed_closure
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (hc : Set.range j = (Set.range i)ᶜ)
    (hju : ∀ M, IsConstantModelConstructible A U M →
      IsConstantModelConstructible A X ((CondensedRing.openImmersionLowerShriek A j).obj M))
    (hiz : ∀ M, IsConstantModelConstructible A Z M →
      IsConstantModelConstructible A X ((CondensedRing.lowerStar A i).obj M)) :
    (∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A U) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A X)
        ((CondensedRing.openImmersionLowerShriek A j).obj M)) ∧
    (∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A Z) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A X)
        ((CondensedRing.lowerStar A i).obj M)) := by
  classical
  obtain ⟨hclosed, ⟨hleft⟩⟩ := closed_exact_adjoint A j i hc
  let := hclosed
  let := hleft
  have : PreservesColimitsOfSize.{u + 1, u + 1} (CondensedRing.lowerStar A i) :=
    inferInstance
  constructor
  · exact closure_map (IsConstantModelConstructible A U)
      (IsConstantModelConstructible A X) (CondensedRing.openImmersionLowerShriek A j) hju
  · exact closure_map (IsConstantModelConstructible A Z)
      (IsConstantModelConstructible A X) (CondensedRing.lowerStar A i) hiz

private theorem reconstruction_closure
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    (h : ∀ (X : Scheme.{u}) (t : QcqsOpenClosedTree X) (W : Scheme.{u}) (p : t.Path W),
      LatticeTree.PreservesModelsAndFlat A p)
    {X U Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] [QuasiCompact i] (hc : Set.range j = (Set.range i)ᶜ) :
    (∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A U) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A X)
        ((CondensedRing.openImmersionLowerShriek A j).obj M)) ∧
    (∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A Z) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A X)
        ((CondensedRing.lowerStar A i).obj M)) := by
  obtain ⟨hju, hiz⟩ := branch_models A h j i hc
  exact open_closed_closure A j i hc hju hiz

private theorem comap_extension_closure
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] {T U Z : Scheme.{u}}
    (j : U ⟶ T) (i : Z ⟶ T) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (hc : Set.range j = (Set.range i)ᶜ)
    (hju : ∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A U) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A T)
        ((CondensedRing.openImmersionLowerShriek A j).obj M))
    (hiz : ∀ M, ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible A Z) M →
      ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A T)
        ((CondensedRing.lowerStar A i).obj M))
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj B T))
    (hu : ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A U)
      ((Mod.comap (coefficientMap a U)).obj ((CondensedRing.upperStar B j).obj N)))
    (hz : ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A Z)
      ((Mod.comap (coefficientMap a Z)).obj ((CondensedRing.upperStar B i).obj N))) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A T)
      ((Mod.comap (coefficientMap a T)).obj N) := by
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible A T)
  obtain ⟨s, hs, hs₂, hs₁, hs₃⟩ := localization_shortExact B j i hc N
  have h₁ : Q ((Mod.comap (coefficientMap a T)).obj s.X₁) := by
    rw [hs₁]
    exact Q.prop_of_iso ((CondensedRing.comapOpenImmersionLowerShriekIso a j).app _).symm
      (hju _ hu)
  have h₃ : Q ((Mod.comap (coefficientMap a T)).obj s.X₃) := by
    rw [hs₃]
    exact Q.prop_of_iso ((CondensedRing.comapLowerStarIso a i).app _).symm (hiz _ hz)
  have := hs.mono_f
  have := hs.epi_g
  have hm := Q.prop_X₂_of_shortExact (hs.map (Mod.comap (coefficientMap a T))) h₁ h₃
  simpa only [ShortComplex.map_X₂, hs₂] using hm

private theorem latticeTree_comap_closure
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (hleaf : ∀ (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
      (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj B W)),
      IsLisseCoefficientModule B N →
      ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A W)
        ((Mod.comap (coefficientMap a W)).obj N))
    (hbranch : ∀ (W : Scheme.{u}) (t : QcqsOpenClosedTree W) (V : Scheme.{u}) (p : t.Path V),
      LatticeTree.PreservesModelsAndFlat A p)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (S : Scheme.Stratification X) (tree : LatticeRefinementTree X X (𝟙 X))
    (ht : tree.AllLeaves (IsConstructibleLatticeLeaf B M S)) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A X)
      ((Mod.comap (coefficientMap a X)).obj M) := by
  classical
  have htree : ∀ (T : Scheme.{u}) (t : T ⟶ X)
      (tr : LatticeRefinementTree X T t),
      tr.AllLeaves (IsConstructibleLatticeLeaf B M S) →
      ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible A T)
        ((Mod.comap (coefficientMap a T)).obj ((CondensedRing.upperStar B t).obj M)) := by
    intro T t tr
    induction tr with
    | @tip T t hcompact hqs himm =>
      intro ht
      let := hcompact
      let := hqs
      by_cases hn : Nonempty T
      · exact hleaf T _ (ht hn).2
      · have : IsEmpty T := not_nonempty_iff.mp hn
        exact ObjectProperty.prop_of_isZero _ (lattice_module_empty A _)
    | @node T U Z t j i hcompact hqs himm hj hi hjqc hiqc hcover hd ha
        left right ihl ihr =>
      intro ht
      let := hcompact
      let := hqs
      let := himm
      let := hj
      let := hi
      let := hjqc
      let := hiqc
      have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
      have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
      have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated j
      have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
      have hc : Set.range j = (Set.range i)ᶜ := by
        exact eq_compl_iff_isCompl.mpr ⟨hd, codisjoint_iff.mpr hcover⟩
      let N := (CondensedRing.upperStar B t).obj M
      have hu : ObjectProperty.weakSerreCoproductClosure.{u + 1}
          (IsConstantModelConstructible A U)
          ((Mod.comap (coefficientMap a U)).obj ((CondensedRing.upperStar B j).obj N)) :=
        ObjectProperty.prop_of_iso _ ((Mod.comap (coefficientMap a U)).mapIso
          ((CondensedRing.upperStarComp B j t).app M)) (ihl ht.1)
      have hz : ObjectProperty.weakSerreCoproductClosure.{u + 1}
          (IsConstantModelConstructible A Z)
          ((Mod.comap (coefficientMap a Z)).obj ((CondensedRing.upperStar B i).obj N)) :=
        ObjectProperty.prop_of_iso _ ((Mod.comap (coefficientMap a Z)).mapIso
          ((CondensedRing.upperStarComp B i t).app M)) (ihr ht.2)
      obtain ⟨hju, hiz⟩ := reconstruction_closure A hbranch j i hc
      exact comap_extension_closure A B a j i hc hju hiz N hu hz
  have hm := htree X (𝟙 X) tree ht
  exact ObjectProperty.prop_of_iso _ ((Mod.comap (coefficientMap a X)).mapIso
    ((CondensedRing.upperStarId B X).app M)) hm

private theorem constructible_comap_closure
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((Mod.comap (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).obj M) := by
  classical
  let A := Profinite.continuousMapRingObj.{u} E
  let B := Profinite.padicAlgClRingObj.{u} ℓ
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E
  obtain ⟨S, hS, tree, ht⟩ :=
    ((qcqs_constructible_integral_lattice_tree ℓ E X).2 M hM).1
  exact latticeTree_comap_closure A B a (fun W _ _ N ↦ lisse_comap_closure ℓ E W N)
    (fun W t ↦ field_reconstruction ℓ E W t (fun V _ _ ↦ field_flat ℓ E V)) X M S tree ht

/-- Restricting a finite constant-model constructible algebraic-closure module to a fixed
finite coefficient subfield puts it in the constructibly generated weak Serre coproduct class.

Source: blueprint latest, `sk-lem-coefficient-finite-descent-lisse` and
`sk-prop-sfb-qlbar-colimit-x`; finite-subextension restriction argument.
(blueprint: lem-sfb-padic-alg-cl-constructible-scalar-restriction)

Proof: Refine the constructible stratification to a finite qcqs open-closed tree using
qcqs_constructible_integral_lattice_tree. At a nonempty leaf its restriction is lisse.
Descend that lisse module to a finite coefficient field F and enlarge F to the compositum
with E. A finite field basis shows that restriction from F to E preserves lisse finite
free local models, hence gives constructible E-modules. The algebraic closure coefficient
basis identifies restriction of the scalar extension of this model with a coproduct of
copies of the model. Restriction from F to E preserves that coproduct, putting the leaf
restriction in the weak Serre coproduct class. Empty leaves give zero objects.
The reconstruction theorem supplies preservation of finite constant-model constructibility
by each open and closed branch functor. Open extension is exact and colimit preserving;
closed direct image is exact and has the exceptional right adjoint from recollement, hence
preserves coproducts. Minimality transports the weak Serre coproduct classes along these
functors. The localization short exact sequence, proved from the open unit, closed counit,
disjoint vanishing and joint detection, reconstructs the root by extensions. All these
functors commute with coefficient restriction. Finally transport through the given
coefficient isomorphism. The indices of all coproducts lie in Type (u+1).
-/
theorem constantModelConstructible_padicAlgCl_comap
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((Mod.comap (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E ≫ e.inv.hom) X)).obj M) := by
  classical
  have hM' := constructible_comap e.inv.hom X M hM
  have hm := constructible_comap_closure ℓ E X _ hM'
  exact ObjectProperty.prop_of_iso _
    ((Mod.comapComp (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)
      (coefficientMap e.inv.hom X)).symm.app M ≪≫
      (Mod.comapCongr (coefficientMap_comp _ _ X).symm).app M) hm

end AlgebraicGeometry.ProEtale
