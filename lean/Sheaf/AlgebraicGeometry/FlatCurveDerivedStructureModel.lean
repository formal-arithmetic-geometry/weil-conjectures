/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NG and J6
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties
import Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange
import Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent
import Sheaf.AlgebraicGeometry.DerivedResidueUnitBetti
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.NoetherianProperBoundedCoherentImage
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor
import Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
import WeilConjectures.AlgebraicGeometry.PerfectLocalizingIsoLocus
import WeilConjectures.AlgebraicGeometry.OpenPerfectModelTransport
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # The two-degree derived structure model of a proper flat curve family

Source: Stacks Project, Tag 0GKA, proof of lemma-genus-in-nodal-family-of-curves;
Tags 0B91, 0E62, 02UZ and 0BCD
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model)

The hypotheses used from the nodal setting are stated explicitly: proper flat finite
presentation, fibre dimension at most one, and fibrewise constant global functions.
The auxiliary constructions below merely name the structure complex, its unit, its
first cohomology, and its canonical base-change arrow, all using the shared library.
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a chosen localization along an exact equivalence of abelian categories.
This is the localization construction in `SchemeIsoDerivedLocalizations`, specialized
to the module-sheaf universe; its helper there is private. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩


private theorem strictlyPerfect_single_restricted_unit (S : Scheme.{u}) (U : S.Opens) :
    Scheme.IsStrictlyPerfect S U
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))) := by
  classical
  let R := (moduleRings S.toRingedSpace).over U
  let M := (SheafOfModules.overFunctor.{u}
    (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)
  let A := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj M
  refine ⟨⟨0, 0, fun n hn ↦ ?_⟩, ?_⟩
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : A.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 M ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (A.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using (hz.eq_of_src (0 : A.X n ⟶ A.X n) (𝟙 _))⟩


private theorem two_degree_split {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    (P : CochainComplex C ℤ)
    (hz : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i))
    (hd : ∀ i j : ℤ, P.d i j = 0) :
    Nonempty (P ≅ (CochainComplex.singleFunctor C 0).obj (P.X 0) ⊞
      (CochainComplex.singleFunctor C 1).obj (P.X 1)) := by
  classical
  let p (n : ℤ) := HomologicalComplex.mkHomToSingle (𝟙 (P.X n))
    (fun i _ ↦ by rw [hd]; simp)
  let j (n : ℤ) := HomologicalComplex.mkHomFromSingle (𝟙 (P.X n))
    (fun i _ ↦ by rw [hd]; simp)
  have hsame (n : ℤ) : j n ≫ p n = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = n
    · subst i
      simp [p, j]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n (P.X n) i hi).eq_of_src _ _
  have hcross (n m : ℤ) (hnm : n ≠ m) : j n ≫ p m = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = n
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) m (P.X m) i
        (by simpa [hi] using hnm)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n (P.X n) i hi).eq_of_src _ _
  refine ⟨⟨biprod.lift (p 0) (p 1), biprod.desc (j 0) (j 1), ?_, ?_⟩⟩
  · rw [biprod.lift_desc]
    ext i
    by_cases h0 : i = 0
    · subst i
      simp [p, j, HomologicalComplex.mkHomToSingle,
        HomologicalComplex.mkHomFromSingle]
    · by_cases h1 : i = 1
      · subst i
        simp [p, j, HomologicalComplex.mkHomToSingle,
          HomologicalComplex.mkHomFromSingle]
      · exact (hz i h0 h1).eq_of_src _ _
  · apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp [Category.assoc, hsame, hcross]
    all_goals rfl

private noncomputable def zero_differential_homology_iso
    {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    (P : CochainComplex C ℤ) (hd : ∀ i j : ℤ, P.d i j = 0) (i : ℤ) :
    P.homology i ≅ P.X i :=
  (ShortComplex.HomologyData.ofZeros (P.sc i) (hd _ _) (hd _ _)).left.homologyIso

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option maxHeartbeats 1000000 in
-- The comparison of the two open-restriction functors requires extra elaboration steps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem noetherian_single_perfect
    {Y T : Scheme.{u}} [IsNoetherian T] (p : Y ⟶ T)
    [IsProper p] [LocallyOfFinitePresentation p]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : M.IsFlatOver p) :
    T.IsPerfect ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)) := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  have hz (i : ℤ) (hi : i < 0 ∨ 0 < i) : IsZero
      ((DerivedCategory.homologyFunctor _ i).obj A) := by
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff A 0).mp inferInstance i hi
    · exact (DerivedCategory.isLE_iff A 0).mp inferInstance i hi
  have hc (i : ℤ) : RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor _ i).obj A) := by
    have hcoh : RingedSpace.IsCoherent Y.toRingedSpace M :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y M).2
        ⟨inferInstance, inferInstance⟩
    have hiso := (RingedSpace.coherent_kernel_cokernel_sum Y.toRingedSpace).2.2.2.2
    by_cases hi : i = 0
    · subst i
      exact hiso _ _ ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).app M).symm hcoh
    · exact hiso _ _ (hz i (by omega)).isoZero.symm
        (RingedSpace.coherent_kernel_cokernel_sum Y.toRingedSpace).2.2.2.1
  obtain ⟨hb, hc⟩ := Scheme.noetherian_proper_directImage_bounded_coherent p A
    ⟨0, 0, hz⟩ hc
  let K := (schemeDerivedDirectImage p).obj A
  have hpc := Scheme.isPseudoCoherent_of_bounded_coherent T K hb hc
  apply Scheme.isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension T K hpc
  intro t
  obtain ⟨U, hU, ht, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := T) (x := t) (U := ⊤) (by trivial)
  obtain ⟨a, b, hab, htor⟩ := properFlat_single_local_hasFiniteTorDimension p M hM U hU
  obtain ⟨er⟩ := open_pullback_restriction_iso T U K
  refine ⟨U, ht, a, b, hab, ?_⟩
  intro G i hi
  obtain ⟨P, hP, ⟨e⟩, hz⟩ := htor G i hi
  exact ⟨P, hP, ⟨e ≪≫ er⟩, hz⟩

set_option maxHeartbeats 1200000 in
-- Elaborating canonical base-change composites compares several chosen localizations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A proper finitely presented morphism sends a relatively flat finitely presented
module in degree zero to a perfect complex, over an arbitrary base.
Source: Stacks Project, Tags 0A1H, 0B91, 08E2 and 08CQ.
The argument uses the independent global localizations supplied by this module.

Proof: Descend the proper finitely presented morphism and the finitely presented
relatively flat module, near a chosen base point, to a Noetherian stage. At that stage,
proper coherence gives bounded coherent cohomology. This is pseudo-coherent. The bounded
flat Cech model gives locally finite Tor dimension, so the pseudo-coherent finite-Tor
criterion proves perfectness. Canonical derived base change for a relatively flat module
identifies its pullback to the original neighbourhood with the original direct image
restricted there. Pullback preserves perfectness. Identify the neighbourhood with its
open image in the base and transport the strictly perfect models along that open
immersion. This supplies a model near every point. The empty base is vacuous; zero
modules and empty sources satisfy the same argument. -/
private theorem proper_relativelyFlat_single_isPerfect
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    S.IsPerfect ((schemeDerivedDirectImage f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) := by
  classical
  let K := (schemeDerivedDirectImage f).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  intro s
  let top : S.Opens := ⊤
  let x : top.toScheme := ⟨s, by trivial⟩
  obtain ⟨V, hx, B, Y, W, _, _, hB, hY, p, hp, M, hfp, hflat,
      g, q, hy, ⟨eTensor⟩⟩ := properFlat_single_noetherian_descent f F hF top x
  have := hB
  have := hY
  have := hp
  have := hfp
  have : LocallyOfFinitePresentation p := inferInstance
  let u : V.toScheme ⟶ S := V.ι ≫ top.ι
  let fV := pullback.snd f u
  let a := pullback.fst f u
  let O := top.ι ''ᵁ V
  let c := top.ι.isoImage V
  let (U : W.toScheme.Opens) : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over U)) :=
    Classical.choice (hasDerivedCategory_of_equivalence
      (C := SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U))
  let (U : V.toScheme.Opens) : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over U)) :=
    Classical.choice (hasDerivedCategory_of_equivalence
      (C := SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U))
  let (U : O.toScheme.Opens) : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings O.toScheme.toRingedSpace).over U)) :=
    Classical.choice (hasDerivedCategory_of_equivalence
      (C := SheafOfModules.{u} ((moduleRings O.toScheme.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U))
  let KP := (schemeDerivedDirectImage p).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  have hP := noetherian_single_perfect p M hflat
  have hg := derivedPullback_preserve_perfect g KP hP
  have : (Scheme.Modules.tensorPullback q).IsLeftAdjoint :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction q).some.isLeftAdjoint
  have : (Scheme.Modules.tensorPullback a).IsLeftAdjoint :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction a).some.isLeftAdjoint
  have : (Scheme.Modules.tensorPullback q).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (Scheme.Modules.tensorPullback q)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (Scheme.Modules.tensorPullback a).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (Scheme.Modules.tensorPullback a)
    exact Functor.additive_of_preservesBinaryBiproducts _
  obtain ⟨cq, _, hq⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    p g q fV hy M hflat
  obtain ⟨ca, _, ha⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    f u a fV (IsPullback.of_hasPullback f u) F hF
  let eq := asIso (schemeDerivedBaseChangeMap p fV g q hy.w
    ((DerivedCategory.singleFunctor _ 0).obj M) ≫ (schemeDerivedDirectImage fV).map cq)
  let ea := asIso (schemeDerivedBaseChangeMap f fV u a pullback.condition
    ((DerivedCategory.singleFunctor _ 0).obj F) ≫ (schemeDerivedDirectImage fV).map ca)
  let em := (schemeDerivedDirectImage fV).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso eTensor)
  let eV : (derivedPullback u).obj K ≅ (derivedPullback g).obj KP :=
    ea ≪≫ em.symm ≪≫ eq.symm
  have hV := CategoryTheory.ShiftSaturated.perfect_iso V.toScheme eV.symm hg
  have hO := derivedPullback_preserve_perfect c.inv ((derivedPullback u).obj K) hV
  have heq : c.inv ≫ u = O.ι := top.ι.isoImage_inv_ι V
  let eO : (derivedPullback c.inv).obj ((derivedPullback u).obj K) ≅
      (derivedPullback O.ι).obj K :=
    (recordedDerivedPullbackComposition c.inv u).app K ≪≫
      eqToIso (congrArg (fun b : O.toScheme ⟶ S ↦ (derivedPullback b).obj K) heq)
  have hO' := CategoryTheory.ShiftSaturated.perfect_iso O.toScheme eO hO
  obtain ⟨er⟩ := open_pullback_restriction_iso S O K
  exact Scheme.local_perfect_of_openRestriction_iso S O K
    ((derivedPullback O.ι).obj K) hO' er s ⟨x, hx, rfl⟩

/-- The abbreviation `K = Rf_*(O_X[0])` in the structure-model statement.
Source: Stacks, Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
abbrev derivedStructureImage {X S : Scheme.{u}} (f : X ⟶ S) :
    schemeDerivedCategory S :=
  (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (SheafOfModules.unit X.ringCatSheaf))

/-- The derived structural unit: the ordinary structural map in degree zero followed
by the canonical right-derived unit. Its H0 is structural function pullback by
`Scheme.Modules.canonicalDirectImageH0Unit`.
Source: Stacks, Tag 0E62, proof, and Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
def derivedStructureUnit {X S : Scheme.{u}} (f : X ⟶ S) :
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ derivedStructureImage f :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    Scheme.Modules.canonicalSingleDirectImageMap f (SheafOfModules.unit X.ringCatSheaf)

/-- The abbreviation `E = H^1(K)` in the structure-model statement.
Source: Stacks, Tag 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
abbrev derivedStructureH1 {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj (derivedStructureImage f)

/-- Canonical structure-sheaf base change. The pinned tensor-pullback counit in
`canonicalSinglePullbackMap` is transported through the unique adjunction-preserving
tensor-to-ordinary pullback isomorphism. Composing with the ordinary adjoint structural
map identifies the pulled-back unit with the unit on the fibre product. Thus this is
the canonical module base-change arrow with target `Rf_{T,*}(O_{X_T}[0])`.
Source: Stacks, Tags 08HY, 0096, 0B91 and 0GKA, proof
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model). -/
def derivedStructureBaseChangeMap {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    (derivedPullback g).obj (derivedStructureImage f) ⟶
      derivedStructureImage (pullback.snd f g) :=
  schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map
      (Scheme.Modules.canonicalSinglePullbackMap (pullback.fst f g)
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit (pullback.fst f g).toRingCatSheafHom))

set_option maxHeartbeats 1200000 in
-- The affine chain representative compares several derived localization functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The structure complex of a proper flat finitely presented family with fibres of
dimension at most one and only constant global functions is locally `O_S[0] ⊕ E[-1]`,
with `E` quasi-coherent finite locally free. The structural H0 unit and every canonical
derived base-change map are invertible, and all other cohomology sheaves vanish.
Source: Stacks, Tag 0GKA, proof, using only the explicitly stated fibre assumptions
(blueprint: lem-weil-pbc-flat-curve-derived-structure-model)

Proof:
1. Descend O_X and f locally to a Noetherian stage. Proper coherence gives a bounded
   coherent direct image there, hence a pseudo-coherent object; the bounded flat Cech
   model gives locally finite Tor dimension. The finite-Tor criterion gives perfectness.
   Canonical relatively flat base change and preservation of perfectness under pullback
   transport the models to S. The flat invertible-module comparison proves invertibility
   of the displayed canonical base-change map. Perfectness gives quasi-coherent homology.
2. The explicit canonical structural-unit properties give negative residue vanishing and
   the residue H0 unit isomorphism. The degree-zero fibre criterion then proves that the
   actual H0 structural unit is invertible.
3. Each fibre is Noetherian, being proper over a field. Grothendieck vanishing kills its
   structure cohomology above degree one. The derived single-object homology comparison
   and canonical base change give residue vanishing above one. Thus the only possibly
   nonzero residue Betti numbers are zero and one, and the degree-zero rank is one.
4. Apply the finite-free residue model directly to K. It has terms only in degrees zero
   and one. Represent the structural unit by a chain map on the affine neighbourhood;
   the residue-H0 stalk criterion makes its degree-zero component invertible everywhere
   there. The chain-map equation kills the only possible differential. Split the two
   singles by their inclusions and projections. Homology identifies the second term
   with restricted E, proving local finite freeness and the requested splitting. The
   other cohomology sheaves vanish on these neighbourhoods, hence globally. -/
theorem flatCurve_derivedStructure_model
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (hconstants : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    S.IsPerfect (derivedStructureImage f) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map (derivedStructureUnit f)) ∧
      (derivedStructureH1 f).IsQuasicoherent ∧
      (derivedStructureH1 f).IsFiniteLocallyFree ∧
      (∀ s : S, ∃ U : S.Opens, s ∈ U ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj (derivedStructureImage f) ≅
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
                (SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)) ⊞
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
                ((derivedStructureH1 f).over U))⟦(-1 : ℤ)⟧)) ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj (derivedStructureImage f))) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (derivedStructureBaseChangeMap f g)) := by
  classical
  let (Y : Scheme.{u}) : Abelian
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let (U : S.Opens) : Abelian
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance
  let (U : S.Opens) : HasColimits
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance
  let OX : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    SheafOfModules.unit X.ringCatSheaf
  have : SheafOfModules.IsInvertible.{u, u, u} OX :=
    SheafOfModules.instIsInvertibleUnit (R := X.ringCatSheaf)
  have hperfect : S.IsPerfect (derivedStructureImage f) :=
    proper_relativelyFlat_single_isPerfect f OX
      (Scheme.Modules.isFlatOver_of_isInvertible f OX)
  have hqc := schemeDerivedQCohProperty_of_isPerfect S _ hperfect
  obtain ⟨hnegative, hfibre⟩ := flat_derived_structure_unit_properties f
  have hzero : ∀ s : S, IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map (derivedStructureUnit f))) :=
    fun s ↦ hfibre s (hconstants s)
  have hunit : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
        (derivedStructureUnit f)) := by
    let (U : S.Opens) (V : U.toScheme.Opens) : HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V)) :=
      Classical.choice (hasDerivedCategory_of_equivalence
        (C := SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V))
    exact (perfect_degreeZero_fibre_criterion S _ hqc hperfect _ hzero hnegative).1
  have hbase (T : Scheme.{u}) (g : T ⟶ S) :
      IsIso (derivedStructureBaseChangeMap f g) := by
    have : IsIso (Scheme.Modules.canonicalSinglePullbackMap (pullback.fst f g) OX) :=
      Scheme.Modules.isIso_canonicalSinglePullbackMap (pullback.fst f g) OX
    have : IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj OX)) :=
      Scheme.Modules.isIso_derivedBaseChange_of_flat_invertible
        f g (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g) OX
    dsimp only [derivedStructureBaseChangeMap]
    infer_instance
  have hpositive : ∀ (s : S) (i : ℤ), 1 < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj (derivedStructureImage f))) := by
    intro s i hi
    let f' := f.fiberToSpecResidueField s
    have : IsProper f' := by dsimp [f', Scheme.Hom.fiberToSpecResidueField]; infer_instance
    have : LocallyOfFinitePresentation f' := by
      dsimp [f', Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    let O : (f.fiber s).Modules := SheafOfModules.unit (f.fiber s).ringCatSheaf
    have : O.IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit (R := (f.fiber s).ringCatSheaf)
    have : HasInjectiveResolutions (f.fiber s).Modules :=
      inferInstanceAs (HasInjectiveResolutions
        (SheafOfModules.{u} (moduleRings (f.fiber s).toRingedSpace)))
    have : IsLocallyNoetherian (f.fiber s) := LocallyOfFiniteType.isLocallyNoetherian f'
    have : CompactSpace (f.fiber s) := QuasiCompact.compactSpace_of_compactSpace f'
    have : IsNoetherian (f.fiber s) := ⟨⟩
    have hq : topologicalKrullDim (f.fiber s) < (i.toNat : WithBot ℕ∞) := by
      apply (hdim s).trans_lt
      exact_mod_cast (show 1 < i.toNat by omega)
    have : Subsingleton (O.H i.toNat) :=
      Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt O hq
    obtain ⟨e, _⟩ := Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H f' i.toNat
    have hz : IsZero ((Scheme.Modules.higherDirectImage f' i.toNat).obj O) := by
      rw [Scheme.Modules.isZero_iff_forall_subsingleton]
      intro U
      rcases U.eq_bot_or_top with rfl | rfl
      · exact AddCommGrpCat.isZero_iff_subsingleton.mp
          (TopCat.Sheaf.isTerminalOfEmpty ((SheafOfModules.toSheaf _).obj
            ((Scheme.Modules.higherDirectImage f' i.toNat).obj O))).isZero
      · exact ⟨fun x y ↦ (e O).injective (Subsingleton.elim _ _)⟩
    let ec := Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom) O i.toNat
    have hz' : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
          (derivedStructureImage f')) := by
      have hh := hz.of_iso ec
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ i)] using hh
    have := hbase (Spec (S.residueField s)) (S.fromSpecResidueField s)
    exact hz'.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (asIso (derivedStructureBaseChangeMap f (S.fromSpecResidueField s))))
  have hmodel (s : S) : ∃ U : S.Opens, s ∈ U ∧
      ∃ P : CochainComplex
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        Scheme.IsStrictlyPerfect S U P ∧
        (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
        (∀ i j : ℤ, P.d i j = 0) ∧
        Nonempty (P.X 0 ≅ SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)) ∧
        (∃ n : ℕ, Nonempty (P.X 1 ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin n)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj (derivedStructureImage f) ≅
            DerivedCategory.Q.obj P) := by
    have hb (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ 1) :
        Scheme.derivedFiberBetti S (derivedStructureImage f) i s = 0 := by
      let F := SheafOfModules.evaluation
        (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤)
      have : F.Additive := ⟨by intros; rfl⟩
      have hz : IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
            ((derivedPullback (S.fromSpecResidueField s)).obj (derivedStructureImage f))) := by
        by_cases hn : i < 0
        · exact hnegative s i hn
        · exact hpositive s i (by omega)
      have hs := ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero hz)
      let : Subsingleton (Scheme.derivedFiberCohomology S (derivedStructureImage f) i s) := hs
      exact Module.finrank_zero_of_subsingleton
    have hrank := Scheme.derivedFiberBetti_zero_eq_one_of_unit_iso
      S (derivedStructureImage f) (derivedStructureUnit f) s (hzero s)
    obtain ⟨_, _, U, hs, hU, P, hPb, hPf, ⟨e⟩⟩ :=
      Scheme.exists_finiteFreeResidueModel S (derivedStructureImage f) hperfect s
    have hP : Scheme.IsStrictlyPerfect S U P := by
      refine ⟨hPb, fun i ↦ ?_⟩
      obtain ⟨ei⟩ := hPf i
      exact ⟨Scheme.derivedFiberBetti S (derivedStructureImage f) i s,
        ei.hom, ei.inv, ei.hom_inv_id⟩
    have hPn (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ 1) : IsZero (P.X i) := by
      obtain ⟨ei⟩ := hPf i
      apply IsZero.of_iso _ ei
      rw [hb i hi hi', IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext j
      exact Fin.elim0 j.down
    have hP0 : Nonempty (P.X 0 ≅ SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))) := by
      simpa only [hrank] using hPf 0
    let r := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
    let M := SheafOfModules.unit S.ringCatSheaf
    let A := (CochainComplex.singleFunctor
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj (r.obj M)
    let c : r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        DerivedCategory.Q.obj A :=
      (r.mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).app (r.obj M)
    obtain ⟨α, hα⟩ := Scheme.perfect_affine_map_representative S U hU A P
      (strictlyPerfect_single_restricted_unit S U) hP
      (c.inv ≫ r.mapDerivedCategory.map (derivedStructureUnit f) ≫ e.hom)
    let F := (Scheme.Modules.overEquiv U).functor
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    have hcomponent : IsIso (F.map (α.f 0)) := by
      apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
      intro x
      have hf := isIso_localized_stalk_component_of_residue_homology
        S (derivedStructureImage f) (derivedStructureUnit f) x.val U x.property P hP
          (fun i hi ↦ hPn i (by omega) (by omega)) hP0 e (hzero x.val) c α hα
      have : IsIso ((localizedModuleStalk S U x).map (α.f 0)) := hf
      exact ConcreteCategory.bijective_of_isIso
        ((localizedModuleStalk S U x).map (α.f 0))
    have : IsIso (α.f 0) := isIso_of_reflects_iso (α.f 0) F
    have hd : P.d 0 1 = 0 := by
      apply (cancel_epi (α.f 0)).mp
      rw [α.comm 0 1]
      have hz : A.d 0 1 = 0 := by simp [A]
      rw [hz, zero_comp, comp_zero]
    have hall (i j : ℤ) : P.d i j = 0 := by
      by_cases hrel : i + 1 = j
      · by_cases hi : i = 0
        · subst i
          subst j
          exact hd
        · by_cases hi' : i = 1
          · exact (hPn j (by omega) (by omega)).eq_of_tgt _ _
          · exact (hPn i hi hi').eq_of_src _ _
      · exact P.shape i j hrel
    let e0 : P.X 0 ≅ SheafOfModules.unit ((moduleRings S.toRingedSpace).over U) :=
      (asIso (α.f 0)).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 (r.obj M)
    exact ⟨U, hs, P, hP, hPn, hall, ⟨e0⟩,
      ⟨Scheme.derivedFiberBetti S (derivedStructureImage f) 1 s, hPf 1⟩, ⟨e⟩⟩
  have hlocalH (U : S.Opens)
      (P : CochainComplex (SheafOfModules.{u}
        ((moduleRings S.toRingedSpace).over U)) ℤ)
      (hd : ∀ i j : ℤ, P.d i j = 0)
      (e : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj (derivedStructureImage f) ≅
          DerivedCategory.Q.obj P) (i : ℤ) :
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
          (derivedStructureImage f)).over U ≅ P.X i :=
    (Functor.mapDerivedCategoryHomologyFunctorIso
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U) i).app
        (derivedStructureImage f) ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app P ≪≫
        zero_differential_homology_iso P hd i
  refine ⟨hperfect, hunit, hqc 1, ?_, ?_, ?_, ?_⟩
  · have hfree (s : S) : ∃ U : S.Opens, s ∈ U ∧ ∃ n : ℕ,
        Nonempty ((derivedStructureH1 f).over U ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin n))) := by
      obtain ⟨U, hs, P, _, _, hd, _, ⟨n, ⟨en⟩⟩, ⟨e⟩⟩ := hmodel s
      exact ⟨U, hs, n, ⟨hlocalH U P hd e 1 ≪≫ en⟩⟩
    choose U hs n he using hfree
    apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free U
      (by
        rw [Opens.coversTop_iff]
        apply top_unique
        intro s _
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hs s⟩)
      (fun s ↦ ULift.{u} (Fin (n s))) he
  · intro s
    obtain ⟨U, hs, P, _, hz, hd, ⟨e0⟩, _, ⟨e⟩⟩ := hmodel s
    obtain ⟨ep⟩ := two_degree_split P hz hd
    let e1 := (hlocalH U P hd e 1).symm
    let es := ((DerivedCategory.singleFunctors
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))).shiftIso
        (-1) 1 0 (by omega)).app ((derivedStructureH1 f).over U)
    let Q := DerivedCategory.Q (C := SheafOfModules.{u}
      ((moduleRings S.toRingedSpace).over U))
    have : Q.Additive := inferInstance
    have : PreservesFiniteBiproducts Q := inferInstance
    have := preservesBinaryBiproducts_of_preservesBiproducts Q
    refine ⟨U, hs, ⟨e ≪≫ Q.mapIso ep ≪≫
      (Q.mapBiprod _ _) ≪≫ biprod.mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (P.X 0)).symm
        ((DerivedCategory.singleFunctorIsoCompQ _ 1).app (P.X 1)).symm ≪≫
      biprod.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e0)
        ((DerivedCategory.singleFunctor _ 1).mapIso e1 ≪≫ es.symm)⟩⟩
  · intro i hi hi'
    apply Scheme.Modules.isZero_of_forall_exists_isZero_restrict
    intro s
    obtain ⟨U, hs, P, _, hz, hd, _, _, ⟨e⟩⟩ := hmodel s
    have h := (hz i hi hi').of_iso (hlocalH U P hd e i)
    have h' := (Scheme.Modules.overEquiv U).functor.map_isZero h
    exact ⟨U, hs, h'.of_iso ((Scheme.Modules.overFunctorEquiv U).app _).symm⟩
  · exact hbase

end

end AlgebraicGeometry
