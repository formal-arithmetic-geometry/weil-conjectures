/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import Mathlib.Algebra.CharP.CharAndCard

/-! # The dualizing complex is bounded constructible of finite Tor amplitude

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-preservation/det-pd-dualizing-complex-ctf.md
(blueprint: det-pd-dualizing-complex-ctf).

The exceptional functors are presented by their adjunctions to the actual
compactification lower shrieks, as in `exceptionalInverseImage_exists`.
The comparison is the conjugate of compact-support composition, evaluated at the
coefficient unit. In particular it is a specified morphism, rather than an
unconstrained isomorphism between the two dualizing objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem regular_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget
    (X := Mod.finiteFree Λ 0)).symm⟩⟩

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  let : (upperStarFromPoint X).Braided :=
    { toMonoidal := inferInstance
      braided := Functor.LaxBraided.braided }
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem regular_constructible (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular (𝟙 X) Λ⟩

private theorem zero_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] : Mod.IsFinitelyPresented Λ
      (0 : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso
    (isZero_cokernel_of_epi (𝟙 (Mod.finiteFree Λ 0)))⟩⟩

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj
        (0 : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj Λ S))) := by
  let 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    .singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _)
  refine ⟨𝒰, fun i ↦ ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩⟩
  exact ((CondensedRing.upperStar Λ (𝒰.f i)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint (𝒰.X i)).mapMod Λ).map_isZero (isZero_zero _))

private theorem zero_constructible (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X
      (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero (𝟙 X) Λ⟩

private theorem coefficientUnit_boundedConstructible
    (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj Λ X))) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible X Λ)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor C 0).obj
          (Mod.regular (condensedRingObj Λ X)))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff ((DerivedCategory.singleFunctor C 0).obj
          (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor C 0).obj
          (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible X Λ)

/-- The two assertions about the dualizing complex, using the actual exceptional
adjunctions and the compact-support compositor `α : Ra_Y! Rf! ≅ Ra_X!`.

The witnesses `hX`, `hY`, `hf` type the restrictions of the ambient compactification
functors to the localizing closures; they only certify membership and do not change
objects or maps. `GX`, `GY`, `Gf` are right adjoints of precisely those functors.
These witnesses and adjunctions are supplied by `exceptionalInverseImage_exists`;
there is no preservation premise on a right adjoint. The base coefficient unit is
written as its single complex in degree zero. Its membership in the localizing
category is a conclusion (`∃ h0`), not a premise.

The first conjunct is omega_X in Dctf(X,Lambda). The second states that the
canonical mate f! omega_Y to omega_X is invertible. Mathlib's `conjugateEquiv`
includes the units and counits of the pasted adjunction, so it specifies the
canonical morphism, including its direction. For the compositor supplied by the
compact-support composition theorem this is exactly the blueprint comparison.
All compactification and right-adjoint presentations are allowed.

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-pd-preservation/det-pd-dualizing-complex-ctf.md, both paragraphs
(blueprint: det-pd-dualizing-complex-ctf).

Proof:
1. On s = Spec k the regular coefficient module has one generator and no
   relations. The identity cover and the single stratum give the finite constant
   local model of sk-def-sfb-constructible. Its degree-zero complex is bounded,
   and tensoring it with any degree-zero module leaves that module, so its Tor
   amplitude is [0,0]. It therefore belongs to Dctf(s,Lambda), and hence to its
   localizing closure; this supplies h0.
2. The global field is algebraically closed, so sk-lem-base-field-cd gives
   cd_l(k)=0. The hypotheses of sk-thm-existence are thus satisfied for a_X
   and a_Y. Its exceptional-preservation clause gives the first conjunct for
   the Brown right adjoint. Uniqueness of right adjoints transports it to the
   supplied adjunctions, using isomorphism invariance of Dctf.
3. A morphism over k between these schemes is separated by separated
   cancellation, locally of finite type by finite-type cancellation, and
   quasi-compact since X is quasi-compact and Y quasi-separated. Thus
   sk-thm-sf-comp-composition applies to f, a_Y and a_X.
4. Paste adjf and adjY by def-weil-pbc-composite-adjunction, then conjugate
   alpha inverse by def-weil-pbc-adjunction-conjugate. The result is the
   natural isomorphism GY followed by Gf to GX. Its component at the unit is
   the displayed morphism, so it is invertible. Both objects belong to Dctf
   by steps 1--2 and exceptional preservation, so the isomorphism is also
   an isomorphism in that full subcategory.

Implementation: the statement already supplies `α`, so step 3 explains its geometric
origin and need not be repeated here. Step 2 is used only for `X`: compactification
comparison identifies the left adjoints, and uniqueness of right adjoints transports
preservation to `GX`. The last conjunct is `conjugateEquiv_iso` evaluated at the unit. -/
theorem dualizingComplex_mem_ctf_and_composition
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (cX : Compactification X.hom) (cY : Compactification Y.hom)
    (cf : Compactification f.left)
    (hX : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ (Spec (.of D.k))
        ((rightDerivedLowerShriekOfCompactification Λ cX).obj K))
    (hY : ∀ K, localizingClosureProEtale Λ Y.left K →
      localizingClosureProEtale Λ (Spec (.of D.k))
        ((rightDerivedLowerShriekOfCompactification Λ cY).obj K))
    (hf : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ cf).obj K))
    (GX : (localizingClosureProEtale Λ (Spec (.of D.k))).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (GY : (localizingClosureProEtale Λ (Spec (.of D.k))).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y.left).FullSubcategory)
    (Gf : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (adjX : localizingLowerShriek Λ cX hX ⊣ GX)
    (adjY : localizingLowerShriek Λ cY hY ⊣ GY)
    (adjf : localizingLowerShriek Λ cf hf ⊣ Gf)
    (α : localizingLowerShriek Λ cf hf ⋙ localizingLowerShriek Λ cY hY ≅
      localizingLowerShriek Λ cX hX) :
    ∃ h0 : localizingClosureProEtale Λ (Spec (.of D.k))
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj Λ (Spec (.of D.k))))),
      (constantModelBoundedConstructible Λ X.left ⊓
        DerivedCategory.finiteTorAmplitude _)
        (GX.obj ⟨(DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩).obj ∧
      IsIso (((conjugateEquiv (adjf.comp adjY) adjX) α.inv).app
        ⟨(DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj Λ (Spec (.of D.k)))), h0⟩) := by
  classical
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime :=
    ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ _hℓ.symm⟩
  let S := Spec (.of D.k)
  let C := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)
  have hunit : constantModelBoundedConstructible Λ S
      ((DerivedCategory.singleFunctor C 0).obj (Mod.regular (condensedRingObj Λ S))) :=
    coefficientUnit_boundedConstructible S Λ
  have htor : DerivedCategory.finiteTorAmplitude C
      ((DerivedCategory.singleFunctor C 0).obj (Mod.regular (condensedRingObj Λ S))) := by
    refine ⟨0, 0, ?_⟩
    intro N
    exact (DerivedCategory.homologyConcentratedIn 0 0).prop_of_iso
      ((MonoidalCategory.whiskerRightIso (DerivedCategory.singleFunctorObjUnitIso C) _) ≪≫
        MonoidalCategory.leftUnitor ((DerivedCategory.singleFunctor C 0).obj N)).symm
      ⟨inferInstance, inferInstance⟩
  have hunit' : (constantModelBoundedConstructible Λ S ⊓
      DerivedCategory.finiteTorAmplitude C)
      ((DerivedCategory.singleFunctor C 0).obj (Mod.regular (condensedRingObj Λ S))) :=
    ⟨hunit, htor⟩
  refine ⟨(fun P _ hP ↦ hP _ hunit'), ?_, inferInstance⟩
  let T : Over S := Over.mk (𝟙 S)
  have : LocallyOfFiniteType T.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  have : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (𝟙 S))
  have : IsSeparated T.hom := inferInstanceAs (IsSeparated (𝟙 S))
  let a : X ⟶ T := Over.homMk X.hom
  obtain ⟨_, _, _, _, h, _, _, H⟩ := exceptionalInverseImage_exists Λ ℓ D.k
    (BaseFieldFiniteCD.of_isAlgClosed ℓ D.k) a _hΛ
  obtain ⟨_, _, _, _, _, hcomp, ⟨G, _, _, ⟨adj⟩, hG⟩, _⟩ := H
  obtain ⟨e⟩ := hcomp cX
  let eL : localizingLowerShriek Λ (compactificationOverField a) h ≅
      localizingLowerShriek Λ cX hX :=
    ((localizingClosureProEtale Λ S).fullyFaithfulι.whiskeringRight _).preimageIso
      (e ≪≫ ((localizingClosureProEtale Λ S).liftCompιIso _ _).symm)
  let eG := (adj.ofNatIsoLeft eL).rightAdjointUniq adjX
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X.left).2.1
  exact (constantModelBoundedConstructible Λ X.left ⊓
    DerivedCategory.finiteTorAmplitude _).prop_of_iso
      ((localizingClosureProEtale Λ X.left).ι.mapIso (eG.app _)) (hG _ hunit')

end AlgebraicGeometry.ProEtale.CondensedRing
