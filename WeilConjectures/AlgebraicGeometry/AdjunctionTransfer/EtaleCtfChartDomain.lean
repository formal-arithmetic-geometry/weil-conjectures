/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportTorWindow
import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackTwistTorWindow
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSiteSquare
public import WeilConjectures.AlgebraicGeometry.EtaleChartComparison.EtaleChartComparisonIsos
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportTorWindowGeneralField
public import WeilConjectures.AlgebraicGeometry.EtalePullbackTwistTorWindowField
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible

/-! # Finite-Tor domains for ordinary etale charts

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
reduction-exceptional proof, Charts; Stacks Tags 03TT, 0F12, 09AL and 07A4
(blueprint: lem-sp-etale-ctf-chart-domain).

The predicates and comparison functor are exactly those of adjunction transfer.
A finite pro-etale Tate object is represented by the comparison pullback of the
ordinary finite Tate object. The finite-root site comparison identifies its first
power with the root sheaf tensored with the constant coefficient ring; the monoidal
comparison identifies all nonnegative powers. All Tor tests use every module sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer

/-- The ordinary etale chart operation: inverse image, finite Tate tensor, then shift.
Tensoring the line on the left uses the symmetry convention for `K(a)`.
Source: blueprint Charts, domain check; Stacks 03PK
(blueprint: lem-sp-etale-ctf-chart-domain). -/
def etaleChartOperation (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (u : T' ⟶ T) (a : ℕ) (b : ℤ) :
    Etale.DerivedCategoryModule R T ⥤ Etale.DerivedCategoryModule R T' :=
  ((Etale.upperStar (ModuleCat.{u + 1} R) u).mapDerivedCategory ⋙
    (Etale.derivedTensor (ModuleCat.{u + 1} R) T').obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist T' N R hR a))) ⋙ shiftFunctor _ b

/-- The same operation on the ordinary pro-etale site, with the finite Tate object
represented by exact comparison inverse image. This is the finite-root Tate object
by lem-amb-finite-root-site-comparison and the canonical monoidal comparison.
Source: blueprint Charts, comparison of finite Tate powers; Stacks 03PK and 07A4
(blueprint: lem-sp-etale-ctf-chart-domain). -/
def proEtaleChartOperation (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (u : T' ⟶ T) (a : ℕ) (b : ℤ) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T') (ModuleCat.{u + 1} R)) :=
  ((ProEtale.upperStar (ModuleCat.{u + 1} R) u).mapDerivedCategory ⋙
    (ProEtale.derivedTensor (ModuleCat.{u + 1} R) T').obj
      ((comparisonUpperStar (ModuleCat.{u + 1} R) T').mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist T' N R hR a)))) ⋙ shiftFunctor _ b

/-- The canonical comparison for inverse image followed by finite Tate tensor and shift.
It is built from the actual site pullback comparison, the derived tensor comparison,
and the exact comparison functor's signed-shift comparison. Thus it is natural and
retains the prescribed maps, rather than selecting an isomorphism of the objects.
Source: blueprint Charts, final two proof steps; Stacks 07A4 and 0GLZ
(blueprint: lem-sp-etale-ctf-chart-domain). -/
def chartOperationComparison (R : Type (u + 1)) [CommRing R] [Finite R] (N : ℕ)
    (hR : (N : R) = 0) {T T' : Scheme.{u}} (u : T' ⟶ T) (a : ℕ) (b : ℤ) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        proEtaleChartOperation R N hR u a b ≅
      etaleChartOperation R N hR u a b ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T').mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
            Functor.mapDerivedCategoryNatIso
              (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) u) ≪≫
            Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
            (ModuleCat.{u + 1} R)
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist T' N R hR a))).symm ≪≫
        (Functor.associator _ _ _).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((comparisonUpperStar (ModuleCat.{u + 1} R) T').mapDerivedCategory.commShiftIso b).symm ≪≫
    (Functor.associator _ _ _).symm

private theorem bounded_of_constructible
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule R T)
    (hK : Etale.DerivedCategory.isBoundedConstructible R T K) :
    _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨a, b, _, hz⟩ := hK.2
  exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun i hi ↦ hz i (.inl hi))⟩,
    ⟨b, (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))⟩⟩

private theorem property_of_iso
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    {K L : Etale.DerivedCategoryModule R T} (e : K ≅ L)
    (hK : etaleProperty R T K) : etaleProperty R T L := by
  refine ⟨⟨?_, ?_⟩, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e hK.2⟩
  · intro i
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1.1 i)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e))
  · obtain ⟨a, b, hab, hz⟩ := hK.1.2
    exact ⟨a, b, hab, fun i hi ↦ (hz i hi).of_iso
      (((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm)⟩

private theorem comparison_preserves
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) :
    ∀ K, etaleProperty R T K → proEtaleProperty R T
      ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) := by
  rintro K ⟨hc, a, b, ht⟩
  exact ⟨ObjectProperty.prop_map_obj _ _ hc, a, b,
    (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
      (comparisonUpperStar (ModuleCat.{u + 1} R) T) a b K).2 ht⟩

private theorem comparison_preimage
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)))
    (hK : proEtaleProperty R T K) :
    ∃ L, etaleProperty R T L ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj L ≅ K) := by
  obtain ⟨L, hc, ⟨e⟩⟩ := hK.1
  obtain ⟨a, b, ht⟩ :=
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hK.2
  exact ⟨L, ⟨hc, a, b,
    (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
      (comparisonUpperStar (ModuleCat.{u + 1} R) T) a b L).1 ht⟩, ⟨e⟩⟩

private theorem comparison_equivalence
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) :
    (comparison R T (comparison_preserves R T)).IsEquivalence := by
  let F := comparison R T (comparison_preserves R T)
  have : F.Full := by
    constructor
    intro K L f
    obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (bounded_of_constructible R T L.obj L.property.1).1).2 f.hom
    exact ⟨ObjectProperty.homMk g, by ext; exact hg⟩
  have : F.Faithful := by
    constructor
    intro K L f g hfg
    ext
    apply (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (bounded_of_constructible R T L.obj L.property.1).1).1
    exact congrArg (fun t ↦ t.hom) hfg
  have : F.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := comparison_preimage R T K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact {}

/-- The current scalar-extension counit computes extension on a K-flat complex.
Source: Stacks 06YT and 06YY (blueprint: lem-sp-etale-ctf-chart-domain). -/
private theorem fixed_scalar_counit_iso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso
      (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat P) :
    IsIso ((fixedCoefficientDerivedExtensionCounit J φ).app P) := by
  let E := fixedCoefficientScalarExtension J φ
  have : E.PreservesKFlatQuasiIso := CategoryTheory.fixedExtension_preservesKFlat J φ
  have hd : (HomologicalComplex.quasiIso
      (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).localizerMorphismKFlat.Derives
      (E.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q) := by
    intro X Y f hf
    let g := (HomologicalComplex.quasiIso
      (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).ιKFlat.map f
    have : QuasiIso g := (HomologicalComplex.mem_quasiIso_iff g).1 hf
    have := E.quasiIso_mapHomologicalComplex_map_of_kFlat X.property Y.property g
    exact Localization.inverts _root_.DerivedCategory.Q _ _
      ((HomologicalComplex.mem_quasiIso_iff _).2 this)
  have : (fixedCoefficientDerivedExtension J φ).IsLeftDerivedFunctor
      (fixedCoefficientDerivedExtensionCounit J φ)
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)) := by
    dsimp only [fixedCoefficientDerivedExtension, fixedCoefficientDerivedExtensionCounit]
    infer_instance
  exact hd.isIso_of_isLeftDerivedFunctor (fixedCoefficientDerivedExtensionCounit J φ)
    ⟨P, hP⟩

/-- Bounded flat constructible models compute the current ordinary scalar extension.
Source: Stacks 03TT, 0GKB, 06YT and 08G1 (blueprint: lem-sp-etale-ctf-chart-domain). -/
private theorem scalar_preserves_etale
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : Etale.DerivedCategoryModule A T) (hK : etaleProperty A T K) :
    etaleProperty B T ((fixedCoefficientDerivedExtension T.smallEtaleTopology φ).obj K) := by
  obtain ⟨a, b, ht⟩ := hK.2
  have hab : min a b ≤ b := min_le_right _ _
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left a b) le_rfl)
  obtain ⟨P, hf, hc, hz, ⟨e⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A T (min a b) b hab K hK.1).1 ht'
  have : P.IsStrictlyGE (min a b) := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun q hq ↦ hz q (.inl hq))
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun q hq ↦ hz q (.inr hq))
  have hp := CochainComplex.kFlat_of_bounded_of_flat P (min a b) b hf
  let E := fixedCoefficientScalarExtension T.smallEtaleTopology φ
  let Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj P
  have hqf (q : ℤ) : ObjectProperty.flat (Q.X q) :=
    flat_etaleSheafExtendScalars_obj (φ := φ) (hf q)
  have hqz (q : ℤ) (hq : q < min a b ∨ b < q) : IsZero (Q.X q) :=
    E.map_isZero (hz q hq)
  have : Q.IsStrictlyGE (min a b) := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun q hq ↦ hqz q (.inl hq))
  have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun q hq ↦ hqz q (.inr hq))
  have htor := _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q (min a b) b hqf
  have hcons := (constructibleCoefficientSiteSquare T A B φ (min a b) b hab P hz hc).2.2.2.1
  have := fixed_scalar_counit_iso T.smallEtaleTopology φ P hp
  let eQ : (fixedCoefficientDerivedExtension T.smallEtaleTopology φ).obj K ≅
      _root_.DerivedCategory.Q.obj Q :=
    (fixedCoefficientDerivedExtension T.smallEtaleTopology φ).mapIso e.symm ≪≫
      asIso ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology φ).app P)
  exact property_of_iso B T eQ.symm ⟨hcons, min a b, b, htor⟩

/-- Compact support, comparison, and twisted shifted inverse image have the finite-Tor
chart domains. The coefficient `R` is arbitrary: specialize it separately to A and B
with the same annihilating power. The chosen compactification's middle scheme has
its induced k-structure and is again separated of finite type by Compactification.overZ,
locallyOfFiniteType_over, quasiCompact_over and isSeparated_over.

Source: blueprint main-20261015, reduction-exceptional proof, Charts;
Stacks 03TT, 06YQ, 0F12, 09AL, 03PK and 07A4
(blueprint: lem-sp-etale-ctf-chart-domain).

Proof:
1. Every finite-type k-scheme is Noetherian; every finite ring is Noetherian.
   For each input and Tor interval use lem-sf-etale-flat-constructible to choose a
   flat constructible representative supported in that interval. It is K-flat by
   lem-pc-bounded-above-flat-kflat-site. No common interval for all inputs is required.
2. Extension by zero is exact (lem-weil-pbc-extension-by-zero-exact), constructible
   (lem-fin-extension-by-zero), and flat by lem-weil-pbc-ringed-slice-extension-tensor
   and exact restriction (prop-weil-pbc-inverse-image-modules-exact). Its model has
   the same support and hence still gives finite Tor amplitude and constructibility,
   using thm-constructible-serre for cohomology.
3. lem-sfb-finite-proper-geometric-cd-bound bounds torsion cohomology on all geometric
   fibres by 2e. Apply det-ctf-finite-proper-tor to the proper part, obtaining output
   Tor interval [alpha,beta+2e]. This is def-amb-etale-compact-support.
4. Exact inverse image preserves flat K-flat models by
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and constructibility by
   prop-constructible-pullback. The characteristic assumption makes N invertible.
   lem-asd-finite-etale-twist-line supplies flat constructible Tate lines, including
   the zeroth power. Tensor preserves the interval by lem-fd-flat-constructible-tensor;
   shifting by b changes it to [alpha-b,beta-b].
5. Apply det-pe-finite-tor-comparison-noetherian to the qcqs scheme and finite ring.
   Transport its small-site model through the constant-module equivalences to the
   exact ordinary comparison. This gives the displayed equivalence and both
   implications for each Tor interval. The ordinary Tor predicate is the actual
   test against all module sheaves, not only etale-origin pro-etale tests.
6. The canonical inverse-image comparison of lem-weil-pbc-comparison-pullback,
   exactness of lem-sf-comparison-pullback-exact and lem-pur-coefficient-pullback-exact,
   the tensor comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and the
   root identification of lem-amb-finite-root-site-comparison give
   chartOperationComparison. Transport preservation across the finite-Tor comparison
   equivalences to get the pro-etale domain assertion. -/
theorem etaleCtfChartDomain
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    (R : Type (u + 1)) [CommRing R] [Finite R] (n : ℕ) (hR : ((ℓ ^ n : ℕ) : R) = 0)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))]
    [LocallyOfFiniteType h] [QuasiCompact h] [IsSeparated h] (c : Compactification h)
    {T T' : Scheme.{u}} [T.Over (Spec (.of k))] [T'.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T' ↘ Spec (.of k))] [QuasiCompact (T' ↘ Spec (.of k))]
    [IsSeparated (T' ↘ Spec (.of k))]
    (u : T' ⟶ T) [u.IsOver (Spec (.of k))] :
    (∀ K, etaleProperty R U K → etaleProperty R V
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K)) ∧
    (∃ hc : ∀ K, etaleProperty R T K → proEtaleProperty R T
        ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K),
      (comparison R T hc).IsEquivalence) ∧
    (∀ K, Etale.DerivedCategory.isBoundedConstructible R T K →
      ∀ a b : ℤ, a ≤ b →
        (_root_.DerivedCategory.torAmplitudeIn
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) a b K ↔
          _root_.DerivedCategory.torAmplitudeIn
            (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) a b
            ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K))) ∧
    (∀ (a : ℕ) (b : ℤ) K, etaleProperty R T K → etaleProperty R T'
      ((etaleChartOperation R (ℓ ^ n) hR u a b).obj K)) ∧
    (∀ (a : ℕ) (b : ℤ) K, proEtaleProperty R T K → proEtaleProperty R T'
      ((proEtaleChartOperation R (ℓ ^ n) hR u a b).obj K)) := by
  classical
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have : IsNoetherian T := ⟨⟩
  have hcompact : ∀ K, etaleProperty R U K → etaleProperty R V
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K) := by
    obtain ⟨e, _, he⟩ := Etale.exists_etaleCompactSupport_torWindow_of_finite_or_isAlgClosed
      k ℓ Fact.out hk hchar c.g
    intro K hK
    obtain ⟨a, b, ht⟩ := hK.2
    have hab : min a b ≤ b := min_le_right _ _
    have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (ht.mono (min_le_left a b) le_rfl)
    obtain ⟨P, hf, hc, hz, hP⟩ :=
      (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
        R U (min a b) b hab K hK.1).1 ht'
    have hprimary : ∃ m : ℕ, 1 ≤ m ∧ (ℓ ^ m : ℕ) • (1 : R) = 0 := by
      refine ⟨n + 1, by omega, ?_⟩
      simp only [pow_succ, Nat.cast_mul, nsmul_eq_mul, mul_one, hR, zero_mul]
    have h := he U c.i R hprimary (min a b) b hab K hK.1 ht' P hP
      (fun i ↦ (hf i).tensorRight) hc hz
    exact ⟨h.2.2.2.2.2.2.2.1, min a b, b + 2 * (e : ℤ),
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2.2.2.2.2.2.2.2⟩
  have hchart : ∀ (a : ℕ) (b : ℤ) K, etaleProperty R T K → etaleProperty R T'
      ((etaleChartOperation R (ℓ ^ n) hR u a b).obj K) := by
    intro a b K hK
    obtain ⟨i, j, ht⟩ := hK.2
    have hij : min i j ≤ j := min_le_right _ _
    have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (ht.mono (min_le_left i j) le_rfl)
    obtain ⟨P, hf, hc, hz, hP⟩ :=
      (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
        R T (min i j) j hij K hK.1).1 ht'
    have : IsSeparated (Over.mk (T ↘ Spec (.of k))).hom :=
      ‹IsSeparated (T ↘ Spec (.of k))›
    have : LocallyOfFiniteType (Over.mk (T ↘ Spec (.of k))).hom :=
      ‹LocallyOfFiniteType (T ↘ Spec (.of k))›
    have : QuasiCompact (Over.mk (T ↘ Spec (.of k))).hom :=
      ‹QuasiCompact (T ↘ Spec (.of k))›
    have : IsSeparated (Over.mk (T' ↘ Spec (.of k))).hom :=
      ‹IsSeparated (T' ↘ Spec (.of k))›
    have : LocallyOfFiniteType (Over.mk (T' ↘ Spec (.of k))).hom :=
      ‹LocallyOfFiniteType (T' ↘ Spec (.of k))›
    have : QuasiCompact (Over.mk (T' ↘ Spec (.of k))).hom :=
      ‹QuasiCompact (T' ↘ Spec (.of k))›
    let f : Over.mk (T' ↘ Spec (.of k)) ⟶ Over.mk (T ↘ Spec (.of k)) :=
      Over.homMk u (comp_over u _)
    have h := (Etale.etale_pullback_twist_tor_window_finite_or_algClosed
      k hk ℓ Fact.out hchar _ _ f n R hR (min i j) j hij).1
        K hK.1 ht' P hP (fun i ↦ (hf i).tensorRight) hc hz a b
    let := _root_.DerivedCategory.braidedCategory'
      (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} R))
    let e : Etale.pullbackTwistDerived R u (ℓ ^ n) hR K a b ≅
        (etaleChartOperation R (ℓ ^ n) hR u a b).obj K :=
      (shiftFunctor _ b).mapIso (β_ _ _)
    exact property_of_iso R T' e ⟨h.2.2.2.2.2.1, min i j - b, j - b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2.2.2.2.2.2⟩
  refine ⟨hcompact, ⟨comparison_preserves R T, comparison_equivalence R T⟩, ?_, hchart, ?_⟩
  · intro K _ a b _
    exact (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
      (comparisonUpperStar (ModuleCat.{u + 1} R) T) a b K).symm
  · intro a b K hK
    obtain ⟨L, hL, ⟨e⟩⟩ := comparison_preimage R T K hK
    have h := comparison_preserves R T' _ (hchart a b L hL)
    let d := ((proEtaleChartOperation R (ℓ ^ n) hR u a b).mapIso e).symm ≪≫
      (chartOperationComparison R (ℓ ^ n) hR u a b).app L
    refine ⟨?_, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso d.symm h.2⟩
    exact ((Etale.DerivedCategory.isBoundedConstructible R T').map
      (comparisonUpperStar (ModuleCat.{u + 1} R) T').mapDerivedCategory).prop_of_iso d.symm h.1

/-- Arbitrary finite coefficient extension preserves both chart domains. The comparison
on these domains is the current derived scalar comparison encoded by
`EtaleChartComparison.ScalarModel`.
No finite projective dimension or flatness of B over A is assumed.

Source: blueprint Charts, coefficient-change proof step; Stacks 03TT, 0GKB, 06YY and 07A4
(blueprint: lem-sp-etale-ctf-chart-domain).

Proof:
1. Choose a bounded flat constructible model P for K by
   lem-sf-etale-flat-constructible. It is K-flat by
   lem-pc-bounded-above-flat-kflat-site.
2. lem-pur-derived-change-of-rings computes scalar extension by P tensor_A B.
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback makes the result K-flat with
   flat B-terms. The tensor does not change the support interval.
3. On each constructible stratum, extend a finite local A-value M to B tensor_A M.
   This is a finite B-module, since it is a quotient of a finite free B-module.
   Hence the same strata are constructible over B. Kernels and cokernels are
   constructible by thm-constructible-serre, giving bounded constructibility.
4. Tensor the resulting bounded flat B-model with every degree-zero B-module
   sheaf. It remains in the same finite interval, proving finite B-Tor amplitude.
5. Use the current total left-derived coefficient extension on the small ordinary and
   pro-etale sites. The canonical B-linear comparison is the left-derived image of
   `EtaleChartComparison.scalarSheafIso`; its K-flat formula is the ordinary balanced
   tensor comparison for the current fixed coefficient extension. Apply the comparison
   equivalence on both rings and the ordinary
   coefficient-extension preservation to deduce the pro-etale assertion. -/
theorem etaleCtfChartScalarDomain
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hA : ((ℓ ^ n : ℕ) : A) = 0) (_hB : ((ℓ ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] :
    (∀ K, etaleProperty A T K → etaleProperty B T
      ((CategoryTheory.fixedCoefficientDerivedExtension T.smallEtaleTopology φ).obj K)) ∧
    (∀ K, proEtaleProperty A T K → proEtaleProperty B T
      ((CategoryTheory.fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) φ).obj K)) := by
  classical
  have _ := hk
  have _ := hchar
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have : IsNoetherian T := ⟨⟩
  refine ⟨scalar_preserves_etale φ T, ?_⟩
  intro K hK
  obtain ⟨L, hL, ⟨e⟩⟩ := comparison_preimage A T K hK
  obtain ⟨a, b, ht⟩ := hL.2
  have hab : min a b ≤ b := min_le_right _ _
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left a b) le_rfl)
  obtain ⟨P, hf, _, hz, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A T (min a b) b hab L hL.1).1 ht'
  have : P.IsStrictlyGE (min a b) := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun q hq ↦ hz q (.inl hq))
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun q hq ↦ hz q (.inr hq))
  have hp := CochainComplex.kFlat_of_bounded_of_flat P (min a b) b hf
  let NA := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let NB := comparisonUpperStar (ModuleCat.{u + 1} B) T
  let E := fixedCoefficientScalarExtension T.smallEtaleTopology φ
  let F := fixedCoefficientScalarExtension (Scheme.ProEt.topology T) φ
  let PN : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ :=
    (NA.mapHomologicalComplex (.up ℤ)).obj P
  let PE := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hnf (q : ℤ) : ObjectProperty.flat (PN.X q) :=
    flat_comparisonUpperStar_obj (hf q)
  have hnz (q : ℤ) (hq : q < min a b ∨ b < q) : IsZero (PN.X q) :=
    NA.map_isZero (hz q hq)
  have : PN.IsStrictlyGE (min a b) := (CochainComplex.isStrictlyGE_iff _ _).2
    (fun q hq ↦ hnz q (.inl hq))
  have : PN.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
    (fun q hq ↦ hnz q (.inr hq))
  have hpn := CochainComplex.kFlat_of_bounded_of_flat PN (min a b) b hnf
  have := fixed_scalar_counit_iso T.smallEtaleTopology φ P hp
  have := fixed_scalar_counit_iso (Scheme.ProEt.topology T) φ PN hpn
  let eEt : (fixedCoefficientDerivedExtension T.smallEtaleTopology φ).obj L ≅
      _root_.DerivedCategory.Q.obj PE :=
    (fixedCoefficientDerivedExtension T.smallEtaleTopology φ).mapIso eP.symm ≪≫
      asIso ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology φ).app P)
  let eSrc : NA.mapDerivedCategory.obj L ≅ _root_.DerivedCategory.Q.obj PN :=
    NA.mapDerivedCategory.mapIso eP.symm ≪≫ NA.mapDerivedCategoryFactors.app P
  let ePro : (fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) φ).obj K ≅
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj PN) :=
    (fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) φ).mapIso
      (e.symm ≪≫ eSrc) ≪≫
      asIso ((fixedCoefficientDerivedExtensionCounit (Scheme.ProEt.topology T) φ).app PN)
  let chain := (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ NB)) (.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (EtaleChartComparison.scalarSheafIso φ T) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso (Iso.refl (NA ⋙ F)) (.up ℤ)
  let d := ePro ≪≫ (_root_.DerivedCategory.Q.mapIso (chain.app P)).symm ≪≫
    (NB.mapDerivedCategoryFactors.app PE).symm ≪≫ NB.mapDerivedCategory.mapIso eEt.symm
  have h := comparison_preserves B T _ (scalar_preserves_etale φ T L hL)
  refine ⟨?_, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso d.symm h.2⟩
  exact ((Etale.DerivedCategory.isBoundedConstructible B T).map
    NB.mapDerivedCategory).prop_of_iso d.symm h.1

end AlgebraicGeometry.ProEtale.AdjunctionTransfer
