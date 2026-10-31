/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.WeilCompletedTensorReflector
public import WeilConjectures.CategoryTheory.ReflectedAdjunctionCoefficientSquares
public import WeilConjectures.AlgebraicGeometry.RingedPushforwardCompletion
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
import all WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree
import WeilConjectures.CategoryTheory.SystemScalarCoherence

/-! # Finite scalar change and completed pullback with the actual units

Source: Stacks Project, algebraization.tex, Tags 0A0E and 0A0G; the finite scalar
extension construction, retained steps 5--7
(blueprint: lem-per-rational-scalar-completion-unit-square).
The coefficient maps, derived tensors, raw categories and quotient-tower units are
those of the imported dependency nodes. Comparison arrows below only orient the
published canonical comparisons and transport them through the unit-normalized
ambient quotient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def scalarUnitIso {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.unit (reductionModuleRing W R) ≅
      (pbcRestrict e.hom).obj (SheafOfModules.unit (reductionModuleRing W S)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      let eU := Iso.commRingCatIsoToRingEquiv
        (((sheafToPresheaf (ProEt.topology W) CommRingCat).mapIso e).app U)
      ModuleCat.isoMk eU.toAddEquiv.toAddCommGrpIso
        (by intro r; ext x; exact ((e.hom.hom.app U).hom.map_mul r x).symm))
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) x))

private theorem scalarFreeTransport {W : Scheme.{u}}
    {R S R' S' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (eR : R ≅ R') (eS : S ≅ S') (φ : R ⟶ S) (ψ : R' ⟶ S')
    (h : eR.hom ≫ ψ = φ ≫ eS.hom) (n : ℕ)
    (hf : Nonempty ((pbcRestrict ψ).obj
      (SheafOfModules.unit (reductionModuleRing W S')) ≅
        ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit (reductionModuleRing W R'))) :
    Nonempty ((pbcRestrict φ).obj (SheafOfModules.unit (reductionModuleRing W S)) ≅
      ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit (reductionModuleRing W R)) := by
  obtain ⟨f⟩ := hf
  let ρ := pbcRestrict eR.hom
  let k := SheafOfModules.systemScalarRestrictionComposition φ eS.hom
    (φ ≫ eS.hom) rfl
  let j := SheafOfModules.systemScalarRestrictionComposition eR.hom ψ
    (φ ≫ eS.hom) h.symm
  exact ⟨(pbcRestrict φ).mapIso (scalarUnitIso eS) ≪≫
    k.app _ ≪≫ (j.app _).symm ≪≫ ρ.mapIso f ≪≫
    PreservesProduct.iso ρ (fun _ : Fin n ↦
      SheafOfModules.unit (reductionModuleRing W R')) ≪≫
    Pi.mapIso (fun _ : Fin n ↦ (scalarUnitIso eR).symm)⟩

private theorem completionUnitor {C : Type*} [Category C]
    (T Λ : C ⥤ C) (η : 𝟭 C ⟶ Λ) (v : T ≅ 𝟭 C)
    (κ : Λ ⋙ T ≅ T ⋙ Λ)
    (hκ : ∀ M, T.map (η.app M) ≫ κ.hom.app M = η.app (T.obj M)) (M : C)
    (hinj : Function.Injective (fun f : Λ.obj M ⟶ Λ.obj (T.obj M) ↦ η.app M ≫ f)) :
    κ.hom.app M = v.hom.app (Λ.obj M) ≫ Λ.map (v.inv.app M) := by
  apply (cancel_epi (v.inv.app (Λ.obj M))).1
  apply hinj
  change η.app M ≫ (v.inv.app (Λ.obj M) ≫ κ.hom.app M) =
    η.app M ≫ (v.inv.app (Λ.obj M) ≫
      (v.hom.app (Λ.obj M) ≫ Λ.map (v.inv.app M)))
  have hn : η.app M ≫ v.inv.app (Λ.obj M) =
      v.inv.app M ≫ T.map (η.app M) := v.inv.naturality (η.app M)
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, hn, Category.assoc, hκ]
  exact η.naturality (v.inv.app M)


/-- The quotient-tower construction is ordinary pullback followed by reflection,
including the actual augmentation, on arbitrary ambient complexes.
Source: Stacks 099M and 099N (2),(5)
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof: choose a flat-term K-flat representative of the input. The reduction/pullback
comparison identifies the whole pulled reduction tower with the reduction tower of
ordinary pullback, including all transitions and the constant-tower augmentation.
Apply the specified derived inverse limit. The Koszul/quotient comparison identifies
its augmentation with the Koszul completion unit. The Koszul reflector's Hom bijection
identifies that completion with pbcActualCompletion, preserving its unit. These steps
use no completeness of the input. They give a natural isomorphism with the displayed
normalization. A map out of a reflected object into a complete object is determined by
its composite with the unit, so the normalization determines the isomorphism uniquely.
On complete inputs the same uniqueness recovers pbcActualCompletedPullback_tower. -/
theorem pbcActualAmbientCompletedPullback_tower
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! e : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d,
      ∀ K : PbcCompletedDerived Y d,
        (pbcActualStrictCompletedPullUnit d g).app K ≫ e.hom.app K =
          (pbcActualCompletedPullUnit g d).app K := by
  classical
  let L := pbcActualDerivedPull g d
  let R := completedTowerRlim d X
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let t : completedReductionTower Y d ⋙ completedTowerPullback g d ≅
      L ⋙ completedReductionTower X d :=
    Functor.isoWhiskerLeft (completedReductionTower Y d) eT ≪≫ τ ≪≫
      Functor.isoWhiskerRight eL.symm (completedReductionTower X d)
  have ht (K : PbcCompletedDerived Y d) :
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
          t.hom.app K = (completedReductionTowerUnit d X).app (L.obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := actualCompletion_quotient d X
  let b : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
    Functor.isoWhiskerRight t R ≪≫ Functor.associator L (completedReductionTower X d) R ≪≫
      Functor.isoWhiskerLeft L c.symm
  have hb (K : PbcCompletedDerived Y d) :
      (pbcActualStrictCompletedPullUnit d g).app K ≫ b.hom.app K =
        (pbcActualCompletedPullUnit g d).app K := by
    have hu : completedPullbackComparison g d K ≫ R.map (t.hom.app K) =
        d.completionUnit X (L.obj K) := by
      dsimp only [completedPullbackComparison]
      rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
      rfl
    simp only [pbcActualStrictCompletedPullUnit, pbcActualCompletedPullUnit, b,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.comp_obj, Iso.symm_hom]
    change completedPullbackComparison g d K ≫
      (R.map (t.hom.app K) ≫ c.inv.app (L.obj K)) =
        (pbcActualCompletionUnit d X).app (L.obj K)
    rw [← Category.assoc, hu, ← hc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  refine ⟨b, hb, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  apply (cancel_epi (b.inv.app K)).1
  apply (actualReflection d X (L.obj K)
    ((pbcActualCompletedPull g d).obj K)
    (pbcActualCompletedPull_isComplete g d K)).injective
  have hi : (pbcActualCompletedPullUnit g d).app K ≫ b.inv.app K =
      (pbcActualStrictCompletedPullUnit d g).app K := by
    rw [← hb K, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  change (pbcActualCompletedPullUnit g d).app K ≫
      (b.inv.app K ≫ e'.hom.app K) =
    (pbcActualCompletedPullUnit g d).app K ≫ (b.inv.app K ≫ b.hom.app K)
  rw [← Category.assoc, ← Category.assoc, hi, he']
  exact (hb K).symm

/-- The uniquely augmentation-normalized ambient comparison; no unrelated map is chosen.
Source: Stacks 099M and 099N (2),(5)
(blueprint: lem-per-rational-scalar-completion-unit-square). -/
def pbcActualAmbientCompletedPullbackIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
  (pbcActualAmbientCompletedPullback_tower d g).exists.choose


variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (i : E →ₐ[ℚ_[l]] L)

/-- The canonical scalar/completion comparison in the direction denoted kappa.
Source: Stacks 0A0E (blueprint: lem-per-rational-scalar-completion-unit-square). -/
def rationalScalarCompletionKappa (W : Scheme.{u}) :
    pbcActualCompletion (pbcIntegralDatum l E) W ⋙ pbcEmbeddingAmbientTensor l E L i W ≅
      pbcEmbeddingAmbientTensor l E L i W ⋙ pbcActualCompletion (pbcIntegralDatum l L) W :=
  (pbcScalarCompletionIso l E L i W).symm

/-- The ordinary balanced comparison in the direction denoted beta.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-per-rational-scalar-completion-unit-square). -/
def rationalScalarOrdinaryBeta {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙ pbcEmbeddingAmbientTensor l E L i X ≅
      pbcEmbeddingAmbientTensor l E L i Y ⋙ pbcActualDerivedPull g (pbcIntegralDatum l L) :=
  (pbcScalarOrdinaryPullIso l E L i g).symm

/-- The inverse reflected coefficient-square comparison, with the published normalization.
Source: Stacks 0A0E and 0A0G
(blueprint: lem-per-rational-scalar-completion-unit-square). -/
def rationalScalarReflectedBeta {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙ pbcEmbeddingAmbientTensor l E L i X ≅
      pbcEmbeddingAmbientTensor l E L i Y ⋙ pbcActualCompletedPull g (pbcIntegralDatum l L) :=
  (pbcScalarCompletedPullIso l E L i g).symm

/-- The same comparison on the actual quotient-tower functors, retaining both units.
Source: Stacks 099M, 099N, 0A0E and 0A0G
(blueprint: lem-per-rational-scalar-completion-unit-square). -/
def rationalScalarStrictBeta {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙
        pbcEmbeddingAmbientTensor l E L i X ≅
      pbcEmbeddingAmbientTensor l E L i Y ⋙
        pbcActualStrictCompletedPull (pbcIntegralDatum l L) g :=
  Functor.isoWhiskerRight (pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l E) g)
      (pbcEmbeddingAmbientTensor l E L i X) ≪≫
    rationalScalarReflectedBeta l E L i g ≪≫
      Functor.isoWhiskerLeft (pbcEmbeddingAmbientTensor l E L i Y)
        (pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l L) g).symm

/-- Finite freeness has the actual relative degree; the uniformizer image is a positive
power times a unit, including ramified extensions.
Source: Serre, Local Fields, I.1 and II.2; Stacks 0A0E
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 1: the finite-free completed scalar comparison supplies the basis
isomorphism after transporting the lifted valuation-ring presentation through its
finite projections. Its rank is the relative field degree. The unique extended
absolute values agree on E, so the image of its uniformizer has value strictly
between zero and one. DVR factorization in L therefore has positive exponent.
Constant sections carry the equality and the inverse unit into both ring sheaves.
No unramified hypothesis is used. -/
theorem rationalScalarCompletionCoefficients (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))] :
    Nonempty
      ((pbcRestrict (pbcScalarCoefficientMap l E L i W)).obj
          (SheafOfModules.unit
            (reductionModuleRing W (pbcAdicCompletion W (pbcIntegralDatum l L)))) ≅
        ∏ᶜ fun _ : Fin (WeilConjectures.completedScalarRelativeDegree l E L i) ↦
          SheafOfModules.unit
            (reductionModuleRing W (pbcAdicCompletion W (pbcIntegralDatum l E)))) ∧
    ∃ (e : ℕ) (a : (PbcIntegralRing l L)ˣ), 1 ≤ e ∧
      pbcEmbeddingIntegerMap l E L i (pbcUniformizer l E) =
        (a : PbcIntegralRing l L) * pbcUniformizer l L ^ e ∧
      ∀ U : W.ProEtᵒᵖ,
        IsUnit (pbcCompletedSection W (pbcIntegralDatum l L) U (a : PbcIntegralRing l L)) ∧
        (pbcScalarCoefficientMap l E L i W).hom.app U
            (pbcCompletedSection W (pbcIntegralDatum l E) U (pbcUniformizer l E)) =
          pbcCompletedSection W (pbcIntegralDatum l L) U (a : PbcIntegralRing l L) *
            pbcCompletedSection W (pbcIntegralDatum l L) U (pbcUniformizer l L) ^ e := by
  have hmap : WeilConjectures.integralCompletedScalarMap l E L i W =
      WeilConjectures.completedCoefficientMap l E L i W := by
    apply (WeilConjectures.completedCoefficientMap_existsUnique l E L i W).unique
    · exact (WeilConjectures.integralCompletedScalarMap_existsUnique l E L i W).exists.choose_spec
    · exact (WeilConjectures.completedCoefficientMap_existsUnique l E L i W).exists.choose_spec
  have hs := WeilConjectures.coefficientScalar_square l E L i W
  rw [hmap] at hs
  have hf := scalarFreeTransport (WeilConjectures.purCoefficientIso l E W)
    (WeilConjectures.purCoefficientIso l L W) (pbcScalarCoefficientMap l E L i W)
    (WeilConjectures.completedCoefficientMap l E L i W) hs
    (WeilConjectures.completedScalarRelativeDegree l E L i)
    (WeilConjectures.finiteFreeCompletedScalarComparison l E L i W).1
  refine ⟨hf, ?_⟩
  obtain ⟨a, e, he, ht⟩ := WeilConjectures.integral_ramification l E L i
  let a' : (PbcIntegralRing l L)ˣ :=
    Units.map ULift.ringEquiv.symm.toRingHom.toMonoidHom a
  have ht' : pbcEmbeddingIntegerMap l E L i (pbcUniformizer l E) =
      (a' : PbcIntegralRing l L) * pbcUniformizer l L ^ e := by
    apply ULift.ext
    exact ht
  refine ⟨e, a', he, ht', ?_⟩
  intro U
  refine ⟨a'.isUnit.map (pbcCompletedSection W (pbcIntegralDatum l L) U), ?_⟩
  rw [scalarCompletedCoefficientSection, ht', map_mul, map_pow]

/-- Scalar extension commutes with the ambient completion, preserving its actual unit.
Source: Stacks 0A0E and 099M
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 2: use finite-free completion transport with the positive unit-power
relation of step 1. Constant/Koszul/quotient comparison identifies the reflectors
including their units. The normalized comparison is unique by the reflector Hom
bijection, so it equals the inverse of pbcScalarCompletionIso. This works on every
ambient complex, without boundedness or completeness of that complex. -/
theorem rationalScalarCompletionKappa_unit (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (N : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E L i W).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app N) ≫
      (rationalScalarCompletionKappa l E L i W).hom.app N =
    (pbcActualCompletionUnit (pbcIntegralDatum l L) W).app
      ((pbcEmbeddingAmbientTensor l E L i W).obj N) := by
  have h := (pbcScalarCompletionIso_exists l E L i W).exists.choose_spec N
  change _ ≫ (pbcScalarCompletionIso l E L i W).inv.app N = _
  apply (cancel_mono ((pbcScalarCompletionIso l E L i W).hom.app N)).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    pbcScalarCompletionIso] using h.symm

variable {X Y : Scheme.{u}}

/-- The completed square preserves the specified quotient-tower units, not merely objects.
The second equality records the reflected-square formula and the third records the
common intermediate expression after the specified unit identifications.
Source: Stacks 0A0E, 0A0G and 099N
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node steps 3--5: the coefficient square commutes after every finite projection,
hence at the limit. Flat-term K-flat tensor balancing yields ordinary beta. The
canonical derived adjunctions have complete-preserving right adjoints and their
unit-normalized direct-image/completion comparisons by ringed-pushforward-completion.
Apply reflected-adjunction-coefficient-squares with delta=beta inverse and the two
kappas from step 2. Its inverse is kappa followed by completion of beta, as displayed.
The ambient quotient comparison preserves the actual augmentation, identifying the
strict units with reflector units. Substitute the kappa-unit equation. Naturality
of the target reflector unit gives the final equality with the intermediate map.
Conjugate back through the two specified quotient isomorphisms to obtain the first
strict-unit equation. This proves equality of actual arrows on all ambient inputs. -/
theorem rationalScalarCompletionUnitSquare
    [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (g : X ⟶ Y) (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    ((pbcEmbeddingAmbientTensor l E L i X).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K) ≫
      (rationalScalarStrictBeta l E L i g).hom.app K =
        (rationalScalarOrdinaryBeta l E L i g).hom.app K ≫
          (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l L) g).app
            ((pbcEmbeddingAmbientTensor l E L i Y).obj K)) ∧
    ((rationalScalarReflectedBeta l E L i g).hom.app K =
      (rationalScalarCompletionKappa l E L i X).hom.app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) ≫
        (pbcActualCompletion (pbcIntegralDatum l L) X).map
          ((rationalScalarOrdinaryBeta l E L i g).hom.app K)) ∧
    ((pbcEmbeddingAmbientTensor l E L i X).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K) ≫
      (rationalScalarStrictBeta l E L i g).hom.app K ≫
      (pbcActualAmbientCompletedPullbackIso (pbcIntegralDatum l L) g).hom.app
        ((pbcEmbeddingAmbientTensor l E L i Y).obj K) =
      (pbcActualCompletionUnit (pbcIntegralDatum l L) X).app
          ((pbcEmbeddingAmbientTensor l E L i X).obj
            ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) ≫
        (pbcActualCompletion (pbcIntegralDatum l L) X).map
          ((rationalScalarOrdinaryBeta l E L i g).hom.app K)) := by
  let CE := pbcEmbeddingAmbientTensor l E L i X
  let CY := pbcEmbeddingAmbientTensor l E L i Y
  let dE := pbcIntegralDatum l E
  let dL := pbcIntegralDatum l L
  let eE := pbcActualAmbientCompletedPullbackIso dE g
  let eL := pbcActualAmbientCompletedPullbackIso dL g
  let β := (rationalScalarOrdinaryBeta l E L i g).hom.app K
  let Λ := pbcActualCompletion dL X
  let η := pbcActualCompletionUnit dL X
  have he (N : PbcCompletedDerived Y dE) :
      (pbcActualStrictCompletedPullUnit dE g).app N ≫ eE.hom.app N =
        (pbcActualCompletedPullUnit g dE).app N :=
    (pbcActualAmbientCompletedPullback_tower dE g).exists.choose_spec N
  have hl : (pbcActualStrictCompletedPullUnit dL g).app (CY.obj K) ≫
      eL.hom.app (CY.obj K) = (pbcActualCompletedPullUnit g dL).app (CY.obj K) :=
    (pbcActualAmbientCompletedPullback_tower dL g).exists.choose_spec (CY.obj K)
  have hf : (rationalScalarReflectedBeta l E L i g).hom.app K =
      (rationalScalarCompletionKappa l E L i X).hom.app
          ((pbcActualDerivedPull g dE).obj K) ≫ Λ.map β := by
    dsimp only [β, Λ, dE]
    unfold rationalScalarReflectedBeta pbcScalarCompletedPullIso
      rationalScalarCompletionKappa rationalScalarOrdinaryBeta
    rfl
  have hs : CE.map ((pbcActualStrictCompletedPullUnit dE g).app K) ≫
        (rationalScalarStrictBeta l E L i g).hom.app K ≫ eL.hom.app (CY.obj K) =
      CE.map ((pbcActualCompletedPullUnit g dE).app K) ≫
        (rationalScalarReflectedBeta l E L i g).hom.app K := by
    simp only [rationalScalarStrictBeta, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Category.assoc]
    change CE.map ((pbcActualStrictCompletedPullUnit dE g).app K) ≫
      (CE.map (eE.hom.app K) ≫
        (rationalScalarReflectedBeta l E L i g).hom.app K ≫
          eL.inv.app (CY.obj K) ≫ eL.hom.app (CY.obj K)) = _
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rw [← Category.assoc, ← CE.map_comp, he]
  have hm : CE.map ((pbcActualStrictCompletedPullUnit dE g).app K) ≫
        (rationalScalarStrictBeta l E L i g).hom.app K ≫ eL.hom.app (CY.obj K) =
      η.app (CE.obj ((pbcActualDerivedPull g dE).obj K)) ≫ Λ.map β := by
    rw [hs, hf, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ Λ.map β)
      (rationalScalarCompletionKappa_unit l E L i X
        ((pbcActualDerivedPull g dE).obj K))
  refine ⟨?_, hf, hm⟩
  apply (cancel_mono (eL.hom.app (CY.obj K))).1
  change (CE.map ((pbcActualStrictCompletedPullUnit dE g).app K) ≫
    (rationalScalarStrictBeta l E L i g).hom.app K) ≫ eL.hom.app (CY.obj K) =
      (β ≫ (pbcActualStrictCompletedPullUnit dL g).app (CY.obj K)) ≫
        eL.hom.app (CY.obj K)
  erw [Category.assoc, hm, Category.assoc, hl]
  exact (η.naturality β).symm

/-- On the completed integral constructible category both actual completion units
are invertible and scalar extension preserves all three membership conditions.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.9
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 6: finite-free constructible scalar transport retains the strata,
bounded perfect models and compatible etale-origin witnesses. Apply ordinary-pullback
preservation in rational-realization-pullback-comparison first to K over E and then
to its scalar extension over L. Both ordinary pullbacks are intrinsically complete.
The same comparison's actual-unit assertion makes both strict quotient units
invertible. All geometric maps are allowed, including maps of empty schemes. -/
theorem rationalScalarCompletionUnitSquare_constructible
    [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (g : X ⟶ Y) (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l L)
        ((pbcEmbeddingAmbientTensor l E L i Y).obj K.obj) ∧
      IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ∧
      IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l L) g).app
        ((pbcEmbeddingAmbientTensor l E L i Y).obj K.obj)) := by
  have hscalar := pbcEmbeddingAmbientTensor_preserves l E L i Y
    (Fact.out : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (Fact.out : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) K
  obtain ⟨sXE⟩ := rationalModuleRealizationFunctor l E X
  obtain ⟨sYE⟩ := rationalModuleRealizationFunctor l E Y
  obtain ⟨sXL⟩ := rationalModuleRealizationFunctor l L X
  obtain ⟨sYL⟩ := rationalModuleRealizationFunctor l L Y
  obtain ⟨aE⟩ := rationalRealizationPullbackComparison l E g sXE sYE
  obtain ⟨aL⟩ := rationalRealizationPullbackComparison l L g sXL sYL
  exact ⟨hscalar, aE.integral.unit_isIso K,
    aL.integral.unit_isIso ⟨_, hscalar⟩⟩

/-- The canonical right adjoint preserves complete objects and its comparison is
normalized by the actual completion units on all ambient inputs.
Source: Stacks 099J and 0A0G
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 4: the coefficient map carries the chosen uniformizer to itself.
Its image ideal is therefore precisely the target principal ideal. Apply the
ringed pushforward/completion theorem to the canonical derived adjunction.
Its preservation clause gives the first assertion. Its unique unit-normalized
comparison is pbcActualDirectCompletionIso, giving the displayed second assertion. -/
theorem rationalScalarCompletionRightAdjoint
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))] :
    (∀ M : PbcCompletedDerived X (pbcIntegralDatum l F),
      PbcIsIntrinsicallyComplete X (pbcIntegralDatum l F) M →
        PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l F)
          ((pbcActualDerivedPush g (pbcIntegralDatum l F)).obj M)) ∧
    ∀ M : PbcCompletedDerived X (pbcIntegralDatum l F),
      (pbcActualCompletionUnit (pbcIntegralDatum l F) Y).app
          ((pbcActualDerivedPush g (pbcIntegralDatum l F)).obj M) ≫
        (pbcActualDirectCompletionIso g (pbcIntegralDatum l F)).hom.app M =
      (pbcActualDerivedPush g (pbcIntegralDatum l F)).map
        ((pbcActualCompletionUnit (pbcIntegralDatum l F) X).app M) := by
  let d := pbcIntegralDatum l F
  constructor
  · intro M hM
    have : IsIso ((pbcActualCompletionUnit d X).app M) :=
      actualCompletion_unit_iso d X M hM
    have h := (pbcActualDirectCompletionIso_exists g d).exists.choose_spec M
    have : IsIso ((pbcActualCompletionUnit d Y).app
        ((pbcActualDerivedPush g d).obj M) ≫
        (pbcActualDirectCompletionIso g d).hom.app M) := by
      change IsIso (_ ≫ (pbcActualDirectCompletionIso_exists g d).exists.choose.hom.app M)
      rw [h]
      infer_instance
    have : IsIso ((pbcActualCompletionUnit d Y).app
        ((pbcActualDerivedPush g d).obj M)) :=
      IsIso.of_isIso_comp_right _ ((pbcActualDirectCompletionIso g d).hom.app M)
    exact (actualComplete_iso Y d (asIso ((pbcActualCompletionUnit d Y).app
      ((pbcActualDerivedPush g d).obj M)))).mpr (actualCompletion_complete d Y _)
  · intro M
    exact (pbcActualDirectCompletionIso_exists g d).exists.choose_spec M

/-- At the identity coefficient extension kappa is the tensor-unitor comparison.
Source: Stacks 0A0E (blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node steps 2 and 7: the ordinary identity scalar comparison is multiplication.
Naturality of that unitor and the completion unit show that the displayed composite
has the kappa-unit normalization. The reflector Hom bijection proves uniqueness,
so it is precisely kappa, on arbitrary ambient inputs. -/
theorem rationalScalarCompletionKappa_identity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (M : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (rationalScalarCompletionKappa l E E (AlgHom.id ℚ_[l] E) W).hom.app M =
      (pbcEmbeddingAmbientUnit l E W).hom.app
          ((pbcActualCompletion (pbcIntegralDatum l E) W).obj M) ≫
        (pbcActualCompletion (pbcIntegralDatum l E) W).map
          ((pbcEmbeddingAmbientUnit l E W).inv.app M) := by
  exact completionUnitor _ _ (pbcActualCompletionUnit (pbcIntegralDatum l E) W)
    (pbcEmbeddingAmbientUnit l E W)
    (rationalScalarCompletionKappa l E E (AlgHom.id ℚ_[l] E) W)
    (rationalScalarCompletionKappa_unit l E E (AlgHom.id ℚ_[l] E) W) M
    (actualReflection (pbcIntegralDatum l E) W M _
      (actualCompletion_complete (pbcIntegralDatum l E) W _)).injective

/-- Coherence of the specified completion comparison under canonical pasting.
The equation uses the published orientation inverse to beta and kappa; inversion
therefore gives the same law for rationalScalarReflectedBeta and kappa.
Source: Stacks 0A0E, 0A0G and the finite scalar-extension construction
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 7: ordinary tensor comparison obeys geometric composition and
coefficient balancing on flat-term K-flat representatives. Completion comparison
preserves the actual units. Precomposing both candidate pasted maps with that unit
reduces to the same ordinary comparison and balanced tensor associator. The complete
output and reflector Hom bijection cancel the unit. Identity gives the unitor law;
binary composition iterates to every geometric or finite coefficient tower, with
arbitrary positive ramification indices. The specified quotient-unit comparison
transports the identical laws to rationalScalarStrictBeta. -/
theorem rationalScalarCompletionUnitSquare_identity (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    (pbcScalarCompletedPullIso l E L i (𝟙 W)).hom.app K.obj ≫
        (pbcEmbeddingAmbientTensor l E L i W).map
          ((pbcActualCompletedPullIdIso (pbcIntegralDatum l E) W).hom.app K) =
      (pbcActualCompletedPullIdIso (pbcIntegralDatum l L) W).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E L i W).obj K.obj,
          pbcScalarPreservesComplete l E L i W K⟩ := by
  exact pbcScalarCompletedPull_identity l E L i W K

/-- Coherence of the specified completion comparison under canonical pasting.
The equation uses the published orientation inverse to beta and kappa; inversion
therefore gives the same law for rationalScalarReflectedBeta and kappa.
Source: Stacks 0A0E, 0A0G and the finite scalar-extension construction
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 7: ordinary tensor comparison obeys geometric composition and
coefficient balancing on flat-term K-flat representatives. Completion comparison
preserves the actual units. Precomposing both candidate pasted maps with that unit
reduces to the same ordinary comparison and balanced tensor associator. The complete
output and reflector Hom bijection cancel the unit. Identity gives the unitor law;
binary composition iterates to every geometric or finite coefficient tower, with
arbitrary positive ramification indices. The specified quotient-unit comparison
transports the identical laws to rationalScalarStrictBeta. -/
theorem rationalScalarCompletionUnitSquare_comp (g : X ⟶ Y)
    {Z : Scheme.{u}} (h : Z ⟶ X) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))] [IsNoetherian Z]
    [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
    [Fact (∀ x : Z, IsUnit (l : Z.presheaf.stalk x))]
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) :
    (pbcActualCompletedPull h (pbcIntegralDatum l L)).map
        ((pbcScalarCompletedPullIso l E L i g).hom.app K.obj) ≫
      (pbcScalarCompletedPullIso l E L i h).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj) =
    (pbcActualCompletedPullCompIso h g (pbcIntegralDatum l L)).hom.app
        ⟨(pbcEmbeddingAmbientTensor l E L i Y).obj K.obj,
          pbcScalarPreservesComplete l E L i Y K⟩ ≫
      (pbcScalarCompletedPullIso l E L i (h ≫ g)).hom.app K.obj ≫
      (pbcEmbeddingAmbientTensor l E L i Z).map
        ((pbcActualCompletedPullCompIso h g (pbcIntegralDatum l E)).inv.app K) := by
  exact pbcScalarCompletedPull_comp l E L i g h K

/-- Coherence of the specified completion comparison under canonical pasting.
The equation uses the published orientation inverse to beta and kappa; inversion
therefore gives the same law for rationalScalarReflectedBeta and kappa.
Source: Stacks 0A0E, 0A0G and the finite scalar-extension construction
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 7: ordinary tensor comparison obeys geometric composition and
coefficient balancing on flat-term K-flat representatives. Completion comparison
preserves the actual units. Precomposing both candidate pasted maps with that unit
reduces to the same ordinary comparison and balanced tensor associator. The complete
output and reflector Hom bijection cancel the unit. Identity gives the unitor law;
binary composition iterates to every geometric or finite coefficient tower, with
arbitrary positive ramification indices. The specified quotient-unit comparison
transports the identical laws to rationalScalarStrictBeta. -/
theorem rationalScalarCompletionKappa_coefficients
    (G : Type u) [Field G] [Algebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (j : L →ₐ[ℚ_[l]] G) (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (pbcScalarCompletionIso l L G j W).hom.app
        ((pbcEmbeddingAmbientTensor l E L i W).obj K) ≫
      (pbcEmbeddingAmbientTensor l L G j W).map
        ((pbcScalarCompletionIso l E L i W).hom.app K) ≫
      (pbcAmbientScalarComp l E L G i j W).hom.app
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) =
    (pbcActualCompletion (pbcIntegralDatum l G) W).map
        ((pbcAmbientScalarComp l E L G i j W).hom.app K) ≫
      (pbcScalarCompletionIso l E G (j.comp i) W).hom.app K := by
  exact pbcScalarCompletion_coefficients l E L i G j W K

/-- Coherence of the specified completion comparison under canonical pasting.
The equation uses the published orientation inverse to beta and kappa; inversion
therefore gives the same law for rationalScalarReflectedBeta and kappa.
Source: Stacks 0A0E, 0A0G and the finite scalar-extension construction
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 7: ordinary tensor comparison obeys geometric composition and
coefficient balancing on flat-term K-flat representatives. Completion comparison
preserves the actual units. Precomposing both candidate pasted maps with that unit
reduces to the same ordinary comparison and balanced tensor associator. The complete
output and reflector Hom bijection cancel the unit. Identity gives the unitor law;
binary composition iterates to every geometric or finite coefficient tower, with
arbitrary positive ramification indices. The specified quotient-unit comparison
transports the identical laws to rationalScalarStrictBeta. -/
theorem rationalScalarCompletionUnitSquare_coefficients (g : X ⟶ Y) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
    (G : Type u) [Field G] [Algebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (j : L →ₐ[ℚ_[l]] G)
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l L G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E L i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l L G j X).map
        ((pbcScalarCompletedPullIso l E L i g).hom.app K) ≫
      (pbcAmbientScalarComp l E L G i j X).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualCompletedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E L G i j Y).hom.app K) ≫
      (pbcScalarCompletedPullIso l E G (j.comp i) g).hom.app K := by
  exact pbcScalarCompletedPull_coefficients l E L i g G j K

/-- The ordinary comparison is the balanced map on tensor generators.
Here r is the intermediate E coefficient, s the final L coefficient, and m
an inverse-image generator; the formula is s tensor r tensor m to s i(r) tensor m.
Source: Stacks 07A4, 0G7E and 0D6D
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 3: finite projections prove the completed coefficient square.
The two adjunction-conjugate ordinary pullbacks flatten to tensor over the pulled
E coefficient ring. Flattening multiplies the two coefficient sections. Insertion
of one gives its inverse. These balanced section maps commute with restrictions
and sheafification. The ordinary adjunction's unit is exactly insertion of one,
so its unique left-adjoint comparison is precisely this balanced map. -/
theorem rationalScalarOrdinaryBeta_tensor (g : X ⟶ Y) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
    (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (V : Y.ProEt) (m : M.val.obj (op V))
    (r : (pbcAdicCompletion X (pbcIntegralDatum l E)).obj.obj
      (op ((proEtaleBaseChange g).obj V)))
    (s : (pbcAdicCompletion X (pbcIntegralDatum l L)).obj.obj
      (op ((proEtaleBaseChange g).obj V))) :
    ((pbcActualScalarOrdinaryPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l L)
        (pbcScalarCoefficientMap l E L i Y) (pbcScalarCoefficientMap l E L i X)
        (pbcScalarCoefficientStructureSquare l E L i g)).inv.app M).val.app
        (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (pbcScalarCoefficientMap l E L i X)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) s
        (r • @id
          (((pbcActualModulePull g (pbcIntegralDatum l E)).obj M).val.obj
            (op ((proEtaleBaseChange g).obj V)))
          (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m))) =
    (s * (pbcScalarCoefficientMap l E L i X).hom.app
        (op ((proEtaleBaseChange g).obj V)) r) •
      @id
        (((pbcActualModulePull g (pbcIntegralDatum l L)).obj
          ((pbcExtend (pbcScalarCoefficientMap l E L i Y)).obj M)).val.obj
            (op ((proEtaleBaseChange g).obj V)))
        (pbcActualModuleUnitSection g (pbcIntegralDatum l L)
          ((pbcExtend (pbcScalarCoefficientMap l E L i Y)).obj M) V
          (pbcTensorSection (pbcScalarCoefficientMap l E L i Y) M (op V) 1 m)) := by
  let dE := pbcIntegralDatum l E
  let dL := pbcIntegralDatum l L
  let φY := pbcScalarCoefficientMap l E L i Y
  let φX := pbcScalarCoefficientMap l E L i X
  let hφ := pbcScalarCoefficientStructureSquare l E L i g
  let δ := pbcActualScalarRightIso g dE dL φY φX hφ
  let α := pbcActualScalarOrdinaryPullIso g dE dL φY φX hφ
  let a := (pbcScalarAdjunction φY).comp (pbcActualModuleAdjunction g dL)
  let b := (pbcActualModuleAdjunction g dE).comp (pbcScalarAdjunction φX)
  have hu := unit_conjugateEquiv_symm a b δ.hom M
  have hv := congrArg (fun f ↦ f.val.app (op V) m) hu
  simp only [a, b, Adjunction.comp_unit_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
  erw [(pbcActualScalarRightIso_exists g dE dL φY φX hφ).exists.choose_spec] at hv
  change ((pbcActualModuleAdjunction g dL).unit.app ((pbcExtend φY).obj M)).val.app
      (op V) (((pbcScalarAdjunction φY).unit.app M).val.app (op V) m) =
    (α.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (((pbcScalarAdjunction φX).unit.app ((pbcActualModulePull g dE).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((pbcActualModuleAdjunction g dE).unit.app M).val.app (op V) m)) at hv
  erw [(pbcScalarAdjunction_exists φY).exists.choose_spec,
    (pbcActualModuleAdjunction_exists g dL).exists.choose_spec,
    (pbcActualModuleAdjunction_exists g dE).exists.choose_spec,
    (pbcScalarAdjunction_exists φX).exists.choose_spec] at hv
  let U := op ((proEtaleBaseChange g).obj V)
  let N := (pbcActualModulePull g dE).obj M
  let x : N.val.obj U := pbcActualModuleUnitSection g dE M V m
  have hr : pbcTensorSection φX N U 1 (r • x) =
      (φX.hom.app U r) • pbcTensorSection φX N U 1 x := by
    have h := (((pbcScalarAdjunction φX).unit.app N).val.app U).hom.map_smul r x
    erw [(pbcScalarAdjunction_exists φX).exists.choose_spec,
      (pbcScalarAdjunction_exists φX).exists.choose_spec] at h
    exact h
  have ht : pbcTensorSection φX N U s (r • x) =
      s • pbcTensorSection φX N U 1 (r • x) := by
    simpa only [pbcTensorSection, mul_one] using
      completedTensor_smul X φX N U s 1 (r • x)
  change (α.inv.app M).val.app U (pbcTensorSection φX N U s (r • x)) = _
  rw [ht, hr, _root_.map_smul, _root_.map_smul, ← hv, mul_smul]
  rfl

/-- The ordinary derived comparison is fixed by its balanced flat-term K-flat model.
Source: Stacks 07A4, 0G7E and 0D6D
(blueprint: lem-per-rational-scalar-completion-unit-square).

Proof, node step 3: ordinary scalar extension and pullback preserve the resolving
class. Their universal computation counits are isomorphisms there. Conjugate the
balanced ordinary chain comparison by these counits and descend through resolving
quasi-isomorphisms. Uniqueness of this representative normalization is the recorded
ringed-topoi tensor/pullback comparison, so it is exactly ordinary beta inverse. -/
theorem rationalScalarOrdinaryBeta_representative (g : X ⟶ Y) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion Y (pbcIntegralDatum l E)) (P.X n)) :
    (rationalScalarOrdinaryBeta l E L i g).inv.app (DerivedCategory.Q.obj P) ≫
        (pbcEmbeddingAmbientTensor l E L i X).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (pbcScalarCoefficientMap l E L i X)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (pbcActualDerivedPull g (pbcIntegralDatum l L)).map
          (pbcComplexCounit (pbcScalarCoefficientMap l E L i Y) P) ≫
        pbcActualPullComplexCounit g (pbcIntegralDatum l L)
          (((pbcExtend (pbcScalarCoefficientMap l E L i Y)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((pbcActualScalarOrdinaryPullComplexIso g (pbcIntegralDatum l E)
            (pbcIntegralDatum l L) (pbcScalarCoefficientMap l E L i Y)
            (pbcScalarCoefficientMap l E L i X)
            (pbcScalarCoefficientStructureSquare l E L i g)).hom.app P) := by
  change (pbcScalarOrdinaryPullIso l E L i g).hom.app _ ≫ _ ≫ _ = _
  unfold pbcScalarOrdinaryPullIso pbcActualScalarDerivedPullIso
  exact (pbcActualScalarDerivedPullIso_exists g (pbcIntegralDatum l E)
    (pbcIntegralDatum l L) (pbcScalarCoefficientMap l E L i Y)
    (pbcScalarCoefficientMap l E L i X)
    (pbcScalarCoefficientStructureSquare l E L i g)).exists.choose_spec P hP hflat

end AlgebraicGeometry.Scheme
