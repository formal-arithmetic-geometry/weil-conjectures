/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.IntegralHomReduction
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.SfCompleteDirectImageReduction
import WeilConjectures.AlgebraicGeometry.SfDirectImageReductionTransitions
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ConstructibleHomComparison
import WeilConjectures.AlgebraicGeometry.IntrinsicSiteHomTransport
import WeilConjectures.AlgebraicGeometry.EtaleHomFiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.CharP.CharAndCard

/-! # Constructible finite-Tor domains of the tensor exchange

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction, proof Step 2; the detailed finite-affine descent and
uniform integral bounds of the DAG (blueprint: lem-sf-tensor-exchange-ctf-domains).

The small pro-etale site and completed coefficient sheaf are the recorded ones.
No separatedness of a scheme over the base or site-perfectness is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures


attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := proEtaleConstantRing X A
  let C := SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.monoidalCategory R
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  have := SheafOfModules.tensorPreadditive R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

private theorem torAmplitude_of_iso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A L a b) :
    HasProEtaleTorAmplitude X A K a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP M i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e⟩ f hf hP M i hi

private theorem constructible_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)}
    (e : K ≅ L) (h : intrinsicFiniteTorsionConstructible l E n hn X L) :
    intrinsicFiniteTorsionConstructible l E n hn X K := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let W : ObjectProperty (proEtaleDerivedCategory X A) :=
    intrinsicFiniteTorsionConstructible l E n hn X
  have : W.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated X A).1
  exact W.prop_of_iso e.symm h

private theorem iso_exists_of_isIso {C : Type*} [Category C] {X Y : C}
    {f : X ⟶ Y} (h : IsIso f) : Nonempty (X ≅ Y) :=
  ⟨@asIso _ _ _ _ f h⟩

private theorem coefficientPrime_unit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (W : Over (Spec (.of D.k))) (x : W.left) :
    IsUnit (l : W.left.residueField x) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hu : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  let g := W.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  simpa only [map_natCast] using hu.map
    ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
      W.left.Γevaluation x).hom

attribute [-instance] IntegralHom.derivedCategory in
/-- Finite-level internal Hom is bounded constructible with the stated common Tor bound.
Source: tensor-exchange detection, finite-affine descent
(blueprint: lem-sf-tensor-exchange-ctf-domains).

Proof: choose bounded constructible etale origins by
lem-weil-pbc-finite-ring-constructible-derived-origin. Reflect the two exact Tor intervals
using lem-sf-comparison-tor-amplitude(ii). Apply thm-sf-hom-ctf with the supplied dimension
bound: its finite affine cover proof works on nonseparated schemes, with one bound on
all members. The evaluation-defined comparison of thm-sf-hom-comparison-constructible
identifies the ambient pro-etale Hom. Transfer constructibility and the same Tor interval
back by lem-sf-comparison-tor-amplitude(i). Neither input is assumed site-perfect.
The empty affine cover gives the zero object on an empty scheme. -/
theorem tensorExchange_finiteHom_domains
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (d : ℕ) (_hd : topologicalKrullDim W.left ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (P Q : proEtaleDerivedCategory W.left (Padic.coefficientExtensionRing l E n))
    (_hP : finiteTorConstructible l E n hn W.left P)
    (_hQ : finiteTorConstructible l E n hn W.left Q)
    (_hPt : HasProEtaleTorAmplitude W.left (Padic.coefficientExtensionRing l E n) P a b)
    (_hQt : HasProEtaleTorAmplitude W.left (Padic.coefficientExtensionRing l E n) Q c e) :
    intrinsicFiniteTorsionConstructible l E n hn W.left
        ((IntegralHom.hom.{u, u} W.left
          (proEtaleConstantRing W.left (Padic.coefficientExtensionRing l E n))).obj (op P, Q)) ∧
      HasProEtaleTorAmplitude W.left (Padic.coefficientExtensionRing l E n)
        ((IntegralHom.hom.{u, u} W.left
          (proEtaleConstantRing W.left (Padic.coefficientExtensionRing l E n))).obj (op P, Q))
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  let : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} B
  let : ∀ x : W.left, Invertible (l : W.left.residueField x) :=
    fun x ↦ (coefficientPrime_unit D l _hl W x).invertible
  let : LocallyOfFiniteType (W.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType W.hom)
  let : QuasiCompact (W.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact W.hom)
  have origin (S : proEtaleDerivedCategory W.left B)
      (hS : intrinsicFiniteTorsionConstructible l E n hn W.left S) :
      ∃ S₀ : (Etale.DerivedCategory.isBoundedConstructible A W.left).FullSubcategory,
        Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison W.left B).obj
          S₀.obj ≅ S) := by
    obtain ⟨r, hr⟩ := hS.1.bddBelow
    obtain ⟨s, hs⟩ := hS.1.bddAbove
    apply (finiteRing_constructibleDerived_origin W.left B).2.2.1 S |>.mpr
    refine ⟨hS.2, min r s, max r s, min_le_max, ?_⟩
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (hr hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hs hz)) (lt_of_le_of_lt (le_max_right _ _) hi)
  obtain ⟨P₀, ⟨eP⟩⟩ := origin P _hP.1
  obtain ⟨Q₀, ⟨eQ⟩⟩ := origin Q _hQ.1
  have plus (S : (Etale.DerivedCategory.isBoundedConstructible A W.left).FullSubcategory) :
      DerivedCategory.TStructure.t.plus S.obj := by
    obtain ⟨r, s, _, hv⟩ := S.property.2
    exact ⟨r, (DerivedCategory.isGE_iff S.obj r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  have hPt := finiteCoefficient_comparison_reflects_torAmplitude
    D l _hl E n hn W.left a b P₀.obj (plus P₀) P _hP.1 _hPt eP.symm
  have hQt := finiteCoefficient_comparison_reflects_torAmplitude
    D l _hl E n hn W.left c e Q₀.obj (plus Q₀) Q _hQ.1 _hQt eQ.symm
  have hhom := finiteCoefficient_derivedHom_ctf_etale D l _hl E n hn W.left d _hd
    a b c e _hab _hce P₀.obj Q₀.obj
    ⟨P₀.property, a, b, _hab, hPt⟩ ⟨Q₀.property, c, e, _hce, hQt⟩ hPt hQt
  let H := ((Etale.derivedHom (ModuleCat.{u + 1} A) W.left).obj (op P₀.obj)).obj Q₀.obj
  have hC := finiteCoefficient_comparison_preserves_torAmplitude D l _hl E n hn W.left
    (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) (by omega) H hhom.1.1 hhom.2.1
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W.left
  let R := ProEtale.finiteCoefficientIntrinsicRealization W.left B
  let Cp := ProEtale.finiteCoefficientIntrinsicDerivedComparison W.left B
  let eC (S : Etale.DerivedCategoryModule A W.left) :
      Cp.obj S ≅ R.mapDerivedCategory.obj (ν.mapDerivedCategory.obj S) :=
    (Functor.mapDerivedCategoryCompIso ν R).app S
  have hcmp := ProEtale.isIso_comparisonDerivedHom_of_constructible
    D l _hl E ⟨n, hn⟩ W.left P₀.obj Q₀.obj P₀.property ⟨a, b, _hab, hPt⟩ Q₀.property
  obtain ⟨ecmp⟩ := iso_exists_of_isIso hcmp
  obtain ⟨eR⟩ := ProEtale.intrinsicSiteHom_transport W.left B
    (ν.mapDerivedCategory.obj P₀.obj) (ν.mapDerivedCategory.obj Q₀.obj)
  let HP := IntegralHom.hom.{u, u} W.left (proEtaleConstantRing W.left B)
  let iso : Cp.obj H ≅ HP.obj (op P, Q) :=
    eC H ≪≫ R.mapDerivedCategory.mapIso
      ecmp ≪≫ eR ≪≫
      HP.mapIso (Iso.prod ((eC P₀.obj).symm ≪≫ eP).symm.op
        ((eC Q₀.obj).symm ≪≫ eQ))
  exact ⟨constructible_of_iso l E n hn W.left iso.symm hC.1,
    torAmplitude_of_iso W.left B iso.symm _ _ hC.2⟩

/-- Completed integral Hom is complete and constructible finite-Tor; its evaluation
transpose commutes with every positive reduction with one uniform interval.
Source: tensor-exchange detection, integral Hom
(blueprint: lem-sf-tensor-exchange-ctf-domains).

Proof: lem-coef-integral-hom-reduction supplies normalized tensor presentations,
completeness in the second variable and invertibility of the evaluation transpose.
Apply the finite-level assertion at each reduction, using the same dimension and the
two common input intervals. Testing Tor amplitude on the coefficient sheaf gives the
common cohomological interval. Completeness, constructibility and that uniform bound
are def-weil-derived-complete-integral-detailed. The uniform Tor interval is precisely
def-weil-finite-tor-amplitude. Lem-coef-integral-residue-tor identifies the two integral
constructible predicates on this arbitrary finite-type scheme. Empty schemes give zero. -/
theorem tensorExchange_integralHom_domains
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (d : ℕ) (_hd : topologicalKrullDim W.left ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (P Q : DerivedCategory (scalarReductionSource.{u, u} l E W.left))
    (_hP : sfIntegralConstructible l E W.left P)
    (_hQ : sfIntegralConstructible l E W.left Q)
    (_hPt : ∀ n : ℕ, HasProEtaleTorAmplitude W.left
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj P) a b)
    (_hQt : ∀ n : ℕ, HasProEtaleTorAmplitude W.left
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj Q) c e) :
    IsSfDerivedComplete l E W.left
        ((IntegralHom.hom.{u, u} W.left
          (completedIntegralCommRingSheaf l E W.left D hl)).obj (op P, Q)) ∧
      sfIntegralConstructible l E W.left
        ((IntegralHom.hom.{u, u} W.left
          (completedIntegralCommRingSheaf l E W.left D hl)).obj (op P, Q)) ∧
      finiteTorConstructibleIntegral l E W.left
        ((IntegralHom.hom.{u, u} W.left
          (completedIntegralCommRingSheaf l E W.left D hl)).obj (op P, Q)) ∧
      sfIntegralConstructible l E W.left = finiteTorConstructibleIntegral l E W.left ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude W.left
        (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj
          ((IntegralHom.hom.{u, u} W.left
            (completedIntegralCommRingSheaf l E W.left D hl)).obj (op P, Q)))
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))) ∧
      ∃ T : IntegralHom.TensorPresentation.{u, u} W.left
          (completedIntegralCommRingSheaf l E W.left D hl),
        ∀ n : ℕ, ∃ M : IntegralHom.ReductionPresentation l E W.left D hl T n,
          IsIso (IntegralHom.comparison l E W.left D hl M P Q) := by
  classical
  let H := (IntegralHom.hom.{u, u} W.left
    (completedIntegralCommRingSheaf l E W.left D hl)).obj (op P, Q)
  let : ∀ x : W.left, Invertible (l : W.left.residueField x) :=
    fun x ↦ (coefficientPrime_unit D l hl W x).invertible
  obtain ⟨T, hcomplete, hmodels⟩ := integralHomReduction l E W.left D hl
  have hc : IsSfDerivedComplete l E W.left H :=
    (sfDerivedComplete_iff_legacy l E W.left D hl H).mpr
      (hcomplete P Q ((sfDerivedComplete_iff_legacy l E W.left D hl Q).mp _hQ.1))
  have hlevels (n : ℕ) :
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W.left
          ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj H) ∧
        HasProEtaleTorAmplitude W.left (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj H)
          (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
    obtain ⟨M, hM⟩ := hmodels n
    have := (hM P Q).1
    let iso := asIso (IntegralHom.comparison l E W.left D hl M P Q)
    obtain ⟨_, r, s, hrs, hPs⟩ := _hP
    obtain ⟨_, t, v, htv, hQs⟩ := _hQ
    have hfinite := tensorExchange_finiteHom_domains D l hl E (n + 1) (Nat.succ_pos n)
      W d _hd a b c e _hab _hce
      ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj P)
      ((scalarReductionDerivedExtension.{u, u} l E W.left n).obj Q)
      ⟨(hPs n).1, a, b, _hPt n⟩ ⟨(hQs n).1, c, e, _hQt n⟩ (_hPt n) (_hQt n)
    exact ⟨constructible_of_iso l E _ _ W.left iso hfinite.1,
      torAmplitude_of_iso W.left _ iso _ _ hfinite.2⟩
  have hab : c - b - 2 * (d : ℤ) ≤ e - a + 2 * (d : ℤ) := by omega
  have hcon : sfIntegralConstructible l E W.left H :=
    ⟨hc, _, _, hab, fun n ↦ ⟨(hlevels n).1,
      support_of_torAmplitude W.left _ _ _ _ (hlevels n).2⟩⟩
  refine ⟨hc, hcon, ⟨hcon, _, _, hab, fun n ↦ (hlevels n).2⟩,
    (integral_residue_tor D l hl E W.left).2, fun n ↦ (hlevels n).2, T, ?_⟩
  intro n
  obtain ⟨M, hM⟩ := hmodels n
  exact ⟨M, (hM P Q).1⟩

/-- Integral direct image has the uniform Tor and cohomological bounds, and the canonical
projection-adjoint reduction comparisons are isomorphisms respecting quotient transitions.
Source: tensor-exchange detection, integral direct image; Stacks Tags 099N and 0944
(blueprint: lem-sf-tensor-exchange-ctf-domains).

Proof: cor-sf-direct-image-ctf-proetale applies to each reduction of K, with the
same source dimension and Tor interval, giving [a,b+2d]. No separatedness of either
scheme over k is used. Def-weil-derived-direct-image supplies the prescribed finite-image
tower and its Roos projections. Lem-sf-complete-direct-image-reduction proves completeness
and invertibility of each scalar adjunct of a projection. The cone relation between
successive projections gives the transition square, after scalar adjunction and the
canonical successive reduction identifications. Testing the coefficient sheaf gives
the cohomological bound. The defining uniform criterion and lem-coef-integral-residue-tor
then give both integral constructible domains and their equality. Empty schemes are zero. -/
theorem tensorExchange_integralDirectImage_domains
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (_hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X.left))
    (_hK : sfIntegralConstructible l E X.left K)
    (_hKt : ∀ n : ℕ, HasProEtaleTorAmplitude X.left
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension.{u, u} l E X.left n).obj K) a b)
    [HasProduct (sfDirectImageTerm l E f.left K)] (L : SfIntegralDirectImage l E f.left K) :
    IsSfDerivedComplete l E Y.left L.obj ∧
      sfIntegralConstructible l E Y.left L.obj ∧
      finiteTorConstructibleIntegral l E Y.left L.obj ∧
      sfIntegralConstructible l E Y.left = finiteTorConstructibleIntegral l E Y.left ∧
      (∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f.left L n)) ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude Y.left
        (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Y.left n).obj L.obj)
        a (b + 2 * (d : ℤ))) ∧
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y.left n).obj L.obj) ⊆
          Set.Icc a (b + 2 * (d : ℤ))) ∧
      ∀ n : ℕ,
        (scalarReductionDerivedRestriction.{u, u} l E Y.left (n + 1)).map
            (sfDirectImageReductionComparison l E f.left L (n + 1)) ≫
          sfDirectImageTransition l E f.left K n =
        (sfDerivedReductionTransition l E Y.left n).app L.obj ≫
          (scalarReductionDerivedRestriction.{u, u} l E Y.left n).map
            (sfDirectImageReductionComparison l E f.left L n) := by
  classical
  let : ∀ x : Y.left, Invertible (l : Y.left.residueField x) :=
    fun x ↦ (coefficientPrime_unit D l _hl Y x).invertible
  obtain ⟨hc, hred⟩ := sfCompleteDirectImage_reduction l E f.left K _hK.1 L
  obtain ⟨r, s, hrs, hKs⟩ := _hK.2
  have hfinite (n : ℕ) :=
    ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l _hl E (n + 1) (Nat.succ_pos n) X Y f d _hd a b
      (K := (scalarReductionDerivedExtension.{u, u} l E X.left n).obj K)
      ⟨(hKs n).1, a, b, _hKt n⟩ (_hKt n)
  have hlevels (n : ℕ) :
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y.left
          ((scalarReductionDerivedExtension.{u, u} l E Y.left n).obj L.obj) ∧
        HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E Y.left n).obj L.obj)
          a (b + 2 * (d : ℤ)) := by
    have := hred n
    let iso := asIso (sfDirectImageReductionComparison l E f.left L n)
    exact ⟨constructible_of_iso l E _ _ Y.left iso (hfinite n).1,
      torAmplitude_of_iso Y.left _ iso _ _ (hfinite n).2⟩
  have hab : a ≤ b + 2 * (d : ℤ) := by omega
  have hs (n : ℕ) := support_of_torAmplitude Y.left _ _ _ _ (hlevels n).2
  have hcon : sfIntegralConstructible l E Y.left L.obj :=
    ⟨hc, a, b + 2 * (d : ℤ), hab, fun n ↦ ⟨(hlevels n).1, hs n⟩⟩
  refine ⟨hc, hcon, ⟨hcon, a, b + 2 * (d : ℤ), hab, fun n ↦ (hlevels n).2⟩,
    (integral_residue_tor D l _hl E Y.left).2, hred,
    fun n ↦ (hlevels n).2, hs, ?_⟩
  exact sfDirectImageReductionComparison_transition l E f.left K L

end WeilConjectures
