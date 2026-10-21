/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Paper.FiniteReductionRestrictTensor
import Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction

/-!
# Bounded etale witnesses for finite reduction and open extension

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 07A4 and 0G7E;
blueprint, compact-support coefficient change, bounded-domain calculation
(blueprint: lem-fix-reduction-open-etale-origin).

The comparisons are the published B-linear scalar comparison and the exact open
comparison. All coefficients use the canonical lift to the small sites' module universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.FiniteReductionOrigin

/-- The actual finite-level coefficient ring, in the small sites' coefficient universe.
Source: blueprint finite-field datum (blueprint: lem-fix-reduction-open-etale-origin). -/
abbrev coefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)

/-- The quotient map induced by the inclusion of powers of the uniformizer ideal.
Source: blueprint finite coefficient reduction
(blueprint: lem-fix-reduction-open-etale-origin). -/
def coefficientMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n) : coefficient l E n →+* coefficient l E m :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

/-- Exact comparison inverse image on the ordinary derived categories.
Source: Stacks 099R (blueprint: lem-fix-reduction-open-etale-origin). -/
abbrev nu (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- Exact etale open extension, applied degreewise before localization.
Source: Stacks 03S2 (blueprint: lem-fix-reduction-open-etale-origin). -/
abbrev etaleOpen (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- Exact pro-etale open extension, applied degreewise before localization.
Source: Stacks 09AF (blueprint: lem-fix-reduction-open-etale-origin). -/
abbrev proEtaleOpen (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- The exact descent of the canonical sheaf comparison for open extension.
Source: Stacks 09AF (blueprint: lem-fix-reduction-open-etale-origin). -/
def openComparison (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    etaleOpen A j ⋙ nu A Z ≅ nu A X ⋙ proEtaleOpen A j :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical B-linear comparison for coefficient reduction of an etale antecedent.
Source: Stacks 07A4, 06YY (blueprint: lem-fix-reduction-open-etale-origin). -/
def reductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X : Scheme.{u}} {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B X).obj ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj Ke) ≅
      (@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).obj K :=
  (pbcComparisonReduction.{u} X φ).symm.app Ke ≪≫
    (@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).mapIso α

/-- Open extension of the specified origin isomorphism.
Source: Stacks 09AF (blueprint: lem-fix-reduction-open-etale-origin). -/
def openOriginComparison {A : Type (u + 1)} [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu A Z).obj ((etaleOpen A j).obj Ke) ≅ (proEtaleOpen A j).obj K :=
  (openComparison A j).app Ke ≪≫ (proEtaleOpen A j).mapIso α

/-- The canonical B-linear open-reduction comparison. First commute etale scalar
extension with open extension, then use the open site comparison and the scalar site
comparison. This is the same balanced-tensor comparison as the pro-etale open route.
Source: Stacks 07A4, 09AF (blueprint: lem-fix-reduction-open-etale-origin). -/
def openReductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B Z).obj ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj
      ((etaleOpen A j).obj Ke)) ≅
    (proEtaleOpen B j).obj ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).obj K) :=
  (nu B Z).mapIso ((Etale.openScalarExtension φ j).app Ke) ≪≫
    (openComparison B j).app ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj Ke) ≪≫
    (proEtaleOpen B j).mapIso (reductionComparison φ α)

private theorem scalar_bound
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (a b : ℤ) (ht : _root_.DerivedCategory.torAmplitudeIn _ a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a b
      ((pbcFixedScalarExtension.{u} J φ).obj K) := by
  let E := AlgebraicGeometry.FiniteReduction.extend J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U := AlgebraicGeometry.FiniteReduction.extendAdjunction J φ
  have : E.Additive := adj.left_adjoint_additive
  have : E.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight E U
      (AlgebraicGeometry.FiniteReduction.extend_restrict_tensor J φ) f hP hQ
  obtain ⟨P, hPa, hPb, hPf, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht
  have hP := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hPf
  let ad := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)
  let ε := (ad.homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))
  have : HasExactColimitsOfShape ℤ (Sheaf J (ModuleCat.{u + 1} A)) :=
    HasExactColimitsOfShape.of_domain_equivalence _ (AsSmall.equiv (C := ℤ)).symm
  have : IsIso ε := Adjunction.isIso_cochainTranspose_of_kFlat E U adj ad P hP
  let Pe := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hPe : _root_.DerivedCategory.homologyConcentratedIn a b
      (_root_.DerivedCategory.Q.obj Pe) := ⟨inferInstance, inferInstance⟩
  exact (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
    ((asIso ε).symm ≪≫ (pbcFixedScalarExtension.{u} J φ).mapIso e) hPe

private theorem bounded_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hc : ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (hb : _root_.DerivedCategory.TStructure.t.bounded K) :
    ∃ Ke : Etale.DerivedCategoryModule A X,
      Etale.DerivedCategory.isBoundedConstructible A X Ke ∧ Nonempty ((nu A X).obj Ke ≅ K) := by
  have hc' (q : ℤ) : IsConstructible A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
    obtain ⟨S, _, _, hS⟩ := hc q
    exact ⟨S, fun i ↦ Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)⟩
  have ho (q : ℤ) := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hc' q)
  obtain ⟨Ke, hKe, ⟨α⟩⟩ := DerivedCategory.boundedConstructible_of_homology A hb ho
  refine ⟨Ke, ⟨?_, ?_⟩, ⟨α⟩⟩
  · intro q
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hKe.2 q)
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hKe.1
    refine ⟨min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff Ke a).mp ha q
        (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff Ke b).mp hb q hq

/-- Bounded reduction and open-extension antecedents, with their specified B-linear
origin isomorphisms and the bounds on the underlying A-complexes.
Source: Stacks 06YY, 07A4 and 0G7E, bounded-domain calculation
(blueprint: lem-fix-reduction-open-etale-origin).

Proof:
1. Convert intrinsic constructibility on each stratum to finite constant models, then
use fixed-module constructible sheaf descent and bounded constructible derived descent.
Translate the resulting etale constructibility predicate to the recorded finite-value one.
2. A complex of Tor amplitude [a,b] has a flat model supported in [a,b]. This bounded
flat model is K-flat. Sheafified scalar extension followed by restriction is ordinary
tensor with the constant target module, so scalar extension preserves K-flat
quasi-isomorphisms. The transpose of the ordinary unit computes the chosen left adjoint
to exact derived scalar restriction on this model. Scalar extension preserves its
zero terms, proving the same [a,b] bound over B, without flatness of A to B.
3. Compose the published B-linear coefficient comparison with scalar extension of alpha.
Exact faithful site comparison reflects homology vanishing, giving the etale bound.
4. Exact open extension preserves boundedness and homology concentration. Commute etale
scalar extension with open extension, then use the canonical open and scalar site
comparisons. Faithful comparison again reflects the resulting [a,b] bound.
5. Exact restriction preserves boundedness. Package the two bounded etale complexes
with the displayed canonical isomorphisms as the requested fixed-origin witnesses. -/
theorem reduction_open_etale_origin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (coefficient l E n))))
    (_hc : ∀ q : ℤ, @Scheme.IsConstructibleProEtaleFixedModuleSheaf X
      (coefficient l E n) _
      (Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)))
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (_hb : _root_.DerivedCategory.TStructure.t.bounded K)
    (a b : ℤ) (_hab : a ≤ b)
    (_ht : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (coefficient l E n)) X a b K) :
    ∃ Ke : Etale.DerivedCategoryModule (coefficient l E n) X,
      @Etale.DerivedCategory.isBoundedConstructible (coefficient l E n) _
        (Equiv.ulift.finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn))) X Ke ∧
      ∃ α : (nu (coefficient l E n) X).obj Ke ≅ K,
        _root_.DerivedCategory.TStructure.t.bounded Ke ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((etaleOpen (coefficient l E n) j).obj Ke) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj Ke) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj
            ((etaleOpen (coefficient l E n) j).obj Ke)) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj Ke) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj
            ((etaleOpen (coefficient l E n) j).obj Ke)) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj
              Ke)) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((Sheaf.derivedRestrictScalars Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj
              ((etaleOpen (coefficient l E n) j).obj Ke))) ∧
        ∃ (hx : _root_.DerivedCategory.TStructure.t.plus
            ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
              _ _ inferInstance inferInstance
              (coefficientMap l E m n hmn)).obj K))
          (hz : _root_.DerivedCategory.TStructure.t.plus
            ((proEtaleOpen (coefficient l E m) j).obj
              ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
              _ _ inferInstance inferInstance
                (coefficientMap l E m n hmn)).obj K)))
          (wx : Scheme.FixedEtaleOriginWitness X (coefficient l E m)
            ⟨(@pbcFixedScalarExtension.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
              _ _ inferInstance inferInstance
              (coefficientMap l E m n hmn)).obj K, hx⟩)
          (wz : Scheme.FixedEtaleOriginWitness Z (coefficient l E m)
            ⟨(proEtaleOpen (coefficient l E m) j).obj
              ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
              (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
              _ _ inferInstance inferInstance
                (coefficientMap l E m n hmn)).obj K), hz⟩),
          wx.complex.obj =
            (@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj Ke ∧
          HEq wx.iso (reductionComparison (coefficientMap l E m n hmn) α) ∧
          wz.complex.obj =
            (@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance (coefficientMap l E m n hmn)).obj
              ((etaleOpen (coefficient l E n) j).obj Ke) ∧
          HEq wz.iso (openReductionComparison (coefficientMap l E m n hmn) j α) ∧
          Nonempty ((nu (coefficient l E n) Z).obj
            ((etaleOpen (coefficient l E n) j).obj Ke) ≅
              (proEtaleOpen (coefficient l E n) j).obj K) := by
  let : Finite (coefficient l E n) := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn))
  obtain ⟨Ke, hcKe, ⟨α⟩⟩ := bounded_origin (coefficient l E n) X K _hc _hb
  let A := coefficient l E n
  let B := coefficient l E m
  let φ := coefficientMap l E m n hmn
  let : Finite B := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E m hm)
  have hKe : _root_.DerivedCategory.TStructure.t.bounded Ke := by
    obtain ⟨a', b', _, hz⟩ := hcKe.2
    exact ⟨⟨a', (_root_.DerivedCategory.isGE_iff Ke a').mpr
      (fun q hq ↦ hz q (Or.inl hq))⟩,
      ⟨b', (_root_.DerivedCategory.isLE_iff Ke b').mpr
        (fun q hq ↦ hz q (Or.inr hq))⟩⟩
  have hOpen := Functor.bounded_mapDerivedCategory_obj
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j) hKe
  have hred := scalar_bound (Scheme.ProEt.topology X) φ K a b _ht
  have hredEt : _root_.DerivedCategory.homologyConcentratedIn a b
      ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj Ke) :=
    Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (comparisonUpperStar (ModuleCat.{u + 1} B) X)
        ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
          (reductionComparison φ α).symm hred)
  have hopenRed := Functor.homologyConcentratedIn_mapDerivedCategory_obj
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j) hred
  have hopenRedEt : _root_.DerivedCategory.homologyConcentratedIn a b
      ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj ((etaleOpen A j).obj Ke)) :=
    Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (comparisonUpperStar (ModuleCat.{u + 1} B) Z)
        ((_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
          (openReductionComparison φ j α).symm hopenRed)
  have hbe := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
    ⟨a, b, hredEt⟩
  have hbze := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
    ⟨a, b, hopenRedEt⟩
  have hbr := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
    ⟨a, b, hred⟩
  have hbo := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).mp
    ⟨a, b, hopenRed⟩
  refine ⟨Ke, hcKe, α, hKe, hOpen, hbe, hbze, hredEt, hopenRedEt,
    (Sheaf.restrictScalars X.smallEtaleTopology φ).bounded_mapDerivedCategory_obj hbe,
    (Sheaf.restrictScalars Z.smallEtaleTopology φ).bounded_mapDerivedCategory_obj hbze,
    hbr.1, hbo.1, ?_⟩
  refine ⟨⟨⟨_, hbe.1⟩, reductionComparison φ α⟩,
    ⟨⟨_, hbze.1⟩, openReductionComparison φ j α⟩, rfl, HEq.rfl, rfl, HEq.rfl,
    ⟨openOriginComparison j α⟩⟩

end AlgebraicGeometry.ProEtale.FiniteReductionOrigin
