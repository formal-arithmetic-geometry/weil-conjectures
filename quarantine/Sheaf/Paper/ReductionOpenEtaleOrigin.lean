/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.RingedCoefficientPullbackComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero

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
    (nu B X).obj ((pbcFixedScalarExtension X.smallEtaleTopology φ).obj Ke) ≅
      (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj K :=
  (pbcComparisonReduction X φ).symm.app Ke ≪≫
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).mapIso α

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
    (nu B Z).obj ((pbcFixedScalarExtension Z.smallEtaleTopology φ).obj
      ((etaleOpen A j).obj Ke)) ≅
    (proEtaleOpen B j).obj ((pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj K) :=
  (nu B Z).mapIso ((Etale.openScalarExtension φ j).app Ke) ≪≫
    (openComparison B j).app ((pbcFixedScalarExtension X.smallEtaleTopology φ).obj Ke) ≪≫
    (proEtaleOpen B j).mapIso (reductionComparison φ α)

/-- Bounded reduction and open-extension antecedents, with their specified B-linear
origin isomorphisms and the bounds on the underlying A-complexes.
Source: Stacks 06YY, 07A4 and 0G7E, bounded-domain calculation
(blueprint: lem-fix-reduction-open-etale-origin).

Proof:
1. Apply clause (ii) of lem-sf-proetale-constructible-origin to the intrinsic bounded
constructible finite-level complex. This gives Ke and alpha, without Noetherianity.
2. The canonical coefficient/inverse-image comparison is B-linear by
lem-pur-coefficient-pullback-comparison. Compose it with scalar extension of alpha.
3. Resolve by a flat-term K-flat complex (lem-pc-kflat-resolution). By
lem-pur-derived-change-of-rings and lem-pur-change-of-rings-tensor-comparison, its
restricted scalar extension is its A-derived tensor with B. The Tor test at the
sheaf B gives vanishing outside [a,b], with no flatness assumption on A to B.
4. Exact etale open extension preserves boundedness. The degreewise comparison of
lem-cbc-proetale-extension-zero-comparison descends to the displayed open origin
isomorphism; both open extensions and comparison inverse images are exact.
5. The B-linear open scalar comparison of lem-fix-open-scalar-tensor-normalization,
combined with step 2, gives openReductionComparison. Equivalently commute etale
open extension with scalars first, as in its definition. On K-flat representatives
both routes are the same balanced tensor map on the open and zero off the open.
Exact pro-etale open extension preserves the [a,b] bound from step 3.
6. By prop-weil-pbc-site-comparison-finite-level, comparison is exact and its sheaf
unit is invertible. It reflects zero cohomology, hence both etale reductions have
cohomology in [a,b]. Scalar restriction leaves the underlying abelian cohomology
unchanged, proving the two A-boundedness assertions. The retained pairs below are
the specified FixedEtaleOriginWitness objects, with bounded etale antecedents. -/
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
          ((pbcFixedScalarExtension X.smallEtaleTopology (coefficientMap l E m n hmn)).obj Ke) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((pbcFixedScalarExtension Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((etaleOpen (coefficient l E n) j).obj Ke)) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((pbcFixedScalarExtension X.smallEtaleTopology (coefficientMap l E m n hmn)).obj Ke) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((pbcFixedScalarExtension Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((etaleOpen (coefficient l E n) j).obj Ke)) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((pbcFixedScalarExtension X.smallEtaleTopology (coefficientMap l E m n hmn)).obj
              Ke)) ∧
        _root_.DerivedCategory.TStructure.t.bounded
          ((Sheaf.derivedRestrictScalars Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
            ((pbcFixedScalarExtension Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
              ((etaleOpen (coefficient l E n) j).obj Ke))) ∧
        ∃ (hx : _root_.DerivedCategory.TStructure.t.plus
            ((pbcFixedScalarExtension (Scheme.ProEt.topology X)
              (coefficientMap l E m n hmn)).obj K))
          (hz : _root_.DerivedCategory.TStructure.t.plus
            ((proEtaleOpen (coefficient l E m) j).obj
              ((pbcFixedScalarExtension (Scheme.ProEt.topology X)
                (coefficientMap l E m n hmn)).obj K)))
          (wx : Scheme.FixedEtaleOriginWitness X (coefficient l E m)
            ⟨(pbcFixedScalarExtension (Scheme.ProEt.topology X)
              (coefficientMap l E m n hmn)).obj K, hx⟩)
          (wz : Scheme.FixedEtaleOriginWitness Z (coefficient l E m)
            ⟨(proEtaleOpen (coefficient l E m) j).obj
              ((pbcFixedScalarExtension (Scheme.ProEt.topology X)
                (coefficientMap l E m n hmn)).obj K), hz⟩),
          wx.complex.obj =
            (pbcFixedScalarExtension X.smallEtaleTopology (coefficientMap l E m n hmn)).obj Ke ∧
          HEq wx.iso (reductionComparison (coefficientMap l E m n hmn) α) ∧
          wz.complex.obj =
            (pbcFixedScalarExtension Z.smallEtaleTopology (coefficientMap l E m n hmn)).obj
              ((etaleOpen (coefficient l E n) j).obj Ke) ∧
          HEq wz.iso (openReductionComparison (coefficientMap l E m n hmn) j α) ∧
          Nonempty ((nu (coefficient l E n) Z).obj
            ((etaleOpen (coefficient l E n) j).obj Ke) ≅
              (proEtaleOpen (coefficient l E n) j).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteReductionOrigin
