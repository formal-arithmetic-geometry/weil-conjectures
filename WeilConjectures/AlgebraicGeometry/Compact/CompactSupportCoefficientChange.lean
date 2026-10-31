/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.SixFunctors.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Change of finite coefficients for compact support

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-trace-perfectness,
order 1824; Stacks Tags 0GL5 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).

Derived scalar extension is expressed by the published universal property
`Sheaf.IsDerivedBaseChange`. A model includes its universal arrow, so the comparison
below is a unique B-linear arrow, not a lift of an unspecified A-linear arrow.
The actual compact-support functors and proper/open mates are used throughout.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- A presentation of the actual derived scalar extension, including its universal arrow.
The universal property is the published definition of derived base change; it determines
this object up to the unique isomorphism respecting that arrow. K-flat scalar extension
supplies such presentations (lem-pur-derived-change-of-rings).
Source: Stacks Tags 06YY and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
structure CoefficientTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) where
  obj : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B))
  unit : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).obj obj
  universal : Sheaf.IsDerivedBaseChange unit

namespace CoefficientTensorModel

/-- The canonical scalar extension of a map, fixed by the universal arrows.
Source: Stacks Tag 07A6 (blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def map
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B} {T : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (f : K ⟶ L) :
    M.obj ⟶ N.obj :=
  (Equiv.ofBijective _ (M.universal N.obj)).symm (f ≫ N.unit)

/-- The composite universal arrow for successive reductions, with the canonical
restriction-of-scalars associativity map. Source: Stacks Tag 0D6D
(blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* B} {ψ : B →+* C} {T : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel ψ T M.obj) :
    CoefficientTensorModel (ψ.comp φ) T K where
  obj := N.obj
  unit := M.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map N.unit ≫
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) rfl).hom.app N.obj
  universal := M.universal.comp rfl N.universal

/-- Pullback of the universal tensor arrow remains universal.
Source: Stacks Tags 07A4 and 06YY
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: compute scalar extension on a K-flat complex with flat terms. Exact inverse
image preserves these models, and on a pure tensor its coefficient comparison is
f^{-1}(x tensor b) = f^{-1}(x) tensor b. Its transpose is the canonical published
restriction/pullback comparison. This identifies the resulting arrow with the
universal scalar-extension arrow. Localization and the canonical model isomorphisms
give universality for every presentation, without flatness of the coefficient map. -/
theorem pullback_universal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T V : Scheme.{u}} (g : V ⟶ T)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) :
    Sheaf.IsDerivedBaseChange
      ((L((g)^*[ModuleCat.{u + 1} A])).map M.unit ≫
        (fixedScalarRestrictionPullback φ g).hom.app M.obj) := by
  sorry

/-- The canonical pullback of a tensor presentation, with its normalized universal arrow.
Source: Stacks Tag 07A4 (blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T V : Scheme.{u}} (g : V ⟶ T)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) :
    CoefficientTensorModel φ V ((L((g)^*[ModuleCat.{u + 1} A])).obj K) where
  obj := (L((g)^*[ModuleCat.{u + 1} B])).obj M.obj
  unit := (L((g)^*[ModuleCat.{u + 1} A])).map M.unit ≫
    (fixedScalarRestrictionPullback φ g).hom.app M.obj
  universal := M.pullback_universal g

end CoefficientTensorModel

/-- The canonical B-linear coefficient comparison. It is the unique arrow whose
restriction, composed with the source tensor unit, is compact support of the input
unit followed by the canonical proper/open restriction comparison.
This is equivalently the tensor comparison: on the proper factor its transpose is
coefficient extension of the counit, and on the open factor it is the unit mate.
Source: Stacks Tags 0GL5, 0GL6 and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def compactSupportCoefficientComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y ((Rf_!(c)[ModuleCat.{u + 1} A]).obj K)) :
    N.obj ⟶ (Rf_!(c)[ModuleCat.{u + 1} B]).obj M.obj :=
  (Equiv.ofBijective _ (N.universal _)).symm
    ((Rf_!(c)[ModuleCat.{u + 1} A]).map M.unit ≫
      (compactSupportRestrictionIso φ c).hom.app M.obj)

/-- The canonical comparison for the actual quotient A_{E,n} to A_{E,m}. The lift
only places scalars in the standard coefficient universe u+1; no site universe is changed.
Source: Weil blueprint order 1824
(blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def finiteReductionCompactSupportComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))}
    (M : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))) X K)
    (N : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))) Y
      ((Rf_!(c)[ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))]).obj K)) :=
  letI : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn))
  letI : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m hm)
  compactSupportCoefficientComparison c M N

/-- Compact support commutes with reduction A_{E,n} to A_{E,m} for bounded
constructible K of finite Tor amplitude, in the finite-field datum.
The conclusion is an isomorphism in the B-coefficient category, for every universal
presentation of each derived tensor. In particular it includes m=n.
Source: Weil blueprint order 1824; Stacks Tags 0GL5, 0GL6 and 0F0G
(blueprint: lem-fix-compact-support-coefficient-change).
Proof:
1. Compute scalar extension on a K-flat resolution with flat terms
(lem-pur-derived-change-of-rings, lem-pc-kflat-resolution); forgetting its B action
identifies it with the ordinary A-derived tensor
(lem-pur-change-of-rings-tensor-comparison). Its canonical adjunction with exact
restriction is compatible with inverse images and counits
(lem-weil-pbc-ring-sheaf-change-adjunction).
2. Write Rf! = Rp* j! in the fixed compactification. Bounded constructible K has
bounded etale origin (lem-sf-proetale-constructible-origin). Exact extension by zero
preserves this origin. Finite Tor amplitude bounds its tensor with the degree-zero
B sheaf; the open tensor formula gives the same boundedness after j!. Comparison
with the etale site is exact and reflects zero cohomology, so the etale tensors are
also bounded below (lem-cbc-extension-zero-projection-formula,
prop-weil-pbc-site-comparison-finite-level).
3. The proper comparison is the mate of inverse image commuting with coefficient
extension. The restriction/counit adjunct formula identifies its restriction with
the actual A-linear projection arrow. Properness implies qcqs. Apply the unbounded
finite-coefficient etale proper projection formula to j!K and B; it needs no
perfectness or flatness of B over A. The invertible canonical direct-image site
comparisons transport that arrow to the pro-etale site, by ringed exchange/tensor
coherence (lem-etale-proper-projection-formula-finite,
lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-weil-pbc-ringed-exchange-tensor-coherence). Exact scalar restriction reflects
isomorphisms, so the proper comparison is invertible in D(B).
4. The open comparison is the unique unit-normalized adjunction mate, hence an
isomorphism (lem-cbc-proetale-extension-zero). Compose it with the proper comparison.
The canonical compact-support restriction square identifies its adjunct with the
universal-arrow formula defining the comparison above
(lem-sf-compact-support-restriction-of-scalars, def-exchange-projection).
5. On K-flat representatives successive reductions send (x tensor b) tensor c to
x tensor (bar b)c. Mate pasting gives the reduction identity. Pasting the coefficient
square with the geometric proper/open square gives pullback compatibility. The
proper transpose is coefficient extension of the same counit, and the open
transpose is extension of the same unit, giving projection compatibility. The
subsequent declarations state these identities without using faithfulness of
derived scalar restriction (lem-weil-pbc-mate-pasting,
lem-cbc-proetale-extension-zero-base-change, thm-cbc-finite-level-proetale). -/
theorem finiteReductionCompactSupportComparison_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))))
    (_hK : DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X K)
    (M : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))) X K)
    (N : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))) Y
      ((Rf_!(c)[ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))]).obj K)) :
    IsIso (finiteReductionCompactSupportComparison l E m n hm hmn c M N) := by
  sorry

end AlgebraicGeometry.ProEtale
