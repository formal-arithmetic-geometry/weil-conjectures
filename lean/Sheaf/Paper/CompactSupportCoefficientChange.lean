/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedExchangeTensorCoherence
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

/-- Every input admits a universal derived scalar-extension presentation, including
nonflat coefficient maps. Thus quantification over the presentations below adds no
existence hypothesis. Source: Stacks Tags 06YY and 07A6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: choose a K-flat resolution with flat terms (lem-pc-kflat-resolution), apply
ordinary scalar extension termwise, and localize. Independence of the resolution is
lem-pur-derived-change-of-rings. The tensor/restriction adjunction on representatives
descends to the derived adjunction (lem-weil-pbc-ring-sheaf-change-adjunction), whose
unit has exactly Sheaf.IsDerivedBaseChange's universal property. The usual equivalence
between modules over a constant ring sheaf and sheaves of modules over the fixed ring
transports this construction to the category used here, without changing its unit. -/
theorem nonempty_coefficientTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    Nonempty (CoefficientTensorModel φ T K) := by
  sorry

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

/-- Successive scalar reductions give the same actual C-linear comparison as direct
reduction, using the canonical associative tensor presentations. This includes identity
reductions and contains no faithfulness assumption on derived restriction.
Source: Stacks Tags 0D6D, 0E46 and 0E47
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the composite tensor units are universal by Sheaf.IsDerivedBaseChange.comp.
Precompose the two displayed arrows with the same universal unit and restrict scalars.
By the defining inverse-bijection equations for model.map and the coefficient comparison,
both adjuncts become compact support of the composite input unit, followed by the
same restriction comparison. The restriction comparisons compose by
lem-sf-compact-support-restriction-of-scalars. Injectivity of the universal-arrow
bijection, in D(C), gives the equality; derived scalar restriction need not be faithful. -/
theorem compactSupportCoefficientComparison_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] {φ : A →+* B} {ψ : B →+* C}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K) (M' : CoefficientTensorModel ψ X M.obj)
    (N : CoefficientTensorModel φ Y ((Rf_!(c)[ModuleCat.{u + 1} A]).obj K))
    (N' : CoefficientTensorModel ψ Y N.obj)
    (P : CoefficientTensorModel ψ Y ((Rf_!(c)[ModuleCat.{u + 1} B]).obj M.obj)) :
    N'.map P (compactSupportCoefficientComparison c M N) ≫
        compactSupportCoefficientComparison c M' P =
      compactSupportCoefficientComparison c (M.comp M') (N.comp N') := by
  sorry

/-- Compatibility of the actual B-linear comparison with the proper/open geometric
exchange for a cartesian square. The right-hand scalar extension of Ex! uses its
universal arrow, rather than an arbitrary map with the same endpoints.
Source: Stacks Tags 0E46 and 0E47
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: on proper factors, paste the inverse-image square with the coefficient square.
On K-flat tensors the two pastings both pull back x and retain b; mate pasting
therefore identifies their counit mates. On the open factors, invert both open
comparisons and transpose under the open adjunction. Both transposes apply scalar
extension to the same pulled-back open unit, then identify coefficients. They agree
in D(B), so the open square commutes. Compose the two equalities in the specified
compactification and its base change (def-cbc-exchange-map,
lem-cbc-proetale-extension-zero-base-change). Passing through the universal-arrow
bijection gives this equation in D(B); no faithfulness of restriction is used.
The finite-level pro-etale theorem identifies this exchange on the bounded etale-origin
inputs of the main theorem (thm-cbc-finite-level-proetale). -/
theorem compactSupportCoefficientComparison_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y ((Rf_!(c)[ModuleCat.{u + 1} A]).obj K))
    (P : CoefficientTensorModel φ Y'
      ((Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} A]).obj
        ((L((g')^*[ModuleCat.{u + 1} A])).obj K))) :
    (L((g)^*[ModuleCat.{u + 1} B])).map (compactSupportCoefficientComparison c M N) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} B) sq c).app M.obj =
      (N.pullback g).map P
          ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} A) sq c).app K) ≫
        compactSupportCoefficientComparison (c.ofIsPullback sq) (M.pullback g') P := by
  sorry

/-- The canonical proper-factor coefficient map, defined by the same universal-arrow
formula as the compactified map, using the specified direct-image mate.
Source: Stacks Tags 07A6 and 0B56
(blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def directImageCoefficientComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y ((R((f)_*[ModuleCat.{u + 1} A])).obj K)) :
    N.obj ⟶ (R((f)_*[ModuleCat.{u + 1} B])).obj M.obj :=
  (Equiv.ofBijective _ (N.universal _)).symm
    ((R((f)_*[ModuleCat.{u + 1} A])).map M.unit ≫
      (fixedScalarRestrictionDirectImage φ f).hom.app M.obj)

/-- The coefficient comparison carries the defining proper counit to the same counit
with B coefficients. Thus it respects the actual counit defining the projection
transformation, not merely the endpoints of that transformation.
Source: Stacks Tags 07A6, 0B56 and 0E48
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the restriction/direct-image comparison is the inverse mate of the actual
restriction/pullback square. The mate counit equation identifies the transpose of
the displayed comparison with coefficient extension of the A counit. The
universal-arrow formula for model.map is exactly that extension, with the pullback
comparison included in its source model. Apply the injective scalar-adjunction
bijection to obtain the equality in D(B). This is the proper equation of step 9
of the DAG proof; ringed exchange/tensor coherence then intertwines the projection
maps for arbitrary ambient Q (lem-weil-pbc-ringed-exchange-tensor-coherence). -/
theorem directImageCoefficientComparison_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y ((R((f)_*[ModuleCat.{u + 1} A])).obj K)) :
    (L((f)^*[ModuleCat.{u + 1} B])).map (directImageCoefficientComparison f M N) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app M.obj =
      (N.pullback f).map M
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K) := by
  sorry

/-- The canonical open-factor coefficient map, defined by its normalized restriction mate.
Source: Stacks Tag 0GL1 (blueprint: lem-fix-compact-support-coefficient-change). -/
noncomputable def openCoefficientComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Z ((D((j)_!open[ModuleCat.{u + 1} A])).obj K)) :
    N.obj ⟶ (D((j)_!open[ModuleCat.{u + 1} B])).obj M.obj :=
  (Equiv.ofBijective _ (N.universal _)).symm
    ((D((j)_!open[ModuleCat.{u + 1} A])).map M.unit ≫
      (fixedScalarRestrictionOpen φ j).hom.app M.obj)

/-- The open coefficient comparison respects the unit used in its projection comparison.
Together with the proper counit equation and the proper/open definition of compact
support, this gives the counit compatibility of the compactified projection transformation.
Source: Stacks Tags 0GL1 and 0E48
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: the restriction/open comparison was defined by transposing the inverse of the
restriction/pullback square. Its unit equation, followed by the two universal-arrow
bijections defining the displayed maps, gives the equality in D(B). Tensoring this
same unit with Q gives the open projection comparison; on K-flat models both routes
send (x tensor q) tensor b to (x tensor b) tensor (q tensor 1). Composing with the
proper counit equation proves the compactified compatibility of def-exchange-projection. -/
theorem openCoefficientComparison_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Z ((D((j)_!open[ModuleCat.{u + 1} A])).obj K)) :
    M.map (N.pullback j) ((fixedScalarOpenAdjunction A j).unit.app K) ≫
        (L((j)^*[ModuleCat.{u + 1} B])).map (openCoefficientComparison j M N) =
      (fixedScalarOpenAdjunction B j).unit.app M.obj := by
  sorry

/-- The coefficient comparison is precisely the proper comparison followed by the
proper direct image of the open comparison in the chosen compactification.
Source: blueprint order 1824, proof steps 3 and 6; Stacks Tags 0GL5 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: precompose both sides with the universal scalar-extension unit of N and use
the defining universal-bijection equations of the three comparisons. Naturality of
the proper restriction isomorphism moves the open comparison past the proper map.
Its adjunct becomes FA of the input unit followed by the open restriction comparison
and then the proper restriction comparison, which is the definition of
compactSupportRestrictionIso. Uniqueness in N.universal gives the equation in D(B).
Together with the open unit and proper counit equations, this fixes the comparison's
normalization as the tensor/projection comparison of def-exchange-projection. -/
theorem compactSupportCoefficientComparison_factorization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (J : CoefficientTensorModel φ c.Z
      ((D((c.i)_!open[ModuleCat.{u + 1} A])).obj K))
    (N : CoefficientTensorModel φ Y ((Rf_!(c)[ModuleCat.{u + 1} A]).obj K)) :
    compactSupportCoefficientComparison c M N =
      directImageCoefficientComparison c.g J N ≫
        (R((c.g)_*[ModuleCat.{u + 1} B])).map (openCoefficientComparison c.i M J) := by
  sorry

end AlgebraicGeometry.ProEtale
