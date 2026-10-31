/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
-- Definition provider: def-a1-condensed-frobenius-transport (existing declarations).
public import WeilConjectures.AlgebraicGeometry.CondensedConstantExtensionFrobenius
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.PoincareDuality.Poincare
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.AlgebraicGeometry.OrientedPerfectDuality
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
/-! # Smooth duality for native condensed field coefficients

Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
degreewise field duality (blueprint: lem-a1-condensed-field-smooth-duality).

## Main statements

* `condensedFieldSmoothDualityDerived`: invertibility of the transpose of the actual
  cup/evaluation/normalized-exceptional-trace composite.
* `condensedFieldSmoothDuality`: the degreewise finite-dimensional, natural,
  Frobenius-equivariant perfect pairing with values in the actual negative Tate line.

All helpers are constructions belonging to this pairing. Cohomology and coefficient
categories are abbreviations for the published native condensed interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonoidalClosed
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
/-- The actual module category over the pulled-back condensed Qbar_l ring.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev coefficientModule (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l) X)
/-- The underived internal coefficient Hom into the regular coefficient module.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev dual (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (M : coefficientModule l X) :=
  (ihom M).obj (𝟙_ (coefficientModule l X))
/-- The canonical map from the negative Tate module to the dual positive Tate module.
At d = 0 it is the transpose of the unit unitor; at a positive integer it is the identity
on the defining internal-Hom presentation of the negative twist.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
def negativeTateToDual (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (d : ℕ) → tateTwist X l (-(d : ℤ)) ⟶ dual l X (tateTwist X l d)
  | 0 => curry (λ_ (𝟙_ (coefficientModule l X))).hom
  | _ + 1 => 𝟙 _
/-- The canonical comparison from the derived tensor of degree-zero modules to their
underived tensor in degree zero. It is localization tensor comparison followed by the
actual single-complex tensor identification.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def singleTensor (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M N : coefficientModule l X) :
    (DerivedCategory.singleFunctor _ 0).obj M ⊗
        (DerivedCategory.singleFunctor _ 0).obj N ⟶
      (DerivedCategory.singleFunctor _ 0).obj (M ⊗ N) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N)).hom ≫
  Functor.LaxMonoidal.μ DerivedCategory.Q
    ((CochainComplex.singleFunctor _ 0).obj M)
    ((CochainComplex.singleFunctor _ 0).obj N) ≫
  DerivedCategory.Q.map
    ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N
      ((CochainComplex.singleFunctor _ 0).obj M)).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorRight N) (.up ℤ) 0).hom.app M) ≫
  (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app (M ⊗ N)
/-- Underived coefficient evaluation, placed in degree zero and precomposed with
the localization tensor comparison. No derived dual is substituted for the underived dual.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def derivedEvaluation (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : coefficientModule l X) :
    (DerivedCategory.singleFunctor _ 0).obj M ⊗
        (DerivedCategory.singleFunctor _ 0).obj (dual l X M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (𝟙_ (coefficientModule l X)) :=
  singleTensor l X M (dual l X M) ≫
    (DerivedCategory.singleFunctor _ 0).map ((ihom.ev M).app _)
/-- The published compactification lower shriek before exact geometric-point sections.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev supported (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {k : Type u} [Field k] {a : X ⟶ Spec (.of k)} (c : Compactification a) :=
  rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l) c
/-- The published ordinary derived direct image before exact geometric-point sections.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev ordinary (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :=
  (lowerStar (Profinite.padicAlgClRingObj l) a).rightDerivedFunctor
/-- Mixed-support cup: exceptional projection followed by direct-image counit.
The construction exists on ambient derived module categories without an exceptional
right adjoint on that entire category.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def cup (l : ℕ) [Fact l.Prime]
    {k : Type u} [Field k] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)}
    (c : Compactification a) (K L : DerivedCategory (coefficientModule l X)) :
    (supported l c).obj K ⊗ (ordinary l a).obj L ⟶ (supported l c).obj (K ⊗ L) :=
  exceptionalProjectionMorphismOfCompactification (Profinite.padicAlgClRingObj l) c K _ ≫
    (supported l c).map
      (K ◁ (derivedUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj l) a).counit.app L)
/-- The structure map as a morphism of Over, with its literal underlying scheme map.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
def structureMap {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    X ⟶ Over.mk (𝟙 (Spec (.of k))) :=
  Over.homMk X.hom (Category.comp_id _)
/-- The published normalized smooth trace transported by the published
compactification-independence comparison. The exceptional counit is used only on the
bounded constructible Tate object.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def orientedTrace (l : ℕ) [Fact l.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (c : Compactification X.hom) (d : ℕ) :
    (supported l c).obj ((shiftFunctor _ (2 * (d : ℤ))).obj
      (tateTwistDerived X.left l d)) ⟶ 𝟙_ (DerivedCategory (coefficientModule l (Spec (.of k)))) :=
  ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
      (f := structureMap X) c (compactificationOverField (structureMap X))).hom.app
        (boundedConstructibleTateTwist l X d (2 * (d : ℤ)))).hom ≫
    (smoothTrace l (structureMap X) d).hom
/-- The scalar contraction of the canonical line-valued derived pairing with a
positive Tate section: mixed-support cup, underived coefficient evaluation, that section,
the shift comparisons, and the normalized exceptional trace, in this order.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def pairing (l : ℕ) [Fact l.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (c : Compactification X.hom) (d : ℕ)
    (M : coefficientModule l X.left)
    (z : 𝟙_ (coefficientModule l X.left) ⟶ tateTwist X.left l d) :
    (supported l c).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⊗
      (shiftFunctor _ (2 * (d : ℤ))).obj ((ordinary l X.hom).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dual l X.left M))) ⟶
      𝟙_ (DerivedCategory (coefficientModule l (Spec (.of k)))) :=
  ((tensorLeft _).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (cup l c ((DerivedCategory.singleFunctor _ 0).obj M)
        ((DerivedCategory.singleFunctor _ 0).obj (dual l X.left M)) ≫
        (supported l c).map (derivedEvaluation l X.left M ≫
          (DerivedCategory.singleFunctor _ 0).map z)) ≫
    ((supported l c).commShiftIso (2 * (d : ℤ))).inv.app _ ≫
    orientedTrace l X c d
/-- The cohomology class of a derived morphism from the coefficient unit to P[r].
This uses the actual derived homology and single/shift comparisons, followed by the
recorded coefficient sections model.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def cohomologyClass (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (P : DerivedCategory (coefficientModule l (Spec (.of k))))
    (r : ℤ) (x : 𝟙_ _ ⟶ (shiftFunctor _ r).obj P) :
    (condensedCoefficientSections l (Spec (.of k))).obj
      ((DerivedCategory.homologyFunctor _ r).obj P) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ x) ≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso r 0 r (add_zero r)).hom.app P
/-- Read an endomorphism of the derived coefficient unit in Qbar_l coordinates
by degree-zero homology and the published unit-section isomorphism.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def valueOfEnd (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    (f : End (𝟙_ (DerivedCategory (coefficientModule l (Spec (.of k)))))) :
    CohomologyScalar.{u} l :=
  (pointSectionsUnitIso l k).inv.hom
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor _ 0).map
        ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ f ≫
          (DerivedCategory.singleFunctorObjUnitIso _).inv) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _)
/-- Evaluate the actual derived pairing on classes in complementary degrees.
The derived tensor shift isomorphism retains its Koszul signs; the sum r + (-r) is
identified with zero before reading the scalar endomorphism.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def degreePairing (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    (P Q : DerivedCategory (coefficientModule l (Spec (.of k))))
    (n r : ℤ) (β : P ⊗ (shiftFunctor _ n).obj Q ⟶ 𝟙_ _)
    (x : 𝟙_ _ ⟶ (shiftFunctor _ r).obj P)
    (y : 𝟙_ _ ⟶ (shiftFunctor _ (n - r)).obj Q) : CohomologyScalar.{u} l :=
  valueOfEnd l k
    ((λ_ (𝟙_ _)).inv ≫
      (x ⊗ₘ (y ≫ ((shiftFunctorAdd' _ n (-r) (n-r) (sub_eq_add_neg n r)).app Q).hom)) ≫
      (DerivedCategory.shiftTensorShiftIso _ P ((shiftFunctor _ n).obj Q) r (-r)).hom ≫
      (shiftFunctor _ (r + -r)).map β ≫
      eqToHom (congrArg
        (fun j : ℤ ↦ (shiftFunctor _ j).obj
          (𝟙_ (DerivedCategory (coefficientModule l (Spec (.of k)))))) (add_neg_cancel r)) ≫
      (shiftFunctorZero _ ℤ).hom.app _)
end AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
namespace WeilConjectures.CondensedWeil
open AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
/-- The contragredient Weil arrow: the canonical closed comparison for pullback,
the pullback unit comparison, and precomposition with the inverse Weil isomorphism.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def dualFrobenius (M : WeilModule D l X₀) :
    (upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom).obj
      (dual l (D.geometricFiber X₀).left M.carrier) ⟶
        dual l (D.geometricFiber X₀).left M.carrier :=
  (Functor.LaxMonoidal.ihomComparison
    (upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    M.carrier).natTrans.app (𝟙_ _) ≫
  (ihom ((upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom).obj M.carrier)).map
      (Functor.Monoidal.εIso
        (upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)).inv ≫
  (pre M.str.inv).app (𝟙_ _)
/-- The canonical native compact-support Frobenius. Geometric-point insertion
is followed by the open/proper compactification exchange and then the derived Weil map.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def compactOperator (c₀ : Compactification X₀.hom) (M : WeilModule D l X₀) :
    End ((supported l (compactBase D X₀ c₀)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier)) :=
  (derivedPointInsertion l D.k (frobeniusPointIso D).hom (𝟭 _)).hom.app _ ≫
    (constantExtensionCompactExchange (Profinite.padicAlgClRingObj l)
      (compactBase D X₀ c₀) (D.geometricFrobenius X₀)
      (D.geometricFrobenius (compactModel D X₀ c₀)) (frobeniusPointIso D)
      (compactOpenSquare D X₀ c₀) (compactProperSquare D X₀ c₀)).app _ ≫
    (supported l (compactBase D X₀ c₀)).map
      (derivedTheta (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom
        M.carrier M.str).hom
/-- The semilinear geometric-Frobenius square of the actual structure map,
from its second geometric-fibre projection identity.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev structureSquare :
    CommSq (D.geometricFrobenius X₀).hom (D.geometricFiber X₀).hom
      (D.geometricFiber X₀).hom (frobeniusPointIso D).hom :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  ⟨(D.galoisMap_projections X₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2⟩
/-- The canonical ordinary Frobenius on the underived dual: geometric-point
insertion, the ordinary direct-image exchange, and the degree-zero contragredient arrow.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def ordinaryDualOperator (M : WeilModule D l X₀) :
    End ((ordinary l (D.geometricFiber X₀).hom).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (dual l (D.geometricFiber X₀).left M.carrier))) :=
  (derivedPointInsertion l D.k (frobeniusPointIso D).hom (𝟭 _)).hom.app _ ≫
    (constantExtensionProperExchange (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).hom (D.geometricFrobenius X₀) (frobeniusPointIso D)
      (structureSquare D X₀)).app _ ≫
    (ordinary l (D.geometricFiber X₀).hom).map
      (((upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀).hom).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map (dualFrobenius D l X₀ M))
/-- An abbreviation for the recorded native condensed compact cohomology functor
applied to the degree-zero carrier of the Weil module.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev compactH (c₀ : Compactification X₀.hom) (M : WeilModule D l X₀) (r : ℤ) :
    ModuleCat.{u + 1} (CohomologyScalar.{u} l) :=
  (condensedCompactCohomology l (compactBase D X₀ c₀) r).obj
    ((DerivedCategory.singleFunctor _ 0).obj M.carrier)
/-- An abbreviation for recorded native condensed ordinary cohomology of the
underived coefficient dual in degree zero.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev ordinaryDualH (M : WeilModule D l X₀) (r : ℤ) :
    ModuleCat.{u + 1} (CohomologyScalar.{u} l) :=
  (condensedOrdinaryCohomology l (D.geometricFiber X₀).hom r).obj
    ((DerivedCategory.singleFunctor _ 0).obj (dual l (D.geometricFiber X₀).left M.carrier))
/-- Sections of the actual positive Tate module on the geometric fibre.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev positiveLine (d : ℕ) : ModuleCat.{u + 1} (CohomologyScalar.{u} l) :=
  (condensedCoefficientSections l (D.geometricFiber X₀).left).obj
    (tateTwist (D.geometricFiber X₀).left l d)
/-- Sections of the actual negative Tate module Lambda(-d) on the geometric fibre.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev valueLine (d : ℕ) : ModuleCat.{u + 1} (CohomologyScalar.{u} l) :=
  (condensedCoefficientSections l (D.geometricFiber X₀).left).obj
    (tateTwist (D.geometricFiber X₀).left l (-(d : ℤ)))
end WeilConjectures.CondensedWeil
namespace WeilConjectures.CondensedWeil
open AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
/-- The specified finite-field characteristic transported to the specified
algebraic closure, using the actual cardinality equality and injective algebra map.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
instance datumCharP (D : FiniteFieldDatum.{u}) : CharP D.k D.p :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  charP_of_injective_algebraMap' D.k₀ D.p
/-- Primality of the characteristic of the specified algebraic closure.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
instance datumCharPrime (D : FiniteFieldDatum.{u}) : Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
/-- Finite type locally for the geometric fibre, obtained by base change.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
instance geometricFiberLft : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
/-- Quasi-compactness of the geometric fibre, obtained by base change.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
instance geometricFiberQc : QuasiCompact (D.geometricFiber X₀).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
/-- Separatedness of the geometric fibre, obtained by base change.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
instance geometricFiberSep [IsSeparated X₀.hom] : IsSeparated (D.geometricFiber X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
/-- The preceding canonical derived pairing for the specified finite-field
geometric fibre. The coefficient-prime condition is transported through the specified
characteristic, rather than imposed as an extra assumption.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def nativePairing (hl : l ≠ D.p) [IsSeparated X₀.hom]
    (c₀ : Compactification X₀.hom) (d : ℕ) (M : WeilModule D l X₀)
    (z : positiveLine D l X₀ d) :
    (supported l (compactBase D X₀ c₀)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ⊗
      (shiftFunctor _ (2 * (d : ℤ))).obj ((ordinary l (D.geometricFiber X₀).hom).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dual l (D.geometricFiber X₀).left M.carrier))) ⟶
      𝟙_ (DerivedCategory (coefficientModule l (Spec (.of D.k)))) :=
  letI : Fact (ringChar D.k ≠ l) := ⟨(ringChar.eq D.k D.p).symm ▸ hl.symm⟩
  pairing l (D.geometricFiber X₀) (compactBase D X₀ c₀) d M.carrier z
/-- Evaluate a negative Tate section against a positive Tate section using
the actual internal-Hom evaluation and unit unitor.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def lineContraction (d : ℕ)
    (w : valueLine D l X₀ d) (z : positiveLine D l X₀ d) :
    (condensedCoefficientSections l (D.geometricFiber X₀).left).obj
      (𝟙_ (coefficientModule l (D.geometricFiber X₀).left)) :=
  (λ_ (𝟙_ _)).inv ≫
    (z ⊗ₘ (w ≫ negativeTateToDual l (D.geometricFiber X₀).left d)) ≫
    (ihom.ev (tateTwist (D.geometricFiber X₀).left l d)).app (𝟙_ _)
/-- The actual covariant map of the recorded compact-cohomology functor.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def compactCohomologyMap (c₀ : Compactification X₀.hom)
    {M N : WeilModule D l X₀} (f : M ⟶ N) (r : ℤ) :
    compactH D l X₀ c₀ M r ⟶ compactH D l X₀ c₀ N r :=
  (condensedCompactCohomology l (compactBase D X₀ c₀) r).map
    ((DerivedCategory.singleFunctor _ 0).map f.hom.f)
/-- The actual contravariant cohomology map induced by precomposition
on the underived coefficient dual.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def ordinaryDualCohomologyMap
    {M N : WeilModule D l X₀} (f : M ⟶ N) (r : ℤ) :
    ordinaryDualH D l X₀ N r ⟶ ordinaryDualH D l X₀ M r :=
  (condensedOrdinaryCohomology l (D.geometricFiber X₀).hom r).map
    ((DerivedCategory.singleFunctor _ 0).map ((pre f.hom.f).app (𝟙_ _)))
/-- The recorded point-sections and homology applied to the native
compact-support Frobenius, with no chosen linear operator.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def compactCohomologyFrobenius (c₀ : Compactification X₀.hom)
    (M : WeilModule D l X₀) (r : ℤ) : End (compactH D l X₀ c₀ M r) :=
  (condensedCoefficientSections l (Spec (.of D.k))).map
    ((DerivedCategory.homologyFunctor _ r).map (compactOperator D l X₀ c₀ M))
/-- The recorded point-sections and homology applied to the
native ordinary Frobenius on the underived dual.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def ordinaryDualCohomologyFrobenius
    (M : WeilModule D l X₀) (r : ℤ) : End (ordinaryDualH D l X₀ M r) :=
  (condensedCoefficientSections l (Spec (.of D.k))).map
    ((DerivedCategory.homologyFunctor _ r).map (ordinaryDualOperator D l X₀ M))
end WeilConjectures.CondensedWeil
namespace WeilConjectures.CondensedWeil
open AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
set_option synthInstance.maxHeartbeats 200000 in
-- Nested linear maps retain the native cohomology module scalar structures.
/-- A family of bilinear maps on the recorded cohomology modules for lisse
Weil modules, with values in the actual negative Tate line.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
abbrev pairingFamily (c₀ : Compactification X₀.hom) (d : ℕ) :=
  ∀ (M : WeilModule D l X₀)
    (_ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) (r : ℤ),
    compactH D l X₀ c₀ M r →ₗ[CohomologyScalar.{u} l]
      ordinaryDualH D l X₀ M (2 * (d : ℤ) - r) →ₗ[CohomologyScalar.{u} l]
        valueLine D l X₀ d
set_option synthInstance.maxHeartbeats 200000 in
-- Nested linear maps retain the native cohomology module scalar structures.
/-- The normalization specifying the pairing. E is fixed by actual Tate
evaluation, and B is fixed on all derived cohomology classes by the cup/evaluation/trace
composite. Thus the existential witnesses in the theorem cannot be arbitrary pairings.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
canonical pairing and its degreewise line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality). -/
@[irreducible] def IsCanonicalPairing (hl : l ≠ D.p) [IsSeparated X₀.hom]
    (c₀ : Compactification X₀.hom) (d : ℕ)
    (E : valueLine D l X₀ d ≃ₗ[CohomologyScalar.{u} l]
      Module.Dual (CohomologyScalar.{u} l) (positiveLine D l X₀ d))
    (B : pairingFamily D l X₀ c₀ d) : Prop :=
  (∀ (w : valueLine D l X₀ d) (z : positiveLine D l X₀ d),
    Mod.regularEndRingHom
      (cohomologyScalarSections l (D.geometricFiber X₀).left (E w z)) =
        lineContraction D l X₀ d w z) ∧
  ∀ (M : WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (r : ℤ) (z : positiveLine D l X₀ d)
    (x : 𝟙_ (DerivedCategory (coefficientModule l (Spec (.of D.k)))) ⟶
      (shiftFunctor _ r).obj ((supported l (compactBase D X₀ c₀)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M.carrier)))
    (y : 𝟙_ (DerivedCategory (coefficientModule l (Spec (.of D.k)))) ⟶
      (shiftFunctor _ (2 * (d : ℤ) - r)).obj
        ((ordinary l (D.geometricFiber X₀).hom).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (dual l (D.geometricFiber X₀).left M.carrier)))),
    E (B M hM r (cohomologyClass l D.k _ r x)
      (cohomologyClass l D.k _ (2 * (d : ℤ) - r) y)) z =
        degreePairing l D.k _ _ (2 * (d : ℤ)) r
          (nativePairing D l X₀ hl c₀ d M z) x y
/-- The derived adjoint of the same smooth trace/cup/evaluation pairing is invertible.
A positive Tate basis is allowed only as a coordinate for the pairing and is quantified
universally; its existence is also asserted. This is the derived form of the node.
Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
the global-duality isomorphism and its equivalent line-valued form
(blueprint: lem-a1-condensed-field-smooth-duality).
Proof: place the lisse module in degree zero. It is locally finite free and site-perfect;
its underived dual is its derived coefficient dual by the local finite-free calculation.
Apply sk-thm-sf-dual-perfect with the specified smooth orientation and then
sk-thm-sf-global-duality. The resulting comparison is the transpose of nativePairing by
sk-thm-sf-identification. A compatible system of roots of unity over the algebraically
closed field trivializes the positive Tate line; tensoring by any such basis removes the
Tate factor, giving the asserted derived isomorphism. -/
theorem condensedFieldSmoothDualityDerived
    (hl : l ≠ D.p) [IsSeparated X₀.hom] [GeometricallyConnected X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom]
    (c₀ : Compactification X₀.hom) :
    Nonempty (𝟙_ (coefficientModule l (D.geometricFiber X₀).left) ≅
      tateTwist (D.geometricFiber X₀).left l d) ∧
    ∀ (M : WeilModule D l X₀)
      (_ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
      (e : 𝟙_ (coefficientModule l (D.geometricFiber X₀).left) ≅
        tateTwist (D.geometricFiber X₀).left l d),
      IsIso (curry (nativePairing D l X₀ hl c₀ d M e.hom)) := by
  sorry
set_option synthInstance.maxHeartbeats 200000 in
-- The nested module duals otherwise exhaust the default instance-search budget.
set_option maxHeartbeats 2000000 in
-- Keep the native sheaf-module cohomology expressions intact during elaboration.
/-- Smooth duality in every integer degree, for the actual condensed Qbar_l module
and its underived coefficient dual. The family is characterized by coefficient evaluation,
mixed-support cup and the exceptional counit under the smooth orientation, through
`IsCanonicalPairing`; its adjoints are both bijective. Naturality is for every Weil-module
map. Frobenius on the target is multiplication by q^d.

Source: latest blueprint, sec-poincare-duality/sk-thm-derived-duality/_section.md,
degreewise field duality, and sk-thm-frobenius/_section.md
(blueprint: lem-a1-condensed-field-smooth-duality).

Proof: the one-stratum lisse module belongs to the coefficient heart and is site-perfect,
locally finite free with Tor interval [0,0], including rank zero. Its underived coefficient
dual computes derived Hom by the local finite-free calculation and sheaf descent.
Oriented perfect duality identifies its Verdier dual with K-dual(d)[2d]. Global duality
identifies ordinary sections of that dual with the coefficient dual of compact sections,
by precisely cup, evaluation and the counit. Finiteness makes the point complexes perfect.
Split a bounded field complex into its cohomology and contractible two-term summands.
On a cohomology summand evaluation has matrix (-1)^r times the identity, so both adjoints
are bijective. Transport this through global duality. Contracting with a positive Tate
section gives exactly `nativePairing`, so the inverse Tate line and its normalization
recover the unique line-valued pairing. Evaluation proves naturality. Equip the underived
dual with the contragredient Weil datum, constructed in `dualFrobenius`. The canonical
Frobenius compatibility of the same derived pairing gives the q^d equation, since the
positive Tate line has geometric Frobenius q^(-d). The compactification exchanges compute
the native geometric Frobenius operators used here; no properness or ambient unbounded
exceptional right adjoint is used. -/
theorem condensedFieldSmoothDuality
    (hl : l ≠ D.p) [IsSeparated X₀.hom] [GeometricallyConnected X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom]
    (c₀ : Compactification X₀.hom) :
    ∃ (E : valueLine D l X₀ d ≃ₗ[CohomologyScalar.{u} l]
        Module.Dual (CohomologyScalar.{u} l) (positiveLine D l X₀ d))
      (B : pairingFamily D l X₀ c₀ d),
      IsCanonicalPairing D l X₀ hl c₀ d E B ∧
      (∀ (M : WeilModule D l X₀)
        (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) (r : ℤ),
        FiniteDimensional (CohomologyScalar.{u} l) (compactH D l X₀ c₀ M r) ∧
        FiniteDimensional (CohomologyScalar.{u} l)
          (ordinaryDualH D l X₀ M (2 * (d : ℤ) - r)) ∧
        Function.Bijective (B M hM r) ∧ Function.Bijective (B M hM r).flip) ∧
      (∀ (M N : WeilModule D l X₀)
        (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
        (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier)
        (f : M ⟶ N) (r : ℤ) (x : compactH D l X₀ c₀ M r)
        (y : ordinaryDualH D l X₀ N (2 * (d : ℤ) - r)),
        B N hN r ((compactCohomologyMap D l X₀ c₀ f r).hom x) y =
          B M hM r x ((ordinaryDualCohomologyMap D l X₀ f (2 * (d : ℤ) - r)).hom y)) ∧
      (∀ (M : WeilModule D l X₀)
        (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
        (r : ℤ) (x : compactH D l X₀ c₀ M r)
        (y : ordinaryDualH D l X₀ M (2 * (d : ℤ) - r)),
        B M hM r ((compactCohomologyFrobenius D l X₀ c₀ M r).hom x)
          ((ordinaryDualCohomologyFrobenius D l X₀ M (2 * (d : ℤ) - r)).hom y) =
            (D.q : CohomologyScalar.{u} l) ^ d • B M hM r x y) := by
  sorry
end WeilConjectures.CondensedWeil
