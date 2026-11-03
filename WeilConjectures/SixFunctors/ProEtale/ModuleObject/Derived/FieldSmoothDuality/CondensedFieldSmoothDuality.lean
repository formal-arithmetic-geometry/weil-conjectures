/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
-- Definition provider: def-a1-condensed-frobenius-transport (existing declarations).
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.PoincareDuality.Poincare
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SmoothPurity.OrientedPerfectDuality
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
end WeilConjectures.CondensedWeil
namespace WeilConjectures.CondensedWeil
open AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
end WeilConjectures.CondensedWeil
namespace WeilConjectures.CondensedWeil
open AlgebraicGeometry.ProEtale.CondensedRing.FieldSmoothDuality
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
set_option synthInstance.maxHeartbeats 200000 in
-- Nested linear maps retain the native cohomology module scalar structures.
set_option synthInstance.maxHeartbeats 200000 in
-- Nested linear maps retain the native cohomology module scalar structures.
set_option synthInstance.maxHeartbeats 200000 in
-- The nested module duals otherwise exhaust the default instance-search budget.
set_option maxHeartbeats 2000000 in
-- Keep the native sheaf-module cohomology expressions intact during elaboration.
end WeilConjectures.CondensedWeil
