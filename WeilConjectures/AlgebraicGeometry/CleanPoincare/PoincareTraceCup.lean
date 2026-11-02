/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting

/-! # Poincaré trace and cup-product datum

This module states the current condensed-coefficient definition from
`def-weil-poincare-trace-cup`.  The finite-field datum and the geometric
setting provide `X₀`, its geometric fibre `X`, and the structure morphism to
`Spec k`.  The supplied orientation is used by the canonical exceptional
counit from the current native exceptional inverse-image interface; the cup
product uses the normalized point tensor and the ordinary direct-image adjunction.
The traces are read directly on the recorded ordinary/compact coefficient complexes.
The displayed graded-commutativity law is recorded separately as a postponed theorem.
Source: literature/blueprint/latest/blueprint/sec-poincare-duality/sk-def-trace-cup/
def-weil-poincare-trace-cup.md (blueprint: def-weil-poincare-trace-cup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CleanPoincare

variable (ell : ℕ) [Fact ell.Prime]

/-- The prescribed continuous condensed rational coefficient ring.
Source: coefficient convention (blueprint: def-weil-poincare-trace-cup). -/
abbrev ring := (PurityTransport.Coefficient.rationals : PurityTransport.Coefficient ell).obj.{u} ell

/-- The actual unbounded derived category of modules over the pulled-back ring.
Source: derived-category convention (blueprint: def-weil-poincare-trace-cup). -/
abbrev category (X : Scheme.{u}) :=
  DerivedCategory.{u + 1}
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring.{u} ell) X))

/-- The regular coefficient module in degree zero, as the derived tensor unit.
Source: K_X = p_X^* Q_ell (blueprint: def-weil-poincare-trace-cup). -/
abbrev unit (X : Scheme.{u}) : category ell X := 𝟙_ _

open PurityTransport

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

/-- The structure morphism to the literal point `Spec k` used by the recorded
condensed cohomology declarations. Source: a_X in the fixed setting
(blueprint: def-weil-poincare-trace-cup). -/
abbrev recordedMap (s : SmoothDatum D) : s.X.left ⟶ s.Y.left :=
  s.map

/-- The ordinary cohomology object recorded by the condensed cohomology node,
restricted along the canonical constant `Q_ell` scalar map. Source: H^i
(blueprint: def-weil-poincare-trace-cup). -/
abbrev recordedCohomology (s : SmoothDatum D) (i : ℤ) : ModuleCat.{u + 1} (Padic ell) :=
  (ModuleCat.restrictScalars
    (Profinite.continuousMapConstRingHom (Padic ell))).obj
    ((CondensedRing.condensedRingOrdinaryCohomology (ring.{u} ell) (recordedMap s) i).obj
      (PurityTransport.unit ell .rationals s.X.left))

/-- The derived category used by the recorded condensed coefficient complexes.
Source: the RΓ convention (blueprint: def-weil-poincare-trace-cup). -/
instance gammaModulesDerived : HasDerivedCategory.{u + 1}
    (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (ring.{u} ell))) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (ring.{u} ell))) _ _
      (ModuleCat.isGrothendieckAbelian_of_commRing _)

/-- Scalar-unit representatives for a recorded ordinary cohomology complex.
Source: the class convention in step 5 (blueprint: def-weil-poincare-trace-cup). -/
abbrev recordedClasses {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    [HasDerivedCategory (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ))]
    (M : DerivedCategory (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ))) (i : ℤ) :=
  (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)))) ⟶ M⟦i⟧

/-- The representative/class equivalence is the projective scalar-unit Yoneda map,
followed by evaluation of a linear map at one. Source: H^i of the recorded RΓ
(blueprint: def-weil-poincare-trace-cup). -/
def recordedClassEquiv {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    [HasDerivedCategory (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ))]
    (M : DerivedCategory (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ))) (i : ℤ) :
    recordedClasses M i ≃
      ↥((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)) i).obj M) :=
  let e := (DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
    (ModuleCat.of (CategoryTheory.MonObj.Γ Λ) (CategoryTheory.MonObj.Γ Λ)) i).app M
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (e.addCommGroupIsoToAddEquiv.toEquiv.trans
      ((ModuleCat.homLinearEquiv (R := CategoryTheory.MonObj.Γ Λ) (S := ℤ)
        (M := ModuleCat.of (CategoryTheory.MonObj.Γ Λ) (CategoryTheory.MonObj.Γ Λ))
        (N := (DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (CategoryTheory.MonObj.Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)) i).obj M)).toEquiv))

/-- The positive Tate sheaf in degree zero.
Source: the orientation and coefficient twist (blueprint: def-weil-poincare-trace-cup). -/
abbrev positiveLine (X : Scheme.{u}) (d : ℕ) : category ell X :=
  (DerivedCategory.singleFunctor _ 0).obj ((Coefficient.rationals).line ell X d)

/-- The negative Tate line is the internal dual of the positive Tate line.
Source: the negative-twist definition (blueprint: def-weil-poincare-trace-cup). -/
abbrev negativeLine (X : Scheme.{u}) (d : ℕ) : category ell X :=
  (ihom (positiveLine ell X d)).obj (unit ell X)

/-- The coefficient Tate line is degree-zero point cohomology of the internal dual
Tate complex, with the constant rational scalar action. Source: Q_ell(-d)
(blueprint: def-weil-poincare-trace-cup). -/
abbrev valueLine (X : Scheme.{u}) (d : ℕ) : ModuleCat.{u + 1} (Padic ell) :=
  (ModuleCat.restrictScalars (Profinite.continuousMapConstRingHom (Padic ell))).obj
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (ring.{u} ell))) 0).obj
      ((CondensedRing.condensedRingCoefficientSections (ring.{u} ell) X).rightDerivedFunctor.obj
        (negativeLine ell X d)))

/-- The scalar coefficient object is degree-zero point cohomology of the coefficient
unit. Source: the target Q_ell of the compact trace
(blueprint: def-weil-poincare-trace-cup). -/
abbrev scalarValue (X : Scheme.{u}) : ModuleCat.{u + 1} (Padic ell) :=
  (ModuleCat.restrictScalars (Profinite.continuousMapConstRingHom (Padic ell))).obj
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (ring.{u} ell))) 0).obj
      ((CondensedRing.condensedRingCoefficientSections (ring.{u} ell) X).rightDerivedFunctor.obj
        (unit ell X)))

/-- The coefficient prime is invertible at every residue field over the fixed closure.
Source: the standing prime convention (blueprint: def-weil-poincare-trace-cup).
Proof: the fixed closure has characteristic p. The distinct prime ell is nonzero
there; its inverse maps to an inverse through the field map into each residue field. -/
theorem residue_prime_unit (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k)) (x : X) :
    IsUnit (ell : X.residueField x) := by
  sorry

variable {ell} {D : WeilConjectures.FiniteFieldDatum.{u}} (s : SmoothDatum D)

/-- The regular module is constructible and has Tor interval [0,0].
Source: the coefficient unit (blueprint: def-weil-poincare-trace-cup).
Proof: on the identity stratification its model is the free rank-one scalar module.
The complex is concentrated in degree zero and its tensor functor is the identity. -/
theorem unit_mem : property ell .rationals s.Y.left
    (PurityTransport.unit ell .rationals s.Y.left) := by
  sorry

/-- The fixed closure has the prescribed positive characteristic.
Source: finite-field conventions (blueprint: def-weil-poincare-trace-cup).
Proof: a finite field of cardinality p^a with a positive has characteristic p.
An algebraic extension of a field has the same characteristic. -/
theorem closure_characteristic : ringChar D.k = D.p := by
  sorry

/-- The literal morphism of the two recorded schemes over the fixed closure.
Source: a_X as an over-field morphism (blueprint: def-weil-poincare-trace-cup). -/
abbrev nativeMap : s.X ⟶ s.Y := s.map.asOver (Spec (.of D.k))

/-- The compactification used by the recorded native constructible exceptional functor.
Source: the exceptional inverse-image convention
(blueprint: def-weil-poincare-trace-cup). -/
abbrev nativeCompactification : Compactification s.map :=
  CondensedRing.compactificationOverField (nativeMap s)

/-- The rational ring is one of the actual native exceptional coefficients.
Source: the coefficient convention (blueprint: def-weil-poincare-trace-cup).
Proof: choose the rational disjunct and the identity ring-object isomorphism. -/
theorem nativeCoefficient : CondensedRing.IsNativeExceptionalCoefficient ell (ring.{u} ell) := by
  sorry

/-- The actual constructible exceptional inverse image of the coefficient unit.
Source: Ra_X^! Q_ell in the chosen orientation
(blueprint: def-weil-poincare-trace-cup). -/
def exceptionalUnit (hEll : ell ≠ D.p) : category ell s.X.left :=
  letI : Fact (ringChar D.k).Prime := ⟨by rw [closure_characteristic (D := D)]; exact D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨by rw [closure_characteristic (D := D)]; exact hEll.symm⟩
  ((WeilConjectures.currentExceptionalInverseImage (ring.{u} ell) ell D.k
    (Or.inr inferInstance) (nativeMap s) (nativeCoefficient (ell := ell))).obj
      ⟨PurityTransport.unit ell .rationals s.Y.left, (unit_mem s).1⟩).obj

/-- The trace uses precisely the chosen orientation and the recorded exceptional counit.
Source: eta_X and Ra_! Ra^! Q_ell -> Q_ell
(blueprint: def-weil-poincare-trace-cup). -/
def smoothTrace (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
      (nativeCompactification s)).obj
        (Coefficient.rationals.derivedLine ell s.X.left s.dim) ⟶ unit ell s.Y.left :=
  letI : Fact (ringChar D.k).Prime := ⟨by rw [closure_characteristic (D := D)]; exact D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨by rw [closure_characteristic (D := D)]; exact hEll.symm⟩
  (CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
    (nativeCompactification s)).map η.inv ≫
      ((WeilConjectures.currentExceptionalAdjunction (ring.{u} ell) ell D.k
        (Or.inr inferInstance) (nativeMap s) (nativeCoefficient (ell := ell))).counit.app
          ⟨PurityTransport.unit ell .rationals s.Y.left, (unit_mem s).1⟩).hom ≫
        (DerivedCategory.singleFunctorObjUnitIso
          (Mod (Sheaf (ProEt.topology s.Y.left) Ab.{u + 1})
            (condensedRingObj (ring.{u} ell) s.Y.left))).hom

/-- For a proper map the specified support-forgetting comparison is invertible.
Source: the proper comparison in the trace definition
(blueprint: def-weil-poincare-trace-cup).
Proof: in a compactification of a proper morphism the open immersion is also closed.
Extension by zero equals direct image on its open-and-closed image. The ordinary
pushforward compositor then identifies the specified map with the identity. -/
theorem properComparison_isIso [IsProper s.map] (K : category ell s.X.left) :
    IsIso (traceShriekToStar ell .rationals (nativeCompactification s) K) := by
  sorry

/-- The smooth trace read on ordinary direct image for a proper structure morphism.
Source: the proper trace comparison (blueprint: def-weil-poincare-trace-cup). -/
def ordinarySmoothTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim) :
    (CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (Coefficient.rationals.derivedLine ell s.X.left s.dim) ⟶ unit ell s.Y.left :=
  letI := properComparison_isIso s
    (Coefficient.rationals.derivedLine ell s.X.left s.dim)
  inv (traceShriekToStar ell .rationals (nativeCompactification s)
    (Coefficient.rationals.derivedLine ell s.X.left s.dim)) ≫ smoothTrace s hEll η

/-- The positive-line inverse-image comparison in degree zero, with root normalization.
Source: Cartesian Tate twists (blueprint: def-weil-poincare-trace-cup). -/
def pullPositive (p : LinePullCoordinates ell .rationals s.map) :
    (CondensedRing.upperStar (ring.{u} ell) s.map).leftDerivedFunctor.obj
      (positiveLine ell s.Y.left s.dim) ≅ positiveLine ell s.X.left s.dim :=
  (shiftFunctor (category ell s.X.left) (2 * (s.dim : ℤ))).preimageIso
    (((CondensedRing.upperStar (ring.{u} ell) s.map).leftDerivedFunctor.commShiftIso
      (2 * (s.dim : ℤ))).symm.app (positiveLine ell s.Y.left s.dim) ≪≫
        LinePullCoordinates.derived ell p s.dim)

/-- The twisted ordinary trace: projection, Cartesian Tate comparison, and the counit.
Source: untwisting the smooth trace (blueprint: def-weil-poincare-trace-cup). -/
def twistedTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map) :
    ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (unit ell s.X.left)) ⟦2 * (s.dim : ℤ)⟧ ⊗ positiveLine ell s.Y.left s.dim ⟶
        unit ell s.Y.left :=
  (((curriedTensor (category ell s.Y.left)).flip.obj
    (positiveLine ell s.Y.left s.dim)).commShiftIso (2 * (s.dim : ℤ))).hom.app _ ≫
      (CondensedRing.properProjectionMorphism (ring.{u} ell) s.map
        (unit ell s.X.left) (positiveLine ell s.Y.left s.dim)) ⟦2 * (s.dim : ℤ)⟧' ≫
      ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.map
        ((unit ell s.X.left) ◁ (pullPositive s p).hom ≫ (λ_ _).hom)) ⟦2 * (s.dim : ℤ)⟧' ≫
      ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.commShiftIso
        (2 * (s.dim : ℤ))).inv.app _ ≫ ordinarySmoothTrace s hEll η

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- The arrow from the shifted ordinary direct image to the negative Tate line is
obtained by transposing the twisted trace against the positive Tate line.
Source: untwisting in step 4 (blueprint: def-weil-poincare-trace-cup). -/
def untwistedTraceArrow [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map) :
    ((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (unit ell s.X.left)) ⟦2 * (s.dim : ℤ)⟧ ⟶ negativeLine ell s.Y.left s.dim :=
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology s.Y.left) Ab.{u + 1})
      (condensedRingObj (ring.{u} ell) s.Y.left))
  curry ((β_ (positiveLine ell s.Y.left s.dim)
    (((CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor.obj
      (unit ell s.X.left)) ⟦2 * (s.dim : ℤ)⟧)).hom ≫ twistedTrace s hEll η p)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- Apply recorded point sections to the untwisted trace arrow, and take the
canonical representative-to-homology equivalence. Source: tr_X^(-d), step 4
(blueprint: def-weil-poincare-trace-cup). -/
def recordedTrace [IsProper s.map] (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (p : LinePullCoordinates ell .rationals s.map)
    (x : recordedCohomology (ell := ell) s (2 * (s.dim : ℤ))) :
    valueLine ell s.Y.left s.dim :=
  let P := (CondensedRing.lowerStar (ring.{u} ell) s.map).rightDerivedFunctor
  let F := (CondensedRing.condensedRingCoefficientSections (ring.{u} ell)
    s.Y.left).rightDerivedFunctor
  let K := PurityTransport.unit ell .rationals s.X.left
  let M := F.obj (P.obj K)
  let N := F.obj (negativeLine ell s.Y.left s.dim)
  let e := DerivedCategory.singleFunctorObjUnitIso
    (Mod (Sheaf (ProEt.topology s.X.left) Ab.{u + 1})
      (condensedRingObj (ring.{u} ell) s.X.left))
  let t := (recordedClassEquiv M (2 * (s.dim : ℤ))).symm x ≫
    (F.map (P.map e.hom))⟦2 * (s.dim : ℤ)⟧' ≫
    (F.commShiftIso (2 * (s.dim : ℤ))).inv.app (P.obj (unit ell s.X.left)) ≫
    F.map (untwistedTraceArrow s hEll η p)
  recordedClassEquiv N 0 (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

/-- The compact trace domain uses the recorded compact cohomology functor with
coefficient Q_ell(d), rather than untwisted coefficients. Source: H_c^(2d)(X,Q_ell(d))
(blueprint: def-weil-poincare-trace-cup). -/
abbrev recordedTwistedCompactTop : ModuleCat.{u + 1} (Padic ell) :=
  (ModuleCat.restrictScalars (Profinite.continuousMapConstRingHom (Padic ell))).obj
    ((CondensedRing.condensedRingCompactCohomology (ring.{u} ell)
      (nativeCompactification s) (2 * (s.dim : ℤ))).obj
        (positiveLine ell s.X.left s.dim))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- The compact trace is homology of the point-sections image of the actual
exceptional counit composed with eta inverse. Source: tr_X, step 3
(blueprint: def-weil-poincare-trace-cup). -/
def recordedCompactTrace (hEll : ell ≠ D.p)
    (η : exceptionalUnit s hEll ≅ Coefficient.rationals.derivedLine ell s.X.left s.dim)
    (x : recordedTwistedCompactTop (ell := ell) s) : scalarValue ell s.Y.left :=
  let R := CondensedRing.rightDerivedLowerShriekOfCompactification (ring.{u} ell)
    (nativeCompactification s)
  let F := (CondensedRing.condensedRingCoefficientSections (ring.{u} ell)
    s.Y.left).rightDerivedFunctor
  let K := positiveLine ell s.X.left s.dim
  let M := (R ⋙ F).obj K
  let N := F.obj (unit ell s.Y.left)
  let t := (recordedClassEquiv M (2 * (s.dim : ℤ))).symm x ≫
    ((R ⋙ F).commShiftIso (2 * (s.dim : ℤ))).inv.app K ≫ F.map (smoothTrace s hEll η)
  recordedClassEquiv N 0 (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- The ordinary direct-image tensor map is the adjoint of the inverse pullback
tensorator followed by the two ordinary counits. Source: step 5, the map adjoint
to epsilon tensor epsilon (blueprint: def-weil-poincare-trace-cup). -/
def ordinarySiteProduct {X Y : Scheme.{u}} (a : X ⟶ Y)
    (K L : category ell X) :
    (CondensedRing.lowerStar (ring.{u} ell) a).rightDerivedFunctor.obj K ⊗
      (CondensedRing.lowerStar (ring.{u} ell) a).rightDerivedFunctor.obj L ⟶
        (CondensedRing.lowerStar (ring.{u} ell) a).rightDerivedFunctor.obj (K ⊗ L) :=
  let A := CondensedRing.derivedUpperStarLowerStarAdjunction (ring.{u} ell) a
  let U := (CondensedRing.upperStar (ring.{u} ell) a).leftDerivedFunctor
  let P := (CondensedRing.lowerStar (ring.{u} ell) a).rightDerivedFunctor
  A.homEquiv _ _ ((Functor.Monoidal.μIso U (P.obj K) (P.obj L)).inv ≫
    (A.counit.app K ⊗ₘ A.counit.app L))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- The lax tensor map of the recorded RΓ is the normalized point tensor map
followed by point sections of ordinarySiteProduct. Source: step 5
(blueprint: def-weil-poincare-trace-cup). -/
def ordinaryComplexProduct (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (K L : category ell X) :
    (CondensedRing.condensedRingOrdinaryCoefficientComplex (ring.{u} ell) a).obj K ⊗
      (CondensedRing.condensedRingOrdinaryCoefficientComplex (ring.{u} ell) a).obj L ⟶
        (CondensedRing.condensedRingOrdinaryCoefficientComplex (ring.{u} ell) a).obj (K ⊗ L) :=
  CondensedRing.TraceCupPoint.tensor (ring.{u} ell) k _ _ ≫
    (CondensedRing.TraceCupPoint.fiber (ring.{u} ell) k).map (ordinarySiteProduct a K L)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- Product of representatives in the recorded scalar derived category. Only the
canonical shift-tensor comparison is used. Source: H^i tensor H^j to H^(i+j), step 5
(blueprint: def-weil-poincare-trace-cup). -/
def recordedProduct {M N P : DerivedCategory
    (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (ring.{u} ell)))}
    (m : M ⊗ N ⟶ P) (i j : ℤ) (x : recordedClasses M i) (y : recordedClasses N j) :
    recordedClasses P (i + j) :=
  (λ_ _).inv ≫ (x ⊗ₘ y) ≫
    (DerivedCategory.shiftTensorShiftIso _ M N i j).hom ≫ m⟦i + j⟧'

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor instance terms exceed the default elaboration budget.
/-- Cup is the specified lax tensor map of RΓ followed by coefficient multiplication,
read on the recorded homology groups. Source: ordinary cup, step 5
(blueprint: def-weil-poincare-trace-cup). -/
def recordedCup (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (i j : ℤ)
    (x : (CondensedRing.condensedRingOrdinaryCohomology (ring.{u} ell) a i).obj
      (PurityTransport.unit ell .rationals X))
    (y : (CondensedRing.condensedRingOrdinaryCohomology (ring.{u} ell) a j).obj
      (PurityTransport.unit ell .rationals X)) :
    (CondensedRing.condensedRingOrdinaryCohomology (ring.{u} ell) a (i + j)).obj
      (PurityTransport.unit ell .rationals X) :=
  let K := PurityTransport.unit ell .rationals X
  let C := CondensedRing.condensedRingOrdinaryCoefficientComplex (ring.{u} ell) a
  let M := C.obj K
  let m : K ⊗ K ⟶ K :=
    ((DerivedCategory.singleFunctorObjUnitIso _).hom ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
  recordedClassEquiv M (i + j)
    (recordedProduct (ordinaryComplexProduct k a K K ≫ C.map m) i j
      ((recordedClassEquiv M i).symm x) ((recordedClassEquiv M j).symm y))

end AlgebraicGeometry.ProEtale.CleanPoincare

namespace AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup

open CategoryTheory.MonObj
open PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
instance geometricProper (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    IsProper (G.structureMorphism D.k) :=
  inferInstanceAs (IsProper (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
instance geometricSeparated (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    IsSeparated (G.structureMorphism D.k) :=
  inferInstanceAs (IsSeparated (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
instance geometricQuasiCompact (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    QuasiCompact (G.structureMorphism D.k) :=
  inferInstanceAs (QuasiCompact (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
instance geometricFiniteType (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    LocallyOfFiniteType (G.structureMorphism D.k) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
instance geometricSmoothDimension (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    SmoothOfRelativeDimension d (G.structureMorphism D.k) :=
  inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The geometric index of the actual base-changed smooth proper model, with identity
compactification. Source: X_0, X and a_X (blueprint: def-weil-poincare-trace-cup). -/
def geometry (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    SmoothDatum D :=
  { X := Over.mk (G.structureMorphism D.k)
    xFinite := geometricFiniteType D d G
    xQuasiCompact := geometricQuasiCompact D d G
    xSeparated := geometricSeparated D d G
    Y := Over.mk (𝟙 (Spec (.of D.k)))
    yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
    yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
    ySeparated := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
    map := G.structureMorphism D.k
    isOver := (Scheme.Hom.isOver_iff (Spec (.of D.k))).mpr (Category.comp_id _)
    separated := geometricSeparated D d G
    finiteType := geometricFiniteType D d G
    quasiCompact := geometricQuasiCompact D d G
    dim := d
    smooth := geometricSmoothDimension D d G
    compactification := Compactification.ofIsProper (G.structureMorphism D.k) }


end AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

/-- The item-owned geometric datum, using the literal geometric fibre.
Source: the fixed setting (blueprint: def-weil-poincare-trace-cup). -/
local notation "geometry" => AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry
local notation "exceptionalUnit" => AlgebraicGeometry.ProEtale.CleanPoincare.exceptionalUnit

/-- The degree-`2d` compactly supported class object from the recorded condensed
cohomology declaration with the positive Tate coefficient, restricted along the
canonical constant scalar map. Source: H_c^(2d)(X,Q_ell(d))
(blueprint: def-weil-poincare-trace-cup). -/
abbrev compactTopClass {D : WeilConjectures.FiniteFieldDatum.{u}}
    (ell : ℕ) [Fact ell.Prime]
    (s : AlgebraicGeometry.ProEtale.PurityTransport.SmoothDatum D) :=
  AlgebraicGeometry.ProEtale.CleanPoincare.recordedTwistedCompactTop (ell := ell) s

/-- The trace, cup product, and complementary-degree pairing attached to a
smooth proper geometric fibre and a chosen orientation.

Source: `literature/blueprint/latest/blueprint/sec-poincare-duality/`
`sk-def-trace-cup/def-weil-poincare-trace-cup.md`,
node `def-weil-poincare-trace-cup`. -/
structure PoincareTraceCupData {D : WeilConjectures.FiniteFieldDatum.{u}}
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (Qbar : Type u) [Field Qbar] [Algebra (Padic ell) Qbar]
    [IsAlgClosure (Padic ell) Qbar] (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d)
    [IsProper G.modelStructureMorphism]
    (η : AlgebraicGeometry.ProEtale.CleanPoincare.exceptionalUnit
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) hEll ≅
      PurityTransport.Coefficient.rationals.derivedLine ell
        (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G).X.left d) where
  /-- The untwisted trace `H^(2d)(X,Q_ell) → Q_ell(-d)`. -/
  trace : AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
      (ell := ell)
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G)
      (2 * (d : ℤ)) →
    AlgebraicGeometry.ProEtale.CleanPoincare.valueLine ell
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G).Y.left d
  /-- The compactly supported trace before the proper support comparison. -/
  compactTrace : compactTopClass ell
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) →
    AlgebraicGeometry.ProEtale.CleanPoincare.scalarValue ell
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G).Y.left
  /-- The ordinary cup product in all integer degrees. -/
  cup : ∀ (i j : ℤ),
    AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
      (ell := ell)
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) i →
      AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
        (ell := ell)
        (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) j →
      AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
        (ell := ell)
        (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) (i + j)
  /-- The trace-cup pairing in complementary degrees. -/
  pairing : ∀ (i : ℤ), 0 ≤ i → i ≤ 2 * (d : ℤ) →
    AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
      (ell := ell)
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G) i →
    AlgebraicGeometry.ProEtale.CleanPoincare.recordedCohomology
      (ell := ell)
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G)
      (2 * (d : ℤ) - i) →
    AlgebraicGeometry.ProEtale.CleanPoincare.valueLine ell
      (AlgebraicGeometry.ProEtale.CondensedRing.CleanTraceCup.geometry D d G).Y.left d

end AlgebraicGeometry.ProEtale.CondensedPoincare
