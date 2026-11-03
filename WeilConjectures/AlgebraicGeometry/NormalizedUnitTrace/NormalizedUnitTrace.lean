/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# The normalized explicit smooth counit at the coefficient unit

Source: smooth purity transport, Steps 1--3, and its counit normalization
(blueprint: def-pur-normalized-explicit-unit-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

/-- The specified finite diagonal/DNC counits and scalar counit equations pin
the family down up to the equality of counits used below. In particular this
selection does not select an arbitrary purity isomorphism or an arbitrary trace.
Source: smooth purity transport Steps 1--3
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def family (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] : Family ell k :=
  (comparisonBrownExplicit k ell Fact.out (Fact.out : ringChar k ≠ ell).symm).choose

/-- Evaluate the source functor at the actual derived tensor unit.
Source: the pullback unit and left unitor in smooth purity transport Step 3
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def unitSource (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (c.smoothSource ell f d).obj (𝟙_ _) ≅ c.derivedLine ell X d :=
  tensorIso (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) f) (Iso.refl _) ≪≫ λ_ _

/-- The normalized explicit counit on the shifted Tate line, with its canonical
unit source comparison. Source: the smooth trace composite
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def unitTrace (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (b : Family ell k) (c : Coefficient ell) (s : Datum k) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).obj
        (c.derivedLine ell s.X s.dim) ⟶ 𝟙_ _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
      (unitSource ell c s.map s.dim).inv ≫
    (b c s).trace ⟨𝟙_ _, smoothTraceUnit_mem ell c s.Y⟩

theorem closure_line_eq (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    (Coefficient.closure : Coefficient ell).line ell X d = tateTwist X ell (d : ℤ) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (Coefficient.closure : Coefficient ell).line ell X d ⊗
        (Coefficient.closure : Coefficient ell).firstLine ell X =
      tateTwistNat X ell d ⊗ tateTwistOne X ell
    rw [ih]
    rfl

/-- The concrete closure Tate line is the published root-tower Tate twist,
with the same scalar inclusion, ordered tensor powers and shift.
Source: condensed Tate conventions and smooth purity transport Step 3
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def closureLineIso (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) (d : ℕ) :
    (Coefficient.closure : Coefficient ell).derivedLine ell X d ≅
      (shiftFunctor _ (2 * (d : ℤ))).obj (tateTwistDerived X ell d) :=
  eqToIso (congrArg
    (fun M ↦ (shiftFunctor _ (2 * (d : ℤ))).obj ((DerivedCategory.singleFunctor _ 0).obj M))
    (closure_line_eq ell X d))

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The same smooth morphism and chosen compactification as the published
bounded constructible compact-support functor.
Source: compactification convention in smooth purity transport Step 3
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def datum (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] : Datum k := by
  letI : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  letI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  letI : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  letI : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  letI : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  exact
    { X := X.left
      Y := Y.left
      base := Y.hom
      map := f.left
      dim := d
      compactification := compactificationOverField f }

/-- The normalized closure-coefficient smooth trace in the published Tate
coordinates. This is an explicit counit, not data selected from bare existence
of a representing map.
Source: smooth purity transport Steps 1--3 and the smooth trace composite
(blueprint: def-pur-normalized-explicit-unit-trace). -/
def closureTrace (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell)
      (compactificationOverField f)).obj
        ((shiftFunctor _ (2 * (d : ℤ))).obj (tateTwistDerived X.left ell d)) ⟶ 𝟙_ _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell)
      (compactificationOverField f)).map (closureLineIso ell X.left d).inv ≫
    unitTrace ell (family ell k) .closure (datum f d)

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
