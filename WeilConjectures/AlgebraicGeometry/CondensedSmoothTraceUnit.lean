/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison

/-! # The normalized smooth trace at the coefficient unit

Source: latest blueprint, sec-smooth-purity/sk-def-sp-trace/_section.md,
trace at the coefficient object (blueprint: sk-def-sp-trace).

## Main definitions

* `smoothTraceUnitCanonical`: the normalized counit at the regular unit.
* `smoothTraceCoefficientLine`: the native line in isomorphic ring coordinates.
* `smoothTraceUnitOfCoefficientIso`: its normalized trace over the original ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The coefficient unit belongs to the stated finite-Tor constructible domain.
Source: latest blueprint, smooth trace at the unit (blueprint: sk-def-sp-trace).
Proof: the regular coefficient module is free of rank one. The one-stratum
stratification and identity pro-etale cover give its finite constant local model.
Its degree-zero complex is bounded, has only the regular module as nonzero
cohomology, and tensoring with it is the identity, so it has Tor amplitude [0,0].
This includes the zero coefficient ring and the empty scheme. -/
theorem smoothTraceUnit_mem (c : Coefficient ell) (Y : Scheme.{u}) :
    property ell c Y (𝟙_ (c.derived ell Y)) := by
  sorry

/-- The unit normalization of the source of the existing smooth trace. It uses
only the specified pullback unit comparison and the native left unitor.
Source: latest blueprint, smooth trace domain (blueprint: sk-def-sp-trace). -/
def smoothTraceUnitSource (c : Coefficient ell) (D : WeilConjectures.FiniteFieldDatum.{u})
    (s : SmoothDatum D) :
    (c.smoothSource ell s.map s.dim).obj (𝟙_ _) ≅ c.derivedLine ell s.X.left s.dim :=
  tensorIso (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) s.map) (Iso.refl _) ≪≫
    λ_ _

/-- The normalized smooth trace on Lambda_X(d)[2d]. This is the recorded
purity-then-Brown-counit trace at the coefficient unit, with its canonical source
unit normalization; it does not choose a new orientation or a new trace.
Source: latest blueprint, displayed smooth trace (blueprint: sk-def-sp-trace). -/
def smoothTraceUnit (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (s : SmoothDatum D)
    (R : CondensedRing.ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj (c.derivedLine ell s.X.left s.dim) ⟶ 𝟙_ _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).map (smoothTraceUnitSource ell c D s).inv ≫
    (smoothTrace ell D hEll c s R ⟨𝟙_ _, smoothTraceUnit_mem ell c s.Y.left⟩).hom

/-- The same unit trace computed directly by the uniquely normalized adjunction's
counit. Counit compatibility of canonical purity identifies it with smoothTraceUnit
for every Brown presentation.
Source: latest blueprint, trace and counit compatibility (blueprint: sk-def-sp-trace). -/
def smoothTraceUnitCanonical (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) (s : SmoothDatum D) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj (c.derivedLine ell s.X.left s.dim) ⟶ 𝟙_ _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).map (smoothTraceUnitSource ell c D s).inv ≫
    (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s).trace
      ⟨𝟙_ _, smoothTraceUnit_mem ell c s.Y.left⟩

end AlgebraicGeometry.ProEtale.PurityTransport

namespace AlgebraicGeometry.ProEtale.CondensedRing
open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) (c : Coefficient ell)
  (e : c.bundled.{u} ell ≅ Λ)

/-- The native positive Tate line in arbitrary isomorphic coefficient coordinates.
Scalar extension along the displayed ring isomorphism is exact and strong monoidal;
it transports the root-tower line and its tensor powers, rather than a discrete model.
Source: latest blueprint, native coefficient twists (blueprint: sk-def-sp-trace). -/
def smoothTraceCoefficientLine (X : Scheme.{u}) (d : ℕ) :=
  (scalarSixChange e.hom X).obj ((DerivedCategory.singleFunctor _ 0).obj (c.line ell X d))

/-- The canonical support coefficient comparison is invertible along a ring iso.
Source: latest blueprint, coefficient invariance of smooth trace
(blueprint: sk-def-sp-trace).
Proof: extension along a ring iso is restriction along its inverse and hence an
exact equivalence. The pullback comparison is the identity on underlying sheaves.
Its direct-image counit mate is invertible because both vertical functors are
equivalences. Open extension commutes with the same restriction, so composing the
proper direct-image mate and open comparison gives the stated isomorphism. -/
theorem smoothTraceCoefficientSupport_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} (cf : Compactification f)
    (M : c.derived ell X) : IsIso ((scalarCompactSupportMap e.hom cf.i cf.g).app M) := by
  sorry

/-- Canonical scalar-extension shifts, transported by adjunction from the termwise
restriction-of-scalars functor. This is the same derived scalar functor already used.
Source: latest blueprint, canonical shift comparisons (blueprint: sk-def-sp-trace). -/
@[instance_reducible]
def smoothTraceCoefficientCommShift (X : Scheme.{u}) :
    (scalarSixChange e.hom X).CommShift ℤ :=
  let adj : scalarSixChange e.hom X ⊣
      (Mod.comap (coefficientMap (Λ := c.obj ell) (Λ' := Λ.X)
        e.hom.hom.hom X)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := c.obj ell) (Λ' := Λ.X) e.hom.hom.hom X)
  adj.leftAdjointCommShift ℤ

/-- The normalized trace in the original condensed coefficient ring. Both changes
of coordinates are canonical scalar maps: inverse compact-support comparison and
inverse scalar unit. The middle arrow is the original normalized integration trace.
Thus this definition applies to every ring isomorphic to an admissible presentation.
Source: latest blueprint, smooth trace (blueprint: sk-def-sp-trace). -/
def smoothTraceUnitOfCoefficientIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (s : SmoothDatum D) :
    (rightDerivedLowerShriekOfCompactification Λ.X s.compactification).obj
      ((smoothTraceCoefficientLine ell Λ c e s.X.left s.dim) ⟦2 * (s.dim : ℤ)⟧) ⟶ 𝟙_ _ :=
  letI := smoothTraceCoefficientCommShift ell Λ c e s.X.left
  letI := scalarSixChangeMonoidal e.hom s.Y.left
  (rightDerivedLowerShriekOfCompactification Λ.X s.compactification).map
      (((scalarSixChange e.hom s.X.left).commShiftIso (2 * (s.dim : ℤ))).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj (c.line ell s.X.left s.dim))) ≫
    @inv _ _ _ _ ((scalarCompactSupportMap e.hom s.compactification.i
      s.compactification.g).app (c.derivedLine ell s.X.left s.dim))
      (smoothTraceCoefficientSupport_isIso ell Λ c e s.compactification _) ≫
    (scalarSixChange e.hom s.Y.left).map (smoothTraceUnitCanonical ell D hEll c s) ≫
    (Functor.Monoidal.εIso (scalarSixChange e.hom s.Y.left)).inv

end AlgebraicGeometry.ProEtale.CondensedRing
