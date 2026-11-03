/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeilTateTwist.CondensedWeilTateTwist
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilTateCompatibility.StrictWeilTateCompatibility
import WeilConjectures.SmoothPurity.CondensedWeilTensor.CondensedWeilTensorProduct

/-! # Closed-point Frobenius on condensed Tate lines

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/
lem-wf-tate-twist-frobenius.md and its proof
(blueprint: lem-wf-tate-twist-frobenius).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The existing signed root line with its canonical Weil datum in degree zero.
Source: latest blueprint, def-wf-tate-twist, signed line and root Weil structure
(blueprint: lem-wf-tate-twist-frobenius). -/
def condensedTateLocalModel (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (c : Coefficient ell) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℤ) :
    CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (c.obj ell) (D.geometricFrobenius X₀).hom).mapDerivedCategory :=
  letI : ∀ y : (D.geometricFiber X₀).left,
      Invertible (ell : (D.geometricFiber X₀).left.residueField y) := fun y ↦
    (show IsUnit (ell : (D.geometricFiber X₀).left.residueField y) by
      simpa only [map_natCast] using
        (primeUnit D ell hEll).map
          ((D.geometricFiber X₀).hom.residueFieldAlgebraMap y)).invertible
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    (derivedTateLine ell c _ m) (tateDatum ell c (D.geometricFrobenius X₀) m)

/-- The actual local-return action on H^0 of the exact scalar Tate stalk.
Source: latest blueprint, local Frobenius on Lambda_X(m) at bar x
(blueprint: lem-wf-tate-twist-frobenius). -/
def condensedTateClosedFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (c : Coefficient ell) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℤ)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (iota : X₀.left.residueField x.val →+* D.k)
    (hiota : iota.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :=
  (NativeCondensedDerived.cohomology (c.obj ell) 0).map
    (NativeCondensedDerived.operator (c.obj ell) D (D.geometricFrobenius X₀).hom
      (condensedTateLocalModel D ell hEll c X₀ m).carrier
      (condensedTateLocalModel D ell hEll c X₀ m).str
      (NativeCondensedModule.localClosedPoint D X₀ x iota hiota)
      (NativeCondensedModule.localClosedPointDegree D X₀ x - 1)
      (NativeCondensedModule.localClosedPoint_return D X₀ x iota hiota))

/-- At every closed point, geometric Frobenius on the signed Tate line is the
negative m-th power of the residue-field cardinality.

Source: latest blueprint, lem-wf-tate-twist-frobenius.md and its single proof paragraph
(blueprint: lem-wf-tate-twist-frobenius).

Proof: root pullback is inverse q-power. Pass to the inverse limit of roots,
extend to O_E and invert ell for E; the finite-subextension colimit gives Qbar.
Finite coefficients use the same root tensor construction. At a closed point
of degree d the prescribed semilinear return iterates the map d times, giving
q^(-d)=Q_x^(-1). Positive tensor powers multiply the scalar, the unit has scalar
one, and evaluation with the inverse positive map gives the reciprocal scalar
on the negative dual powers. Exact point pullback and scalar sections identify
H^0 of the degree-zero line with its actual stalk, retaining this action.
Changing a root frame conjugates a scalar and leaves the formula unchanged. -/
theorem condensedTateTwist_closedFrobenius (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (c : Coefficient ell)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℤ)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (iota : X₀.left.residueField x.val →+* D.k)
    (hiota : iota.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    condensedTateClosedFrobenius D ell hEll c X₀ m x iota hiota =
      (if 0 ≤ m then
        Ring.inverse (Nat.card (X₀.left.residueField x.val) : MonObj.Γ (c.obj ell)) ^ m.toNat
      else
        (Nat.card (X₀.left.residueField x.val) : MonObj.Γ (c.obj ell)) ^ (-m).toNat) •
      𝟙 _ := by
  sorry

end WeilConjectures
