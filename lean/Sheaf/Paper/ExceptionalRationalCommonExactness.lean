/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ExceptionalRationalCommonCoherence

/-! # Shift normalization after the unshifted common-field adjunction descent

This is solely the exactness and shift part of Zheng, Construction 6.6.
The quotient functors, adjunction, and inclusion maps are already explicitly constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
  (P : RationalStageAssembly.{u, v} l Ω D hl A)

/-- Shift and exactness structures on the explicitly constructed pair functors.
There are no functors, adjunctions, comparison maps or transition equations to choose here.
Endpoint inclusion shifts are chosen once for the whole compactification family.
Source: Zheng, Construction 6.6, common-field descent step 4
(blueprint: lem-sf-rational-common-exact-shifts). -/
structure RationalCommonShiftData where
  inclusionX (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (commonInclusion.{u, v} l Ω X i).CommShift ℤ
  inclusionY (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (commonInclusion.{u, v} l Ω Y i).CommShift ℤ
  leftShift (c : Compactification f) : (rationalCommonLeft A P c).functor.CommShift ℤ
  rightShift (c : Compactification f) : (rationalCommonRight A P c).functor.CommShift ℤ
  leftExact (c : Compactification f) :
    letI := leftShift c
    (rationalCommonLeft A P c).functor.IsTriangulated
  rightExact (c : Compactification f) :
    letI := rightShift c
    (rationalCommonRight A P c).functor.IsTriangulated
  unitShift (c : Compactification f) :
    letI := leftShift c
    letI := rightShift c
    (rationalCommonAdjunction A P c).unit.CommShift ℤ
  counitShift (c : Compactification f) :
    letI := leftShift c
    letI := rightShift c
    (rationalCommonAdjunction A P c).counit.CommShift ℤ
  qShift (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
      (P.operation c (commonField.{u, v} l Ω i)).leftShift
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
      inclusionX i
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
      inclusionY i
    letI := leftShift c
    ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ
  bShift (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    letI : ((rationalCommonRight A P c).Φ i).CommShift ℤ :=
      (P.operation c (commonField.{u, v} l Ω i)).rightShift
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
      inclusionX i
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
      inclusionY i
    letI := rightShift c
    ((rationalCommonRight A P c).ιCompFunctorIso i).inv.CommShift ℤ

/-- Normalize the shifts of the fixed quotient adjunction, retaining the supplied
rational operation structures and using endpoint inclusion shifts independent of c.
This theorem asserts only shift structures and their exactness and compatibility.
Source: Zheng, Construction 6.6, common-field descent step 4
(blueprint: lem-sf-rational-common-exact-shifts).

Proof: take the ratio of the supplied endpoint localization shift with the
canonical localization shift. Residue Tor represents every rational object by an
integral finite-Tor object. Naturality of this ratio on integral arrows extends to
rational arrows: these are sums of scalar multiples of localized integral arrows,
and every rational scalar commutes with every morphism. Thus the ratio descends
to a natural automorphism of the rational shift functor, with its zero and addition
laws inherited from the two localization CommShift structures. P.shiftX and
P.shiftY make these endpoint corrections independent of compactification.
The identity q of P.localization and its shift square express P's left shift as
the normalized integral left shift conjugated by these corrections. A.leftShift
identifies the latter with the actual compact-support shift. Apply these endpoint
corrections to the canonical common-field inclusion shifts. If there is no
compactification, choose the canonical inclusion shifts and all remaining claims
are vacuous; otherwise compute the corrections at any compactification.
Normalize each rational left functor shift using its compact-support realization.
The integral scalar projection cocycle, its shift square, and P.scalar_normalized
show that these normalized shifts obey the scalar enlargement square. The right
shift is the adjunction transpose of the normalized left shift; the finite unit
and counit squares determine it and give the right scalar enlargement square.
Include these normalized finite shift maps at each literal pair object. The
scalar squares prove naturality on representatives and the finite zero/addition
laws prove the CommShift laws. For exactness use the normalized finite shifts
and the canonical inclusions: every distinguished triangle is isomorphic to an
included finite-stage triangle, and the normalized finite compact-support functor
is exact. Its right adjoint is exact by the triangulated-adjunction theorem.
The descended units and counits are the included finite ones, so their shift
squares hold. Finally transport the endpoint corrections back in the restriction
squares; the localization shift equation recovers precisely the original rational
left shifts, and uniqueness of the adjoint shift recovers the original right
shifts. This gives qShift and bShift. Repeated stages and negative shifts use the
published scalar associators and the integer CommShift addition law. -/
theorem exists_rational_common_exact_shifts :
    Nonempty (RationalCommonShiftData.{u, v} l Ω D hl A P) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
