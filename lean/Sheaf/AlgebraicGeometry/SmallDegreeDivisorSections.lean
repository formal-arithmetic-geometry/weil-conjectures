/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Sections of small-degree divisors on a curve

Source: Milne, Abelian Varieties, Chapter III, proof of Proposition 2.3, pp.92–93,
and Lemma 5.2(a),(b), pp.101–102 (blueprint: lem-sfb-small-degree-divisor-sections).

The cohomology is the recorded right derived functor on modules, with scalars
restricted along the given structure morphism. Point divisors use Mathlib's
`pointEquivClosedPoint` and the existing finitely supported divisor group.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every point divisor has one independent section on a positive-genus curve;
each degree from zero to the genus also has an effective divisor with one section,
and the zero divisor works in degree zero.
Source: Milne, Abelian Varieties, Chapter III, proof of Proposition 2.3, pp.92–93,
and Lemma 5.2(a),(b), pp.101–102 (blueprint: lem-sfb-small-degree-divisor-sections).

Proof:
1. Projective-proper and smooth-connected-curve-local-rings make C proper, integral,
   Noetherian and regular. Divisor-module-local makes O(D) invertible. Divisor degree
   agrees with line-bundle degree (def-sc-pic0). Serre duality and Riemann–Roch give
   h0(D)-h1(D)=deg(D)+1-g. At D=0, def-sc-genus gives h1(0)=g, hence h0(0)=1.
2. The constant rational function 1 gives h0([Q])>=1. For g=1, Riemann–Roch in large
   degree gives equality. For g>=2, lem-sfb-linear-series-degree-dimension-bound,
   with lem-pc-degree-agrees-sc, gives h0([Q])<=3/2, hence equality by integrality.
3. Let N_D be the canonical sheaf tensor O(D)'s inverse, using canonical-sheaf,
   invertible-dual and sheaf-tensor-product. The local description t^(-n) of O(D)
   identifies H0(N_(D+[Q])) with the kernel of evaluation H0(N_D) -> N_D(Q): at Q
   the inclusion has image t(N_D)_Q, and away from Q it is the identity.
4. If h1(D)>0, duality gives a nonzero section of N_D. Invertible-module-generic-stalk
   makes its generic germ nonzero. On a nonempty open it generates N_D; rational-
   points-dense supplies Q there. Evaluation onto the one-dimensional fibre is
   surjective. Rank-nullity and duality give h1(D+[Q])=h1(D)-1, allowing repeated Q.
5. Starting with D_0=0, repeat while j<g to get effective divisors D_j of degree j
   with h1(D_j)=g-j. Riemann–Roch then gives h0(D_j)=1, including j=0 and j=g. -/
theorem smallDegreeDivisor_sections
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g) :
    (∀ Q : {q : Spec (.of k) ⟶ C // q ≫ f = 𝟙 _},
      Module.finrank k ((RingedSpace.moduleCohomology C.toRingedSpace 0 ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          (Divisor.moduleOfSmoothConnectedCurve k C f
            (Finsupp.single (pointEquivClosedPoint f Q) 1 : C.Divisor))) = 1) ∧
    (∀ r : ℤ, 0 ≤ r → r ≤ (g : ℤ) → ∃ D : C.Divisor,
      (∀ P : closedPoints C, 0 ≤ D P) ∧ Divisor.degree C D = r ∧
      Module.finrank k ((RingedSpace.moduleCohomology C.toRingedSpace 0 ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          (D.moduleOfSmoothConnectedCurve k C f)) = 1) ∧
    Module.finrank k ((RingedSpace.moduleCohomology C.toRingedSpace 0 ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        ((0 : C.Divisor).moduleOfSmoothConnectedCurve k C f)) = 1 := by
  sorry

end AlgebraicGeometry.Scheme
