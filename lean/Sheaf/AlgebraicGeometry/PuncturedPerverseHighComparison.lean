/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound

/-!
# High-degree comparison on a punctured strictly local scheme

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Lemma 5.3.2,
printed pages 288--289, and Proposition 3.2.1
(blueprint: lem-per-punctured-perverse-high-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The specified constant zeroth truncation gives the high-degree comparison isomorphism
on the punctured spectrum. Source: ILO, Expose XVII, Lemma 5.3.2, pp. 288--289
(blueprint: lem-per-punctured-perverse-high-comparison).

The presentation `e` expresses that the local scheme is the spectrum of its local ring.
`ULift` only places the coefficient ring in the universe of the six-functor library.
The stalk bound is stated on cohomology sheaves: exactness of geometric stalks identifies
it with cohomology of the geometric restriction. Local dimensions are finite nonnegative
integers under `hdim`, so `ENat.toNat (WithBot.unbotD 0 ...)` is their integer value.
Natural subtraction `2 * h - 2` is exactly `max(0, 2h - 2)`. Cohomology retains its
coefficient-module structure and is computed by the existing derived global sections.

Proof:
1. Set `C = tau_ge_1 M`. The ordinary truncation triangle, with its first object identified
   using `alpha`, is `Lambda_U -> M -> C -> Lambda_U[1]`. Its first arrow is precisely
   `alpha.hom` followed by the ordinary truncation inclusion. The cohomology sheaves of C
   vanish in degrees at most zero and agree with those of M in positive degrees
   (def-sbc-standard-tstructure-derived-category, def-kun-truncations).
2. For y in U, concatenate generalization chains with the strict specialization to x:
   `h_y <= d-1`; concatenating with chains in the closure of y gives `h_y + e_y <= d`
   (lem-sc-scheme-stalk-dimension-generalization-chains). Exactness and conservativity
   of geometric stalks show that C has no cohomology above `2d-4`
   (prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative).
   For d = 2 this already gives C = 0.
3. For r = 2i-1 or 2i, with `1 <= i <= d-2`, a nonzero stalk of H^r(C) forces
   `h_y >= i+1`, hence `e_y <= d-i-1`. This uses geometric support, without any
   assumption that the support is closed or constructible.
4. Filter H^r(C) by powers of ell. Each quotient is killed by ell and has the same
   support bound. Apply lem-per-punctured-support-cohomological-bound to each quotient
   to obtain vanishing in degrees `p >= 2(d-i-1)`. Descending induction in the finite
   filtration gives this vanishing for H^r(C). Use the short-exact-sequence triangle,
   triangulated derived global sections, and its long exact sequence
   (lem-sf-derived-ses-triangle, def-weil-pbc-global-sections-functor,
   lem-weil-pbc-module-sheaves-enough-injectives,
   lem-weil-pbc-derived-direct-image-triangulated, lem-sf-derived-homology-long-exact).
   These calculations can all be made with underlying abelian sheaves; no claim that
   an injective module sheaf is injective as an abelian sheaf is needed.
5. For `t >= 2d-2`, each H^r(C)[-r] has vanishing degree-t hypercohomology by step 4.
   Induct up the finite ordinary truncation filtration, from tau_le_0 C = 0 to
   tau_le_(2d-4) C = C, using lem-weil-pbc-truncation-triangle and the long exact sequence.
   Thus H^t(U,C) = 0 for `t >= 2d-2`; the d = 2 case follows from C = 0 directly.
6. For `q >= 2d`, the long exact sequence of step 1 has outer groups
   H^(q-2)(U,C) and H^(q-1)(U,C), both zero by step 5. Its middle map is the asserted
   H^(q-1)(alpha followed by truncation), so that map is an isomorphism. -/
theorem isIso_punctured_perverse_high_comparison
    (ell n : ℕ) (_hell : Nat.Prime ell) (_hn : 1 ≤ n)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsStrictlyHenselianLocalRing R]
    (_hexc : IsExcellent R)
    (_hnormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (d : ℕ) (_hd : 2 ≤ d) (_hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (_hellunit : IsUnit (ell : R))
    (X : Scheme.{u}) (e : X ≅ Spec (.of R)) (x : X)
    (_hx : e.hom x = IsLocalRing.closedPoint R)
    (U : X.Opens) (_hU : (U : Set X) = {x}ᶜ)
    (M : DerivedCategory.Plus
      (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))))
    (_hM : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ U.toScheme) (a : ℤ),
      ((2 * ENat.toNat (WithBot.unbotD 0
        (ringKrullDim (X.presheaf.stalk (U.ι (s default))))) - 2 : ℕ) : ℤ) < a →
      IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.homologyFunctor _ a).obj M.obj)))
    (alpha : constantComplex (ULift.{u + 1} (ZMod (ell ^ n))) U.toScheme ≅
      (DerivedCategory.TStructure.t.truncLE 0).obj M.obj)
    (q : ℤ) (_hq : 2 * (d : ℤ) ≤ q) :
    IsIso ((cohomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))
      U.toScheme (q - 1)).map
        (alpha.hom ≫ (DerivedCategory.TStructure.t.truncLEι 0).app M.obj)) := by
  sorry

end AlgebraicGeometry.Etale
