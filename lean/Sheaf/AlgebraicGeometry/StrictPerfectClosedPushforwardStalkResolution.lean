/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Bounded projective resolutions of closed-pushforward stalks

Source: Stacks Project, Duality for Schemes, Tag 0A9U, hypothesis translation;
Cohomology of Sheaves, Tags 08C4 and 08CM; More on Algebra, Tag 066Q
(lemma-perfect-module).
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-resolution).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A specified strictly perfect local model of the ordinary pushforward in degree zero
along a closed immersion gives a bounded projective resolution of the source stalk
restricted to the target stalk. No Tor assertion or tensor test module is involved.

Source: Stacks Project, Tags 08C4 and 08CM, and More on Algebra, Tag 066Q
(lemma-perfect-module); hypothesis translation for Duality, Tag 0A9U.
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-resolution).

Proof. Closed-pushforward stalks identify the ordinary pushforward at i(x) with
restriction of scalars of the source stalk. Restriction to a neighbourhood preserves
the stalk, and the exact stalk functor preserves quasi-isomorphisms. Apply it to the
given derived isomorphism over U. Taking stalks of K thus gives a bounded complex
representing the restricted source stalk in degree zero. Each term is projective:
the finite-free retraction in
IsStrictlyPerfect becomes a retraction of a finite free module on stalks.
Starting at the highest positive nonzero degree, split the surjection onto the
last projective term, which exists by exactness in that degree. Remove the resulting
contractible two-term summand and repeat down to degree one. The remaining complex
is concentrated in nonpositive degrees, with projective terms, and its degree-zero
cokernel is the restricted source stalk. Reverse the indices to obtain an augmented
projective resolution indexed by natural numbers. The original lower bound for K
makes its terms zero above a natural-number bound. This works also for an acyclic
model: the restricted stalk is then zero, and its zero resolution suffices. -/
theorem strictPerfectClosedPushforward_stalkResolution
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (x : Z) (U : Y.Opens) (hx : i x ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hK : Y.IsStrictlyPerfect U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      DerivedCategory.Q.obj K) :
    ∃ (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) (n : ℕ),
      ∀ j : ℕ, n < j → IsZero (P.complex.X j) := by sorry

end AlgebraicGeometry
