/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-!
# Canonical pullback in degrees zero and one

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, proper and affine cases in degrees zero and one
(blueprint: lem-sc-constant-low-degree-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, proper and affine cases in degrees zero and one
(blueprint: lem-sc-constant-low-degree-base-change).

Proof: baseChange_curve preserves the smooth connected curve hypotheses. Choose a primitive
root in k and transport it to K; exponentiation by it identifies constant coefficients with
roots of unity and commutes with pullback. In degree zero both groups are the roots of unity
in the ground fields, and the primitive-root coordinates identify the map with the identity.
For a proper curve, divisibility of global units and the Kummer sequence identify degree one
with Picard n-torsion. Identify this with Jacobian n-torsion;
genus_jacobian_invariant and the finite-etale n-torsion assertion of thm-av-final make its
pullback bijective. For an affine curve, the Kummer short exact ladder has bijective outer
maps by units_quotient_base_change and the affine Picard-torsion clause of
kummer_base_change_compatibility, so its middle map in degree one is bijective by the short
five lemma. The proper-or-affine dichotomy exhausts all connected smooth curves.
For n = 1 the groups are zero and the same argument applies. -/
theorem IsConnectedCurve.constant_low_degree_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (_hfin : (Set.range c.i.base)ᶜ.Finite)
    (_hclosed : ∀ x ∈ (Set.range c.i.base)ᶜ, IsClosed ({x} : Set c.Z))
    (n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0)
    (r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q)
    (hr : (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q))) :
    ∀ q : ℕ, q ≤ 1 → Function.Bijective (r q) := by sorry

end AlgebraicGeometry
