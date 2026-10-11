/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.HilbertToPicardMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Surjectivity of the Hilbert-to-Picard morphism

Source: Stacks Project, Tag 0BA0, clause (5) and proof, fourth paragraph
(blueprint: lem-sc-hilb-to-pic-surjective).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- For a smooth projective geometrically integral curve over a separably closed field,
the morphism from the Hilbert scheme of degree `d` divisors to the degree-`d` Picard
scheme is surjective when `d` is at least the genus.
Source: Stacks Project, Tag 0BA0, clause (5) and proof, fourth paragraph.
(blueprint: lem-sc-hilb-to-pic-surjective)

Proof: (1) The integral smooth curve has a rational point over the separably closed
field (lem-pc-rational-points-dense). After any field extension it is integral,
proper and one-dimensional, with H⁰(O) = K, h¹(O) = g, and no higher coherent
cohomology (prop-pc-xk-integral, lem-pc-projective-proper, lem-pc-vanishing-above-dim,
lem-pc-euler-characteristic-well-defined); hence χ(O) = 1 - g.
(2) A K-point of P corresponds to a Picard class represented by an invertible module
L on C_K, since the rational point splits the Picard functor (thm-pc-pic-split,
lem-pc-rational-hyp). Its degree is d by the definition of the degree component
(def-pd-degree-morphism, def-pd-fibrewise-degree, def-pc-degree-line-bundle).
(3) Thus χ(L) = d + 1 - g ≥ 1, so h⁰(L) ≥ 1 and L has a nonzero section
(def-pc-euler-characteristic).
(4) Its zero scheme D is an effective Cartier divisor on the integral curve and
L ≅ O(D) (lem-pc-nonzero-section-integral-cartier, lem-pc-zero-scheme-divisor-iso,
def-pc-divisor-line-bundle).
(5) D is finite over K and its length equals deg O(D) = d; over a field it is flat
and finitely presented, hence a degree-d Hilbert point
(lem-pc-cartier-divisor-finite-over-field, lem-pc-degree-base-change,
def-pc-finite-locally-free, def-pc-hilb-functor).
(6) Under the Hilbert representing equivalence D gives x : Spec K ⟶ H. The
classifying equality below and lem-sc-hilb-to-pic-morphism identify x ≫ γ with
the original Picard point, by naturality and Yoneda (lem-pc-yoneda).
(7) Apply this to K = κ(p) for each point p of P, with its canonical residue-field
point (def-weil-residue-field, lem-weil-pbc-residue-field-point-naturality).
The resulting lift maps to p, proving surjectivity on underlying points
(def-weil-surjective-morphism).
-/
theorem surjective_hilbertToPicardMorphism {k : Type u} [Field k] [IsSepClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]
    [GeometricallyIntegral f] (d : ℕ) (hd : @Scheme.arithmeticGenus k _ C ⟨f⟩ ≤ d)
    (H P : Over (Spec (.of k))) (eH : (hilbertPresheaf f d).RepresentableBy H)
    (eP : (picardFunctorDegree f d).obj.RepresentableBy P)
    (L : (pullback f H.hom).Pic)
    (hL : L ∈ (picardSubfunctorDegree f d).obj (op H))
    (hD : Nonempty ((fromSkeleton _).obj L.val ≅ ((eH.homEquiv (𝟙 H)).1).toModulesᵛ))
    (γ : H ⟶ P)
    (hγ : eP.homEquiv γ =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f d).toFunctor).app (op H) ⟨L, hL⟩) :
    Surjective γ.left := by
  sorry

end AlgebraicGeometry
