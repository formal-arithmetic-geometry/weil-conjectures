/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-! # Descent across a finite-support cokernel

Source: Stacks Project, Tags 0A3Q and 0GJA, normalization and dense-open comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A constructible prime-annihilated sheaf with the eight curve assertions transfers
those assertions to a subsheaf whose cokernel vanishes on a dense open.
Source: Stacks Project, Tags 0A3Q, proof, and 0GJA, proof, remarks (a)--(d).
(blueprint: b3-finite-support-mono-assertions)

Proof: The dense-open complement in a finite-type curve is zero-dimensional. The
constructible cokernel, annihilated by ℓ, has finite stalks since Λ/(ℓ) is finite.
It is the closed direct image of its restriction to that complement. Finite direct
image and zero-dimensional cohomology show that it and its pullbacks have zero
positive cohomology, finite degree-zero cohomology, and bijective field-extension maps.
The short exact sequence gives isomorphisms from F to G in degrees at least two,
the exact sequence 0 → H⁰(F) → H⁰(G) → H⁰(Q) → H¹(F) → H¹(G) → 0.
These prove C1, C2 and finiteness. For C3 and C6, if ℓ equals the characteristic
use the primary branch, and otherwise use the invertible-order branch. If a
conditional hypothesis on F has the opposite torsion type, F is zero: stalks are
annihilated by two coprime integers. For C6, when ℓ differs from the characteristic
G has invertible torsion;
when ℓ equals the characteristic and F has invertible torsion, F is zero.
For C6 and C7, degree zero is the kernel of H⁰(G) → H⁰(Q). In degree one use
0 → coker(H⁰(G) → H⁰(Q)) → H¹(F) → H¹(G) → 0 and the short five lemma.
The bijective comparisons for G and Q give both kernel and cokernel comparisons;
in higher degrees use the isomorphisms with G. For C7 use properness of X.
For C8 lift a degree-two class using G, identify H²(F) with H²(G), and use
injectivity of H² of the pulled-back inclusion, since H¹ of the pulled-back Q is zero.
Empty complements, empty curves, and the zero coefficient quotient obey the same argument. -/
theorem IsCurve.Assertions.of_finite_support_mono {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] [Scheme.IsConstructibleSheaf G]
    [Scheme.IsConstructibleSheaf (cokernel α)] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (hℓ : ℓ • 𝟙 G = 0)
    (V : X.Opens) (hV : Dense (V : Set X))
    (hQ : IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj (cokernel α)))
    (H : IsCurve.Assertions Λ f G) : IsCurve.Assertions Λ f F := by sorry

end AlgebraicGeometry
