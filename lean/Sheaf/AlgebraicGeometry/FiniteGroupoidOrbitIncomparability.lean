module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Inseparable

/-! # Incomparability of points in finite groupoid orbits

Source: Stacks Project, More on Groupoids, Tag 0ABG,
`lemma-no-specializations-map-to-same-point`
(blueprint: lem-sfb-finite-groupoid-orbit-incomparability).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Distinct points in an orbit of a groupoid scheme with finite source and target do not
specialize to one another. The orbit of `x` is the image `t.base '' (s.base ⁻¹' {x})`.

Source: Stacks Project, More on Groupoids, Tag 0ABG
(blueprint: lem-sfb-finite-groupoid-orbit-incomparability).

Proof:
1. Point-arrows with matching source and target compose after passing to a common residue
   field extension. The tensor product of their residue fields over the common residue field
   is nonzero by lem-weil-common-extension-fields-tensor-nontrivial, and has a prime by
   lem-weil-common-extension-fields-maximal-ideal. The description of fibre-product points
   (lem-weil-pbc-fibre-product-points) gives a point of the composable-arrow scheme.
   The laws of def-a1-groupoid-scheme give its source and target. Identities show that `x`
   belongs to its orbit; composition keeps successive targets in this orbit.
2. A finite morphism is integral (pqf-lem-finite-integral-lft). Two comparable points in one
   fibre lie in an affine inverse image of an affine neighbourhood of the common image.
   Their primes are comparable (def-weil-affine-spectrum), and have equal contractions.
   Integral incomparability (pqf-lem-incomparability) makes them equal. Hence a finite
   morphism has no strict specialization inside a fibre.
3. By lem-weil-pbc-finite-closed-map-finite-fibres, the source fibre and its target image
   are finite and the source map is closed. Given an arrow and a strict specialization of
   its source, lift that specialization along the closed source map using
   lem-trf-closed-map-specializing. Continuity of the target gives a target specialization;
   it is strict, since otherwise step 2 for the target map would identify the two arrows.
4. If `x` strictly specializes to a point `y` in its orbit, choose an arrow from `x` to `y`.
   Repeatedly use step 3 to lift the source specialization, and take the new target as the
   next point. Step 1 keeps every new point in the orbit, while step 3 makes each successive
   specialization strict. This constructs such a chain of every finite length.
5. Specialization on a scheme is antisymmetric by lem-sc-scheme-sober. Thus all points of
   this strict chain are distinct: a repetition, together with transitivity, would give
   reverse specialization across a strict step. A chain longer than the finite orbit is
   impossible. This excludes `y` from the singleton closure of `x`. Inversion and composition
   identify the orbits of points in a common orbit, giving the assertion for every ordered
   pair of distinct points in that orbit. -/
theorem IsGroupoidScheme.not_mem_closure_singleton_of_isFinite
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (_hG : IsGroupoidScheme s t e i c)
    [IsFinite s] [IsFinite t] (x y : U) (_hxy : x ≠ y)
    (_hy : y ∈ t.base '' (s.base ⁻¹' {x})) : y ∉ closure ({x} : Set U) := by
  sorry

end AlgebraicGeometry
