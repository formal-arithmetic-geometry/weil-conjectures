module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum
import Mathlib.Topology.Constructible
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import WeilConjectures.RingTheory.QuasiFiniteAtPrime

/-!
# Quasi-finiteness at a closed fibre point with no other generalization

Source: Stacks Project, Morphisms of Schemes, Tag 01TH,
`lemma-quasi-finite-at-point-characterize`, implication (3) to (1)
(blueprint: lem-sfb-closed-fibre-point-quasifinite-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed point of a fibre with no other generalization in that fibre is quasi-finite.

Source: Stacks Project, Morphisms of Schemes, Tag 01TH,
`lemma-quasi-finite-at-point-characterize`, implication (3) to (1)
(blueprint: lem-sfb-closed-fibre-point-quasifinite-criterion).

Proof plan:
1. Choose affine opens `U = Spec A` about `y` and `V = Spec R` about `g y` with
   `g(U) ⊆ V`. Local finite type gives finitely many generators of `A` over `R`
   (def-weil-finite-type-morphism, def-weil-affine-spectrum). Tensoring these generators
   gives generators of the fibre ring `B = κ(p) ⊗[R] A` over `κ(p)`.
2. The fibre homeomorphism identifies `U ∩ Y_t` with `Spec B`
   (def-pc-scheme-fibre, lem-weil-pbc-fibre-spec-homeomorphism). The prime `b`
   corresponding to `y` is closed, and the closure hypothesis says its singleton is
   stable under generalization. Closure in a subspace is the intersection with ambient closure.
3. The one-point spectrum of `κ(p)` is Noetherian, so `Spec B` is Noetherian by
   lem-sfb-finite-type-noetherian-spectrum. Its closed singleton `{b}` is constructible
   by the Noetherian clause of def-weil-constructible-subset.
4. Apply lem-trf-spectrum-constructible-generalization-open to conclude that `{b}` is open.
5. The prime `b` contracts to the prime of `A` corresponding to `y`
   (lem-weil-pbc-fibre-spec-homeomorphism). Thus the finite-type map `R → A` is
   quasi-finite at that prime (def-weil-pbc-ring-map-quasi-finite-at-prime). The chosen
   affine opens give the witnesses for `IsQuasiFiniteAtPoint g y` (pqf-def-quasifinite).
-/
theorem isQuasiFiniteAtPoint_of_closed_fibre_no_other_generalization
    {Y T : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ T) [LocallyOfFiniteType g] (y : Y)
    (hclosed : IsClosed ({g.asFiber y} : Set (g.fiber (g y))))
    (hgeneralization : ∀ y' : g.fiber (g y),
      g.asFiber y ∈ closure ({y'} : Set (g.fiber (g y))) → y' = g.asFiber y) :
    g.IsQuasiFiniteAtPoint y := by
  sorry

end AlgebraicGeometry.Scheme.Hom
