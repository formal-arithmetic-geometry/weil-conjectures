module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Noetherian affine charts at fibre component generic points

Source: Stacks Project, Tag 01T6 (lemma-finite-type-noetherian), applied over the
residue field, and Tag 00ES (lemma-irreducible), the affine closure formula.
(blueprint: lem-trf-fibre-component-noetherian-affine-chart)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type fibre is locally Noetherian, and a generic point of any
irreducible component has a Noetherian affine neighbourhood on which it is a minimal prime.
The prime is identified using the canonical isomorphism `hU.isoSpec`.

Source: Stacks Project, Tag 01T6 (lemma-finite-type-noetherian), and Tag 00ES
(lemma-irreducible).
(blueprint: lem-trf-fibre-component-noetherian-affine-chart)

Proof:
1. The residue field at `t` is Noetherian: any ideal containing a nonzero element
contains its inverse multiple 1, so its only ideals are (0) and (1). Its spectrum
is locally Noetherian by the single affine chart
(def-pc-scheme-fibre, def-weil-affine-spectrum, def-weil-pbc-noetherian-ring,
pqf-def-locnoeth).
2. The fibre projection to this spectrum is locally of finite type by
lem-weil-pbc-lft-base-change. Apply pqf-lem-locnoeth-lft to obtain local Noetherianity.
3. Choose a Noetherian affine open neighbourhood of `y` from the cover in
pqf-def-locnoeth. Its section ring is Noetherian; the affine spectrum identification
is the canonical isomorphism with the spectrum of this ring.
4. If a prime `q` lies inside the prime of `y`, let `z` be its point on the chart.
By lem-weil-pbc-spec-irreducible-closed-subsets-primes, `y` belongs to the closure
of `z`. This closure is closed and irreducible and contains the closure of `y`,
which is `C` by def-sc-generic-point. Maximality of `C` as an irreducible component
(def-weil-irreducible-components) implies that the two closures are equal.
Intersecting with the chart shows that `z` belongs to the chart closure of `y`.
The same affine closure formula gives the reverse prime inclusion, hence equality.
-/
theorem exists_noetherian_affine_chart_of_fibre_component_genericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (t : S)
    (C : Set (f.fiber t)) (_hC : C ∈ irreducibleComponents (f.fiber t))
    (y : f.fiber t) (_hy : IsGenericPoint y C) :
    IsLocallyNoetherian (f.fiber t) ∧
      ∃ (U : (f.fiber t).Opens) (hU : IsAffineOpen U) (hyU : y ∈ U),
        IsNoetherianRing Γ(f.fiber t, U) ∧
          ∀ q : Ideal Γ(f.fiber t, U), q.IsPrime →
            q ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
              q = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
  sorry

end AlgebraicGeometry
