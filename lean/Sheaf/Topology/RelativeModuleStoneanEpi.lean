module

public import Sheaf.Topology.RelativeFiniteBundleModel
public import Mathlib.Topology.ExtremallyDisconnected

/-! # Detecting epimorphisms of relative continuous modules on Stonean tests

Source: Stacks Tags 03CN and 08YN and steps 1--2 of the relative finite-bundle
Roos argument (blueprint: lem-sfb-relative-module-stonean-epi).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace Profinite

/-- Epimorphisms of relative continuous modules are exactly the maps surjective on
sections over every test object with extremally disconnected domain.
Source: Stacks Tags 03CN and 08YN; steps 1--2 of lem-sfb-relative-finite-bundle-roos
(blueprint: lem-sfb-relative-module-stonean-epi).

Proof: forget the scalar action to abelian sheaves. This functor is faithful and
exact and reflects epimorphisms. An epimorphism is locally surjective. For a
section over an extremally disconnected test S, choose a finite jointly
surjective covering with local lifts. The disjoint union V of its domains maps
surjectively to S. The sheaf condition glues the lifts to a section on V:
the summands are clopen and disjoint, and sections on the empty object form the
zero group. Stonean projectivity gives a continuous section of V -> S. It is
a map over P because V -> P factors through S. Restriction along this section
is a lift over S, proving the forward implication. Conversely, every profinite
test Q admits a surjection S -> Q from a Stonean profinite space, for example
the ultrafilter space of its underlying discrete set. Compose with Q -> P to
make this a map in the slice. Surjectivity on S-sections lifts the restriction
of any section on Q, proving local surjectivity, hence epimorphy. Empty tests
and zero coefficient rings are included; no assumption on scalar actions or
finite presentation is used. -/
theorem relativeContinuousRing_epi_iff_stonean
    (P : Profinite.{u}) (T : Type v) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T]
    {M N : SheafOfModules.{max u v + 1} (relativeContinuousRing P T)} (f : M ⟶ N) :
    Epi f ↔ ∀ (Q : Over P) [ExtremallyDisconnected Q.left],
      Function.Surjective (f.val.app (op Q)) := by sorry

end Profinite
