/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison
import WeilConjectures.Algebra.Homology.TorIndependentKFlatResolutionTensor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Topology.Sheaves.Stalks

/-! # Tor-independent base change for closed pushforward

Source: Stacks Project, perfect.tex, Tag 0E23,
lemma-compare-base-change-closed-immersion
(blueprint: lem-sfb-tor-independent-closed-pushforward-comparison).

The comparison is an isomorphism of functors on the entire unbounded derived category
of structure-sheaf modules. Its forward components are the recorded canonical mates.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- In a Tor-independent square with a closed immersion, derived pullback commutes
with closed pushforward, naturally on all unbounded complexes. The forward components
are exactly `schemeDerivedBaseChangeMap`: transpose under `Li'^* ⊣ Ri'_*` the composition
comparison `Li'^* Lf^* Ri_* K ≅ Lg^* Li^* Ri_* K` followed by `Lg^*` of the counit.
The derived-category instance family chooses localizations; it adds no geometric,
boundedness, quasi-coherence, Noetherianity or finiteness assumption.

Source: Stacks Project, perfect.tex, Tag 0E23,
lemma-compare-base-change-closed-immersion
(blueprint: lem-sfb-tor-independent-closed-pushforward-comparison).

Proof:
1. Apply lem-sfb-closed-immersion-derived-exchange-stalk-formula to this canonical mate.
At a point of the closed image write R = O_{X,x}, A = O_{Z,z}, B = O_{X',x'},
and C = O_{Z',z'}. It identifies C with A tensor_R B and identifies the stalk of
this mate with the canonical ring comparison for M = K_z. Off the closed image
both stalk objects vanish.
2. Use lem-pc-source-module-kflat-resolution over A and over R to choose an A-K-flat
representative Q of M and an R-K-flat resolution s : P -> Q restricted to R.
By lem-pc-affine-derived-base-change-comparison-map the ring comparison is represented
by P tensor_R B -> Q tensor_R B, followed by the balancing isomorphism
Q tensor_R B = Q tensor_A (A tensor_R B). This sends q tensor b to
q tensor (1 tensor b), with inverse q tensor (a tensor b) mapping to aq tensor b.
3. Stalkwise Tor independence and lem-pc-tor-independent-kflat-resolution-tensor
make s tensor_R B a quasi-isomorphism. Hence the ring comparison is invertible
in the unbounded derived category (def-weil-abstract-derived-category).
4. All stalk comparisons are invertible, including zero-to-zero outside the image.
By lem-weil-pbc-module-stalk-exact, stalks commute with cohomology. Apply
lem-weil-pbc-module-iso-on-stalks to each cohomology map, then
lem-weil-pbc-unbounded-derived-iso-cohomology to the mate itself. Naturality follows
from the composition comparisons, counit and adjunction Hom equivalence; the component
inverses are natural by cancelling invertible components in that naturality identity. -/
theorem torIndependent_closedPushforward_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Z X X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X' ⟶ X)
    (hTor : PullbackStalkTensor.IsTorIndependent i f) :
    ∃ e : schemeDerivedDirectImage i ⋙ derivedPullback f ≅
        derivedPullback (pullback.fst i f) ⋙ schemeDerivedDirectImage (pullback.snd i f),
      ∀ K : schemeDerivedCategory Z,
        e.hom.app K = schemeDerivedBaseChangeMap i (pullback.snd i f) f
          (pullback.fst i f) pullback.condition K := by
  sorry

end AlgebraicGeometry
