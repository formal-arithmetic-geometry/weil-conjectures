/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSubtrusive
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

/-! # Subtrusive topology and descent of quasi-compactness

Source: Rydh, Submersions and effective descent of étale morphisms, Corollary (1.5),
Proposition (1.7)(iii), Remark (1.8), Definition (2.2), the paragraph before
Proposition (2.4), Proposition (2.4)(ii), and Remark (2.5)(2c), pp.5--8
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

## Main statements

* Universal subtrusiveness implies universal Zariski submersiveness.
* Affine tests suffice, and universal subtrusiveness is stable under base change,
  composition, and passing from a composite to its second factor.
* Universally open surjections, including surjective representable étale maps, qualify.
* Quasi-compactness is detected after universally subtrusive base change.

Quasi-compact spaces use `CompactSpace (Point F)`; quasi-compact maps use the existing
`MapIsQuasiCompact`. Relative quasi-separatedness is quasi-compactness of
`pullback.diagonal f`; absolute quasi-separatedness is the existing affine-test predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universal subtrusiveness implies universal submersiveness for the Zariski topology.
Source: Rydh, Corollary (1.5), Remark (1.8) and paragraph before Proposition (2.4)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: by [lem-sfb-space-constructible-topology-comparison], a subset is Zariski closed
exactly when it is constructible closed and stable under specialization. On each affine
test, a closed inverse image descends to a constructible closed set by the quotient
condition; lifting specialization pairs makes the descended set specialization stable.
This proves the Zariski quotient condition on affine tests. For any space base change,
use affine étale charts from [lem-a1-space-affine-etale-cover]. The point image formula
and continuity of [lem-a1-space-point-open-calculus] give surjectivity and allow the
closed-set condition to be checked on these charts. Their final topology from
[def-a1-space-point-topology] yields the quotient assertion on the whole base change. -/
theorem universallySubtrusive_universallySubmersive {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hf : MapIsUniversallySubtrusive f.hom.hom) :
    MapIsUniversallySubmersive f.hom.hom := by
  sorry

/-- The affine tests defining universal subtrusiveness suffice for every quasi-separated
algebraic-space base change, including the constructible quotient and pair-lifting clauses.
Source: Rydh, Remark (1.8), Definition (2.2) and Proposition (2.4)(ii)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: cover the base change by affine étale charts using [lem-a1-space-affine-etale-cover].
Constructible closedness is detected there by [lem-sfb-space-constructible-topology-comparison],
and surjectivity by [lem-a1-space-point-open-calculus]. Lift the specialized point to a chart,
then lift its generalization in that same chart by [lem-sfb-open-space-generization-lifting].
The affine subtrusive test lifts the pair to the pullback, and projection preserves
specialization. Conversely, affine schemes are quasi-separated by
[lem-weil-pbc-affine-scheme-qcqs], so the asserted tests include all defining affine tests.
All products remain quasi-separated: the identity
`U ×_(X ×_Y W) V = (U ×_X V) ×_(U ×_Spec Z V) (U ×_W V)` reduces their affine diagonal
tests to [lem-sfb-qcqs-space-fibre-product] and [lem-weil-pbc-affine-scheme-qcqs]. -/
theorem universallySubtrusive_iff_space_tests {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y) :
    MapIsUniversallySubtrusive f.hom.hom ↔
      ∀ (W : AlgebraicSpace S), IsAbsolutelyQuasiSeparated W → ∀ g : W ⟶ Y,
        MapIsSubtrusive (Limits.pullback.snd f.hom.hom g.hom.hom) := by
  sorry

/-- Affine scheme tests also suffice for universal Zariski submersiveness.
Source: Rydh, Remark (1.8), pp.6--7
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: for an arbitrary algebraic-space base change choose an affine étale presentation
by [lem-a1-space-affine-etale-cover]. The affine quotient tests detect closed sets on each
chart, and [def-a1-space-point-topology] detects them on the target. Surjectivity follows
chartwise from [lem-a1-space-point-open-calculus]. Conversely, representable schemes
are algebraic spaces, so arbitrary space tests contain the affine scheme tests. -/
theorem universallySubmersive_iff_affine_tests {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y) :
    MapIsUniversallySubmersive f.hom.hom ↔
      ∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj), IsAffine T.left →
        Topology.IsQuotientMap (mapPoint (Limits.pullback.snd f.hom.hom a)) := by
  sorry

/-- Universal subtrusiveness is preserved by arbitrary base change between
quasi-separated spaces; the conclusion uses the canonical sheaf pullback projection.
Source: Rydh, Definition (2.2) and Remark (1.8)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: for an affine test `T → W`, associate the two fibre products using
[lem-trf-space-fibre-products-etale-covers]. The projection being tested identifies with
the base change of `f` along `T → W → Y`, which is subtrusive by hypothesis. The point
topologies are invariant under this isomorphism by [lem-a1-space-point-open-calculus]
and [lem-sfb-space-constructible-topology-comparison]. -/
theorem universallySubtrusive_baseChange {S : Scheme.{u}}
    (X Y W : AlgebraicSpace S) (f : X ⟶ Y) (g : W ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hW : IsAbsolutelyQuasiSeparated W)
    (_hf : MapIsUniversallySubtrusive f.hom.hom) :
    MapIsUniversallySubtrusive (Limits.pullback.snd f.hom.hom g.hom.hom) := by
  sorry

/-- Universal subtrusiveness is closed under composition.
Source: Rydh, paragraph before Proposition (2.4)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: over an affine test of `Z`, the second map is subtrusive by definition; the first
is subtrusive over the resulting quasi-separated space by the space-test criterion.
Compose the surjective constructible quotient maps. Lift a specialization pair first to
the middle space, then to the source. Fibre-product associativity from
[lem-trf-space-fibre-products-etale-covers] identifies this with the tested composite.
The quasi-separatedness of the products is the affine diagonal argument using
[lem-sfb-qcqs-space-fibre-product] and [lem-weil-pbc-affine-scheme-qcqs]. -/
theorem universallySubtrusive_comp {S : Scheme.{u}}
    (X Y Z : AlgebraicSpace S) (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hZ : IsAbsolutelyQuasiSeparated Z)
    (_hf : MapIsUniversallySubtrusive f.hom.hom)
    (_hg : MapIsUniversallySubtrusive g.hom.hom) :
    MapIsUniversallySubtrusive (f ≫ g).hom.hom := by
  sorry

/-- If a composite is universally subtrusive, its second factor is universally subtrusive.
No surjectivity or subtrusiveness of the first factor is assumed.
Source: Rydh, paragraph before Proposition (2.4)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: base change to any affine test of `Z`. Surjectivity of the composite implies that
of the second map. A subset with constructible closed inverse image under the second
map has closed inverse image under the composite, by constructible continuity from
[lem-sfb-space-constructible-topology-comparison], hence is closed. Continuity gives the
converse. Lift a specialization pair through the composite, then project to the middle
space using continuity from [lem-a1-space-point-open-calculus]. -/
theorem universallySubtrusive_of_comp {S : Scheme.{u}}
    (X Y Z : AlgebraicSpace S) (f : X ⟶ Y) (g : Y ⟶ Z)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hZ : IsAbsolutelyQuasiSeparated Z)
    (_hfg : MapIsUniversallySubtrusive (f ≫ g).hom.hom) :
    MapIsUniversallySubtrusive g.hom.hom := by
  sorry

/-- Universally open maps surjective on points are universally subtrusive.
Source: Rydh, Proposition (1.6)(iii) and Remark (2.5)(2c)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: over an affine target, images of affine étale source charts are open and cover the
target, by [lem-a1-space-affine-etale-cover] and [lem-a1-space-point-open-calculus].
Choose finitely many using [lem-weil-pbc-affine-scheme-qcqs]. Their coproduct exists by
[lem-weil-pbc-scheme-coproduct-family] and is qcqs. Its surjection to the affine target
is quasi-compact by [lem-sfb-space-qcqs-permanence], hence constructible closed by
[lem-sfb-space-quasicompact-constructible-closed] and therefore constructible quotient.
Its factorization through the original source makes that source map quotient too, using
[lem-sfb-space-constructible-topology-comparison]. Finally lift the specialized point by
surjectivity, and its generalization by [lem-sfb-open-space-generization-lifting]. -/
theorem universallySubtrusive_of_universallyOpen_surjective {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_ho : MapIsUniversallyOpen f) (_hs : Function.Surjective (mapPoint f.hom.hom)) :
    MapIsUniversallySubtrusive f.hom.hom := by
  sorry

/-- Surjective representable étale morphisms are universally subtrusive.
Source: Rydh, Remark (2.5)(2c); Stacks, Tag 03IR
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: representable étaleness and point surjectivity persist under arbitrary base change
by [lem-trf-space-representable-etale-scheme-tests] and [lem-a1-space-point-open-calculus].
The latter makes each point map open. Thus the map is universally open and surjective,
and the preceding universally open criterion applies. -/
theorem universallySubtrusive_of_etale_surjective {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_he : IsEtale f.hom.hom) (_hs : Function.Surjective (mapPoint f.hom.hom)) :
    MapIsUniversallySubtrusive f.hom.hom := by
  sorry

/-- Quasi-compactness is detected after universally subtrusive base change.
Source: Rydh, Proposition (1.7)(iii) and Remark (1.8)
(blueprint: lem-sfb-subtrusive-topological-descent-calculus).

Proof: the forward implication is base-change stability
[lem-sfb-space-quasicompact-affine-tests]. For the converse fix an affine test `T → Y`.
Write `V = Z ×_Y T`, `Q = Y' ×_Y T` and `V' = V ×_T Q`. The assumed quasi-compact
map `V' → Q` is constructible closed by [lem-sfb-space-quasicompact-constructible-closed].
For constructible closed `F ⊆ V`, continuity from
[lem-sfb-space-constructible-topology-comparison] and the point image formula from
[lem-a1-space-point-open-calculus] give `a_T⁻¹(f(F)) = f'(p⁻¹(F))`. The quotient
condition on `Q → T` makes `f(F)` closed, so `V → T` is constructible closed.
For `t ∈ T`, [def-weil-residue-field] and [def-weil-affine-spectrum] give `Spec κ(t)`.
Surjectivity of `Q → T` and [def-a1-algebraic-space-point-classes] yield a field extension
`L/κ(t)` and a point of `Q` over it. The corresponding `V_L` is quasi-compact and
surjects onto `V_κ(t)`, which is therefore quasi-compact. By
[lem-sfb-qc-space-affine-etale-atlas] it has an affine surjective étale atlas. That atlas
is constructibly compact by [lem-weil-pbc-affine-scheme-qcqs],
[lem-weil-pbc-qcqs-scheme-spectral] and
[lem-weil-pbc-spectral-constructible-topology-quasi-compact]. Its continuous point image
in `V` is exactly the point fibre, making that fibre constructibly compact.
Finally, for a constructible open cover of `V`, finitely many members cover each fibre.
If their union is `O_t`, constructible closedness makes `T \ f(V \ O_t)` an open
neighborhood of `t` whose inverse image lies in `O_t`. Compactness of constructible `T`
gives finitely many such neighborhoods, hence a finite subcover of `V`. The constructible
topology is finer than Zariski by [lem-sfb-space-constructible-topology-comparison], so
`V` is Zariski quasi-compact. This is exactly the affine-test definition for `b`.
Empty fibres and the empty affine test are covered by the same empty finite-cover argument. -/
theorem quasiCompact_iff_subtrusive_baseChange {S : Scheme.{u}}
    (Y' Y Z : AlgebraicSpace S) (a : Y' ⟶ Y) (b : Z ⟶ Y)
    (_hY' : IsAbsolutelyQuasiSeparated Y') (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hZ : IsAbsolutelyQuasiSeparated Z)
    (_ha : MapIsUniversallySubtrusive a.hom.hom) :
    MapIsQuasiCompact b.hom.hom ↔
      MapIsQuasiCompact (Limits.pullback.snd b.hom.hom a.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
