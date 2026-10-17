## What changed

Implemented the localizing-category argument for the three proper-pushforward adjoint
instances in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.
All existing declaration signatures, universes, instance visibility and definitions are
unchanged. The item adds two private proof imports and one proved private common helper.
No other existing Lean module is changed.

The new `BoundedConstructibleLocalizingClosure` module constructs the hull as an actual
intersection of replete triangulated object properties closed under ambient coproducts.
Its inclusion, universal property, triangulated structure and coproduct closure are proved.
Countable coproducts split idempotents inside the hull. Comparing that splitting with
an ambient retraction proves retract closure, matching the thick-subcategory convention
in the cited well-generation theorem.
Its transport criterion requires coproduct preservation only on the source hull, rather
than the entire ambient category. The latter distinction matters for adic coefficients.

`EllAdicProperLocalizingPushforward` constructs the actual restricted derived pushforward
using this criterion, existing bounded-constructible preservation, and the coproduct input.
Its shift structure, triangulatedness and coproduct preservation are proved.
`EllAdicLocalizingBrownRepresentability` proves that its Hom functors are cohomological,
checks their product preservation, applies the separate cohomological input, and assembles
the representations into an adjoint using the partial-adjoint API.

The item's helper lifts that right adjoint to bounded constructible objects, constructs
the two commuting functor squares, and restricts the adjunction along fully faithful
inclusions with `Adjunction.restrictFullyFaithful`. The three original instances specialize
this proof using the three constructors of the existing coefficient certificate.
The only selected adjoint data is governed by its adjunction universal property.

All seven delivered Lean modules compile through `lcompile.py --all`, without errors or
non-sorry warnings. The existing coefficient-generic consumer
`Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` was also freshly compiled against
the repaired overlay (exit 0, 1.9 seconds), without changing its source. Its temporary
sandbox copy was removed before delivery. No full-library build was run.

## Proved and sorry left

The original item has three proof holes, all discharged:

- `AlgebraicGeometry.ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`
- `AlgebraicGeometry.ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`
- `AlgebraicGeometry.ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`

There are zero remaining holes in the item. The delivery adds exactly three holes, each
in its own new module, in the same namespace:

- `ellAdic_localizingLowerStar_preservesCoproducts`, node
  `lem-sfb-adic-proper-localizing-coproducts`. Still needs the proper unbounded-window
  calculation on ind-constructible cohomology, with the integral bound `[0, 2d+1]`, and
  identification of the canonical coproduct comparison. The node and docstring give
  the rational, finite-subextension algebraic-closure, and integral cases separately.
- `ellAdic_localizing_cohomological_isRepresentable`, node
  `lem-sfb-adic-localizing-cohomological-representability`. Still needs essential smallness
  from finite presentation/descent data and bounded Postnikov extensions, and the
  well-generated version of Brown representability. The exact ambient and indexing
  universes are specified. Compactness of the constructible generators is not assumed.
- `ellAdic_localizing_rightAdjoint_obj_boundedConstructible`, node
  `lem-sfb-adic-localizing-exceptional-constructible`. Still needs geometric restriction:
  the smooth projection calculation by the diagonal/trace, the closed-immersion
  localization calculation, finite affine factorization and gluing, and the compatible
  integral torsion-level construction. It is a preservation theorem for an already
  supplied adjoint, and does not assert its existence.

This is a decomposition of the three original holes into three shared inputs, with
substantial categorical glue proved. The local count is three closed and three added;
it is not an end-to-end proof of the geometric theorem. The three remaining statements
are distinct parts of the argument, not renamed versions of an original instance.
No private theorem or definition contains a hole. The other new declarations are proved.

## No longer needed

The original private direct import `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`
is replaced by the two localizing proof imports; they already import that coefficient
interface. No existing module is withdrawn or claimed globally unreachable. Both
original public imports remain necessary. Unused exploratory proof imports
were removed from the new hull module: `Mathlib.CategoryTheory.Triangulated.Orthogonal` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`. The hull
uses the smaller constructible-derived-category and module-object basic imports instead.
The source bounded-constructible module is still needed privately by the proper
pushforward proof for the preservation theorem.

The cohomological input imports the homological-functor and opposite-pretriangulated
interfaces its statement needs. Its former `Triangulated.Yoneda` public import is
replaced by a private import in the Brown assembly proof, where that theorem is used;
the redundant direct `Triangulated.Opposite.Basic` import is removed.

The Brown branch does not require `det-brown-hypotheses-generation`,
`sk-thm-constructible-compactness`, or the compactness clauses of
`det-prop-int-compactness-compact`. Their modules were not imported. The direct-sum
clauses of `det-prop-int-compactness-direct-sums` remain in the coproduct proof plan.
The smallness argument is applied directly to the library's finite-presentation predicate;
the Brown input itself does not need the finite-Tor comparison node.
These are dependency choices for this proof, not assertions that other targets no longer
use those nodes. No unit statement or realized unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was refused because the item file changed after its delivery
base. This repair starts from the current repository file, including both existing
`[IsFinitenessCoefficient ℓ Λ]` assumptions in the compactification and chosen sections,
and reapplies the retained three-instance proof. Neither coefficient assumption is removed.
The shared localizing-pushforward proof now derives `IsFinitenessCoefficient` by cases
on its adic certificate. Its public signature is unchanged. The private bounded helper
receives the coefficient class explicitly, inferred in the three concrete instances.
This is a source repair against the current interface, not an unchanged re-push.

The earlier report's timing and validator diagnoses are obsolete. All compilation in
this repair uses `lcompile.py` on the project server. The retained split-offs remain
exactly the three geometric/representability statements listed above; this repair adds
no further holes. No project tool was changed or bypassed.

The three original node plans already refer to four localizing-interface node IDs which
have no node files or Lean modules in the supplied repository. Those interfaces have now
been constructed or stated, with two further, strictly smaller analytic inputs separated
from their categorical consequences. The existing coefficient-generic proper-adjoint
interface imports this item and specializes its instances, so importing it here would
be circular. The general Grothendieck-derived Brown theorem concerns the entire derived
category and does not directly supply Brown on this localizing full subcategory.

STATEMENT-DISPUTED: the compactness clause (1) of the source unit `sk-thm-existence`,
read over its arbitrary standing base field, cannot justify this item. The reviewed
node `det-brown-hypotheses-generation` explicitly identifies the infinite-cohomological-
dimension obstruction and restricts its own compact-generation claim to an algebraic
closure of a finite field. The item has no such hypothesis. Its statements are unchanged;
the new Brown proof plan uses well generation instead. Its precise sources are Neeman,
*On the derived category of sheaves on a manifold*, Theorem 0.2 (derived categories of
arbitrary Grothendieck abelian categories), and Krause, *Localization theory for
triangulated categories*, Theorem 7.2.1 (set-generated localizing subcategories) and
Theorem 5.1.1 (perfect-generator Brown representability).

WANTED: Neeman's above paper, Documenta Mathematica 6 (2001), 483--488, Theorem 0.2,
and Krause's above paper, arXiv:0806.1324, Theorems 7.2.1 and 5.1.1, for the new
cohomological node. Primary texts checked at
https://www.maths.tcd.ie/EMIS/journals/DMJDMV/vol-06/19.pdf and
https://webhomes.maths.ed.ac.uk/~v1ranick/papers/krause2.pdf .
The repository's literature lists were not edited.

The library constructibility predicate uses arbitrary finite presentation matrices, whereas
the source's adic definition uses finite constant local models. These are not equivalent
on arbitrary schemes (`det-def-sfb-constructible-local-model` gives a counterexample).
Here the schemes and strata are Noetherian. The remaining geometric proof plans explicitly
require the existing field/Qbar local-triviality results and integral torsion-chart/local-
free-resolution results to make the coefficient comparison; they do not silently identify
the two definitions in general.

The current `boundedConstructible_rightDerivedLowerStar_obj` and restricted
pushforward now require `IsFinitenessCoefficient`. The retained proof was written before
that restriction. The certificate bridge described above supplies exactly the needed
instance for the three adic families, without restoring arbitrary-coefficient finiteness.
Its existing node `lem-sfb-dc-lower-star-preserves` remains a dependency.

## New nodes

Change records: `coord/changes/isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj.md`, `coord/changes/isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj.md`, and `coord/changes/isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj.md`.


`def-sfb-bounded-constructible-localizing-closure`: actual intersection construction and
proved closure/transport/inclusion API in `BoundedConstructibleLocalizingClosure`.

`lem-sfb-adic-proper-localizing-coproducts`: the first remaining input, restricted to the
source hull and with the ambient target; not coproduct preservation on all adic complexes.

`lem-sfb-adic-proper-localizing-pushforward`: proved restriction of the actual ambient
functor and its structural API in `EllAdicProperLocalizingPushforward`.

`lem-sfb-adic-localizing-cohomological-representability`: the second remaining input,
with a well-generated proof plan covering the unchanged arbitrary base field.

`lem-sfb-adic-localizing-brown-representability`: proved Hom-representation/adjoint assembly
in `EllAdicLocalizingBrownRepresentability`, using the cohomological input.

`lem-sfb-adic-localizing-exceptional-constructible`: the third remaining input, geometric
preservation for any supplied right adjoint. Its adjunction determines the object up to
the isomorphism under which constructibility is invariant.

The six new nodes have matching Lean records, actual three-kind search evidence and
proof-dependency lists. Source paths exist and their dependency graph has no new cycle.
The three original node copies change only `proof`, `proof_deps` and `proof_origin`.
The three retained change records describe the instance proof changes; no existing
statement, definition, public import or consumer source is changed. The dispatcher
reserves the independent second reading for the next worker; none is claimed here.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
