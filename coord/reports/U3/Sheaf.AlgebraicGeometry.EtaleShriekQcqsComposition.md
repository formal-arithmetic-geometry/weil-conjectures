## What changed

Proved `AlgebraicGeometry.Etale.nonempty_iso_etaleShriek_qcqs_compactification_comp`
with its complete original signature. The Lean proof follows the compatible triangle,
open-extension composition, open/proper interchange, and compactification comparisons
of Stacks `more-etale.tex`, Tag 0F7J (`lemma-shriek-composition`), first paragraph and
four-line calculation; Tag 0F7I supplies comparisons between the chosen models.

The geometric theorem supplies the two actual compactifications `df` and `dfg`.
`openImmersionLowerShriekComp`, lifted by the exact-functor bounded-below API,
combines their open maps. Whiskering the stated interchange and associating the
four factors gives the displayed calculation. Direct images preserve injectives
because their inverse-image left adjoints preserve monomorphisms; consequently
`Functor.rightDerivedFunctorPlusCompIso'` applied to `lowerStarComp` supplies the
proper-map compositor directly on D+. The last two comparisons recover `cf` and
`cgf`, while `cg` is fixed throughout. These are local constructions inside a proof,
not definitions selecting arbitrary objects from existence theorems.

Updated only the item's DAG proof, proof dependencies and proof origin to describe
that implementation. Both existing public imports and all exported signatures stay
unchanged. Single-file launcher compilation passed cleanly (6.2 seconds in the final
version). File-level namespace openings remain exactly as before; pullback names
are qualified inside the proof.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Etale.nonempty_iso_etaleShriek_qcqs_compactification_comp`
(node `lem-weil-pbc-etale-shriek-qcqs-composition`).

Added 0 holes. There are no remaining `sorry`s in the delivered module and no
split-offs or new modules. This is a proof from existing named dependencies,
including the still-stated compatible-triangle and open/proper-interchange
lemmas; it does not assert that their transitive obligations are closed.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
and dependency node `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` from
this item's route. The proved source bounded-below compositor avoids the entire
general ringed-topos construction and its K-injective normalization; the theorem
only needs existence of a natural isomorphism. This reports pruning of this edge,
not a claim that the module is absent from every other target path.

Replaced `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` by its
smaller dependency `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence`.
The proof uses only the existing `rightDerivedLowerShriekOfCompactificationPlusIso`;
identity, cocycle and arbitrary-refinement coherence are unnecessary here. Its
independence node remains, since the comparison itself is still used.

Replaced the direct `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
import with `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`, which
provides the already-proved open compositor and publicly imports those definitions.
Removed redundant direct `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
`OpenImmersion.Comp` already exports it. Their definition, adjunction and exactness
nodes remain needed. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Step 4 over-specified the machinery: the actual fixed-coefficient, bounded-below
functors already have a proved composition API requiring only injective-object
preservation. There is no need to instantiate the much more general ringed-topos
statement or compare its existentially chosen derived functors with these ones.
The remaining geometric/interchange/choice-comparison steps fit as stated.
No statements or definitions were changed. No new mathematical edge cases are
introduced: the proof uses no nonemptiness of schemes, no nontriviality of the
finite ring, and no residue-characteristic restriction. Empty schemes, the zero
coefficient ring and identity morphisms retain the original theorem's scope.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
