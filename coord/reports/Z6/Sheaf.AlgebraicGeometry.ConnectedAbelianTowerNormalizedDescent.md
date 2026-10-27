## What changed

The original theorem `AlgebraicGeometry.ProEtale.nonempty_connectedAbelianTowerNormalizedDescent`
now has a complete Lean proof assembling three strictly separate results: the
objectwise normalized splitting and monodromy calculation, equivariant morphism
descent for supplied splittings, and finite-frame descent. The proof constructs the
fibre functor, proves its identity and composition laws by the actual stalk functor,
constructs a FullyFaithful witness from the unique descended maps, and constructs
the natural fibre isomorphism. It then supplies every field of the original package.
No signature or conclusion was changed.

The constant-map fibre determination clause is proved directly, without another
hole. Finite constant representability and the clopen-coproduct calculation show
that a global section on a connected scheme is a constant label. Disjointness
makes constant labels injective on every nonempty pointed neighbourhood. Filtered
colimit equality then detects equality of labels from equality of germs. Naturality
and the sheafification adjunction extend this to equality of sheaf morphisms.
The proof includes empty finite sets.

`ConnectedAbelianTowerNormalizedData` contains the existing eight shared definitions,
verbatim. The original module publicly re-exports them and retains the package
structure in its original module. This dependency separation allows the three
lemmas to import the interfaces without a cycle. It changes no mathematical object.
The existing consumer `NormalizedFiniteSplittingOperations` needs no adaptation.
The change record is `coord/changes/connected-abelian-tower-normalized-data.md`.

The object module directly constructs the continuous action-label map and the
second-projection overlap map, with proved equations for both projections. The Hom
module directly defines the label map of a sheaf morphism from its geometric stalk
map and proves the cancellation equation. No public definition chooses data from
an unproved existence theorem. The objectwise choice in the main proof is local to
a proof of a proposition, and is not exported as a definition.

Source read: Bhatt--Scholze, Lemma 4.2.12 (continuous labels), Lemmas 5.1.2 and
5.1.4, and Corollary 5.1.5 (pp. 34--35, continuity and descent). The finite-set
frame argument is the agent-formulated refinement already in the original DAG;
Corollary 5.1.5 itself concerns finite free modules. The existing Stacks morphism
descent and finite inverse-limit nodes are retained for the corresponding lemmas.

The complete five-module sandbox compiled successfully using `lcompile.py --all`.
The first successful run took 27.9, 14.7, 12.8, 14.1 and 14.5 seconds per module.
The later run checks that the package structure stays in its original module.
The code uses the three named intermediate declarations, whose proofs remain open;
this is a compiling decomposition, not a claim of a sorry-free descent theorem.

## Proved and sorry left

Original holes closed: one, in
`AlgebraicGeometry.ProEtale.nonempty_connectedAbelianTowerNormalizedDescent`
(node `lem-sfb-connected-abelian-tower-normalized-descent`). Its assembly is complete.
There are no remaining holes in the assigned module.

Three holes are added, each the complete proof of one public theorem in its own module:

- `AlgebraicGeometry.ProEtale.nonempty_abelianTowerDescentObject`, node
  `lem-sfb-connected-abelian-tower-descent-object`;
- `AlgebraicGeometry.ProEtale.abelianTowerDescentHom`, node
  `lem-sfb-connected-abelian-tower-descent-hom`;
- `AlgebraicGeometry.ProEtale.abelianTowerFiniteFrame`, node
  `lem-sfb-connected-abelian-tower-finite-frame`.

Thus the original hole is decomposed into three separately stated mathematical
results; the net hole change of this packet is +2, not net proof progress.
The private lemmas `connected_copies_map_constant`, `comparison_constantLabel`,
`constantLabel_injective`, `constantLabel_surjective`,
`constantLabel_germ_injective`, and `constant_maps_fibre_ext` are fully proved.
The public projection and fibre-label cancellation lemmas are also fully proved.
The data module has zero holes and no definitions with proof holes.

## No longer needed

No mathematical dependency of the original argument is claimed globally pruned.
The original first seven steps are retained in objectwise descent, steps 8--9
in morphism descent, and steps 10--11 in finite-frame descent. The direct
constant-map proof uses the existing finite-representability and clopen-coproduct
nodes. The original unit route is preserved.

The following direct proof imports leave the assigned module:

- `Mathlib.CategoryTheory.CofilteredSystem`;
- `Mathlib.CategoryTheory.Yoneda`;
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`;
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`;
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`;
- `Sheaf.CategoryTheory.SetSheafCoverDescent`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`;
- `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity`.

Their mathematical uses remain in the appropriate intermediate nodes where needed;
those nodes' proofs, rather than the functor assembly, are the next proof items.
The five original public imports are in the shared data module and publicly
re-exported; they are not pruned. Finite-constant representability and the
clopen-coproduct import stay as direct proof imports. The direct filtered-Type
colimit import supports the proved germ argument.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or target change was found. The original signatures of the
listed proof dependencies were read. They supply restriction, representability,
stalk comparison, morphism descent and continuity; none directly states the
objectwise normalized torsor calculation, its equivariant Hom calculation, or
finite-frame descent. These are genuine separate results of the original eleven
steps. Merely applying one of the listed dependencies cannot construct the package.

The generic Mathlib Galois-category equivalence found by semantic search requires
a fibre functor and Galois-category structure, so applying it here would assume
part of the desired construction. It also does not identify the entire specified
overlap arrow. It is not a shorter replacement for the normalized calculation.

Edge cases checked for the new statements: empty labels have their unique action
and empty stalk; both-empty labels have one morphism; a nonempty source has no map
to empty target labels. The connected schemes are nonempty by ConnectedSpace;
pointed refinements are nonempty because they carry the specified geometric point.
A one-level trivial-group tower reduces to the usual finite-constant calculation.
Finite-frame descent has no geometric-point or preexisting finite-level-triviality
hypothesis on its reverse implication. Abelian groups retain the stated left-action
convention, with no hidden inversion. Surjectivity of finite projections is used
only where the Hom argument requires finite-label equivariance from G-equivariance.

## New nodes

`lem-sfb-connected-abelian-tower-descent-object` is the calculation for one sheaf,
not a fibre functor and not a Hom theorem. It retains the original steps 1--7,
including normalization, compatibility at every trivializing level, and equality
on the entire labelled overlap.

`lem-sfb-connected-abelian-tower-descent-hom` takes two supplied objectwise
splittings. It states the label formula for a sheaf morphism and unique descent
of an equivariant map. Its proof is original steps 8--9 and does not construct
the objectwise splittings or prove finite-stage completeness.

`lem-sfb-connected-abelian-tower-finite-frame` concerns arbitrary sheaves and
finite constancy at the limit versus a level. It has no point or action and is
independent of objectwise monodromy and Hom descent. Its proof is original steps
10--11 plus restriction for the forward implication.

All three have source/proof docstrings, complete natural-language proof steps,
Lean attachments and logged Mathlib searches. Blueprint searches for finite
frames and normalized finite descent found no matching blueprint node; the
broad equivariant-morphism match concerns spreading inputs and is unrelated.
The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py;
the inherited detailed route and via chain are preserved. The shared-data module
is attached to the existing definition node, whose statement remains unchanged.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
