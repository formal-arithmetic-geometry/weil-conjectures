## What changed

Replaced the sole sorry in
AlgebraicGeometry.Scheme.geometric_triples_colimit_comparison with a compiling
composition proof. The exact original theorem signature is preserved verbatim.
The field identification is proved using separability in towers and triviality of
separable extensions of a separably closed field. Algebraic closure existence uses
AlgebraicClosure. The proof constructs i by composing the algebraic equivalence e
with the geometric comparison g, proves every base-map and evaluation equation,
and proves uniqueness using colimit.hom_ext, injectivity of K -> Omega, and
uniqueness of inverse maps. This is a decomposition, not a complete proof from
sorry-free dependencies.

The eight original canonical maps and predicates have been moved verbatim to
Sheaf.AlgebraicGeometry.GeometricTriplesComparisonMaps, publicly reexported by the
original module. Their names, universes, signatures and bodies are unchanged;
only their docstring node tags change. This lets both lower lemmas refer to them
without an import cycle. The item retains its original six public imports.
The interface move is recorded in
coord/changes/geometric-triples-comparison-maps.md. No other existing module is
changed. There are no existing direct Lean importers of the assigned module.
The original DAG parents remain needed, including parents whose proofs have
not yet imported this module. No withdrawal is proposed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.geometric_triples_colimit_comparison
(node lem-wf-geometric-triples-colimit-comparison): 1 of 1 original holes closed.
Its proof has no remaining sorry. The field and algebraic-closure conjuncts are
proved directly, and the combination and uniqueness arguments are complete Lean.

Added two holes, each the entire proof of one public theorem in its own module:

- AlgebraicGeometry.Scheme.geometric_triples_diagram_comparison,
  node lem-wf-geometric-triples-diagram-comparison, in
  Sheaf.AlgebraicGeometry.GeometricTriplesDiagramComparison: the source's affine
  neighbourhood/triple equivalence and colimit specialization, independent of C.
- AlgebraicGeometry.Scheme.geometric_triples_algebra_recognition,
  node lem-wf-geometric-triples-algebra-recognition, in
  Sheaf.AlgebraicGeometry.GeometricTriplesAlgebraRecognition: recognition of the
  algebraic triple colimit, independent of Omega and geometric neighbourhoods.

Thus this delivery closes 1 original hole and adds 2 lower holes. It is a
substantive decomposition, with net minus one holes closed; no claim of net
sorry reduction is made. GeometricTriplesComparisonMaps has zero holes and every
definition has real data. The two new statements have source citations and
complete proof plans in both their docstrings and nodes.

## No longer needed

Removed the assigned module's three direct private proof imports:
WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples,
WeilConjectures.RingTheory.StrictHenselizationTriples, and
WeilConjectures.RingTheory.MapIntoHenselianColimit. The actual composition imports
GeometricTriplesDiagramComparison and GeometricTriplesAlgebraRecognition instead.

None of the mathematical dependencies behind those imports is globally pruned:
lem-weil-pbc-etale-local-ring-triples and
lem-weil-pbc-colimit-initial-full-subcategory remain in the diagram lemma's plan;
lem-weil-pbc-strict-henselization-triples and
lem-weil-pbc-map-into-henselian-colimit remain in the recognition lemma's plan.
The original structural and residue-field definition dependencies remain needed.
No module or node is withdrawn, and no unit step is bypassed. There are no other
imports or declared dependencies that this route makes unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The node's steps are not directly applicable
as written Lean: etale_local_ring_triples uses the relative separable closure
of a scheme residue field and a full affine chart category, while this item uses
the specified K and ring-written representatives. The diagram lemma isolates
that transport. Algebraic recognition also needs transport from the scheme
residue field to the base local residue field, arbitrary colimit cocones, and
ULift transport for C in an independent universe. Existing mapping theorems
have concrete filtered presentation hypotheses rather than the item's
IndEtaleAcrossUniverses predicate. The recognition lemma isolates that glue.

Edge cases checked mathematically: A a field, k imperfect and separably closed,
Omega transcendental over K, arbitrary small representative equivalences, and
unequal universes for C. Neither lower statement adds a perfectness or an
algebraicity assumption on Omega. The geometry lemma makes no claim about C;
the algebraic lemma has no geometric diagram or comparison g, so neither is a
renaming or hypothesis-repackaging of the original theorem. The unit record has
empty realized lists; its boundary-stalk route is preserved through the same
triple and henselian mapping tools.

## New nodes

- def-wf-geometric-triples-comparison-maps attaches the original eight real
  constructions to their new shared module. It introduces no new mathematical
  notion or unproved data.
- lem-wf-geometric-triples-diagram-comparison is steps 2 and 6 of the original
  plan, with residue containment from etale separability and the proved field
  identification supplied as an input.
- lem-wf-geometric-triples-algebra-recognition is steps 3 and 4, with the
  uniqueness of inverse ring maps used in step 5.

The original proof, proof_deps and proof_origin now describe the actual Lean
argument. The lower nodes retain all source dependencies needed by their plans.
Change record: coord/changes/geometric-triples-comparison-maps.md.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
