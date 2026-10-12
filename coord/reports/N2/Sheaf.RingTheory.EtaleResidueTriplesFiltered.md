## What changed

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_filtered_part` in
`Sheaf.RingTheory.EtaleResidueTriplesFiltered`, preserving its statement and docstring.
Added the proof-only import `Mathlib.AlgebraicGeometry.Pullbacks`.

The proof follows the three constructions of the existing DAG plan. Ring pushouts
implement its tensor products. For two objects the pushout has the compatible map to K.
For parallel maps, E is their pushout, P is the pushout of the two structural maps
R → T, and U is the pushout of P → E along multiplication P → T. The two maps T → E
become the same map T → U; the pushout relation then equalizes the parallel maps.
Étale base change, composition and cancellation are applied through Mathlib's
`isPullback_SpecMap_pushout`, `MorphismProperty.of_isPullback`, the composition instance,
and `AlgebraicGeometry.Etale.of_comp`.

Private proved helpers construct pointings using `Scheme.SpecToEquivOfField`, verify
that their primes lie over p, and build morphisms in the induced category. The two
private noncomputable definitions contain complete constructions and no postponed proof.
No existing public definition, statement, public import, or DAG dependency changed.
The existing plan and its two Mathlib dependencies still describe the proof, so no node
copy is needed.

Searches: LeanFinder for filteredness of étale algebras with a compatible map to a field
returned étale algebra composition and base-change results, not this category theorem.
Loogle `CategoryTheory.IsFiltered` returned the filteredness constructors and finite
colimit criterion. The search wrapper grep found no direct match; local rg found only
the downstream colimit/strict-henselization uses. Mathlib source searches located the
Spec pushout-to-pullback lemma and étale cancellation. The source read was
[Stacks Tag 04GW](https://stacks.math.columbia.edu/tag/04GW), the three filteredness
paragraphs; the local literature source file was absent on this machine.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_filtered_part`
(node `lem-weil-pbc-etale-triples-filtered-colimit-filtered`): 1 of 1 original sorries.
There are no sorries left or split off. All private helpers are proved.
The module compiles locally without warnings using the required `lcompile.py` wrapper.
The delivery dry run checks the declaration axioms and compiles on the server.

The proof uses only a field K and its given residue-field map: no separable closure,
algebraicity, or chosen algebra instance is introduced. Nonemptiness is constructed
explicitly, including when K is the original residue field. Identical parallel maps
are covered by the same pushout construction; no distinctness assumption is used.
No changes to the blueprint unit route were made.

## No longer needed

None. Both original public imports are used. The new proof-only pullback import is
used to prove étaleness of pushout maps. The planned nodes
`lem-weil-pbc-etale-ring-base-change` and
`lem-weil-pbc-etale-composition-cancellation` remain needed, implemented by their
Mathlib matches. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The tensor-product plan admits a complete categorical
pushout implementation using existing Mathlib declarations. Recovering the prime and
residue embedding through `Scheme.SpecToEquivOfField` implements the planned kernel
factorization without separately manipulating localized rings.

## Second reading by N2

1. Interface preservation: PASS. Diffed the sole delivered module against the
   repository version. The existing theorem signature and docstring are byte for
   byte unchanged. Both existing public imports remain; the added Pullbacks import
   is proof-only. All additional declarations are private proof helpers. No existing
   definition changed, and no change record is required.
2. Proof and trust: PASS. Independently compiled the module with lcompile.py without
   errors or warnings. Scanned the complete source: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition. A scratch copy with #print axioms
   for AlgebraicGeometry.Scheme.etaleResidueTriples_filtered_part reports exactly
   propext, Classical.choice and Quot.sound. The delivery tool also probes every
   declaration, including private helpers.
3. Split statements and edge cases: PASS. There are no split-off statements or new
   public statements to review. Read the private constructions and the imported
   residue-triple definition. SpecToEquivOfField supplies the actual prime and
   residue embedding; evaluating the commuting Spec maps at the unique point of
   Spec K proves that prime lies over p. The identity triple handles K = κ(p),
   the object construction handles identical objects, and the parallel-map
   construction handles f = g without a distinctness assumption. A zero ring cannot
   supply p and a zero pushout cannot map to the field K, so neither gives an
   unhandled exceptional case.
4. Route and pruning: PASS. Reviewed the construction top down and searched again
   with LeanFinder for a category of etale neighborhoods with a field-valued point.
   It found the etale over-category and site declarations, no filteredness theorem.
   Local rg finds only downstream uses of this arbitrary-field theorem; the
   strict-henselization special case depends on it. Read Mathlib's
   SpecToEquivOfField, isPullback_SpecMap_pushout, and Etale.of_comp implementations.
   The proof directly realizes nonemptiness, tensor-product successors, and the
   diagonal base-change equalizer; no simpler reusable theorem was found.
   All three imports serve the statement or proof. Both old proof dependencies are
   used as Mathlib base-change/composition/cancellation facts, so the No longer
   needed list is complete (none). Read dag/units/sk-thm-p1.json realized: this
   subordinate argument preserves the unit's statement and all four step routes.
5. DAG agreement: PASS. Read the item's node and both proof-dependency nodes. Its
   three proof steps describe precisely the Lean construction, with categorical
   pushouts implementing the tensor products. proof_deps and proof_origin remain
   accurate. No node copy or new node is necessary.

Second-reading changes: appended this independent review and recorded the additional
search. No repair to the Lean proof, imports, statements, or DAG was needed.
