## What changed

Proved the remaining endpoint hole in
`Sheaf.AlgebraicGeometry.HigherDirectImageOverMapCoefficient`.
All existing signatures, visibility, definitions, documentation and imports are unchanged.
The factorization proof applies `Functor.map_comp` directly; the assembly uses `Eq.trans`.

The endpoint proof instantiates a proved private categorical identity using the homology
functor H, derived direct image R, triangle transition l, single-complex comparison s and
coefficient identification c. The identity follows from composition preservation and
associativity. A private congruence proof generator, adapted from the existing
`HigherDirectImageRawTransitionToHomCore` code, identifies its two sides with the concrete
maps by explicit proof irrelevance and heterogeneous congruence. Lean checks every generated
proof. This avoids forcing kernel conversion to normalize the large derived-category objects.
The complete delivered module compiled without warnings in 48.9 seconds through lcompile.py.

Updated the three existing nodes' proof routes to match the actual dependencies.
The preflight scanner treats private meta definitions as interface commands;
`coord/changes/B2-coefficient-structural-congruence.md` documents that conservative
classification and the absence of any public interface change.
No auxiliary source module, new public declaration or definition change is delivered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.higherDirectImageOverMap_coefficient_endpoint`
(node `sbc-lem-higher-image-over-map-coefficient-endpoint`).

Retained the already proved `higherDirectImageOverMap_coefficient_factorization` and
`higherDirectImageOverMap_coefficient`; the latter now rests on the completed endpoint proof.
The new private `mapped_coefficient_comp` is fully proved from `Functor.map_comp` and
`Category.assoc`. There are no remaining or added source sorries, and no split-off statements.
The argument works for every integer degree, identity arrows and zero coefficient sheaves,
without finiteness, positivity or nonemptiness assumptions, and makes no data choices.

## No longer needed

No existing import or module is pruned: the sole public import supplies the unchanged statements.
The earlier proposed `HigherDirectImageOverMapCoefficientEndpointCoherence` module and its
endpoint-unfolded and endpoint-expansion nodes remain outside the delivery under scratchpad.
No imports of the transition-composition or transition-to-hom modules are necessary: only their
private proof-generation technique is adapted, and none of their mathematical results is used.

Removed the erroneous parent-theorem proof dependencies of the endpoint and factorization
nodes. The factorization has no DAG proof dependencies; it uses Mathlib functoriality.
The parent node now uses exactly its factorization and endpoint nodes, replacing the old direct
proof edges to `def-sbc-module-higher-image-transitions`,
`lem-weil-pbc-inverse-image-composition`, `def-sbc-higher-image-raw-over-complex`, and
`def-sbc-higher-image-raw-over-coefficient`. The transition, raw-complex and raw-coefficient
constructions remain necessary through the endpoint. No separate inverse-image composition
lemma is applied: its fixed comparison appears identically in the two definitions.
The blueprint unit statement, steps and realized entries are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier direct proof had the correct mathematical calculation, but relied on expensive
kernel conversion between elaborated instance/proof arguments in derived-category expressions.
Its 60-second timeout was a performance problem, not a broken compiler. Merely changing the
wrappers to abbreviations, caching instances, or rewriting the endpoint as HEq did not repair it.
Those experiments are excluded from the delivery. The existing library already contains a
kernel-checked solution to this problem: explicit structural congruence proofs before reduction.
Adapting that proof generator closes the endpoint within the unchanged limit, without modifying
another group's definitions, splitting the file, or bypassing the kernel.

The earlier split-off unfolded endpoint restated the whole outstanding argument; its expansion
helper duplicated a definitional equation. Neither is needed. The existing DAG proof routes for
factorization and endpoint incorrectly cited their parent theorem; those circular proof edges
are removed. The remaining proof is elementary functoriality of the existing canonical maps.

## Second reading by B2

1. PASS: Diffed the sole delivered module against the repository. Extracted and compared
   all three existing theorem signatures byte for byte, including their proof arguments.
   Signatures, visibility, documentation, definitions and the sole public import are unchanged.
   The private categorical helper and meta proof generators affect proofs only; the change
   record documents the scanner's conservative classification. No other source module is delivered.
2. PASS: Independently compiled the full module without errors or warnings (49.1 seconds).
   Read the generic categorical calculation and the complete proof generator against
   HigherDirectImageRawTransitionToHomCore: it builds HEq reflexivity, proof irrelevance,
   heterogeneous function extensionality and congruence terms, then transports the proved
   calculation. No kernel bypass, custom axiom, unsafe declaration or source sorry is present.
   The separate scratch copy compiled in 48.3 seconds and #print axioms shows exactly
   propext, Classical.choice and Quot.sound for each of the three public theorems.
3. PASS: No statement is split off and no new source hole is added. The fully proved private
   identity is valid for arbitrary categories and composable maps; identity maps and zero
   coefficients introduce no exception, and no degree restriction or object choice occurs.
4. PASS: The mathematical route is exactly functoriality and associativity of the existing
   canonical maps. Independent Loogle search for CategoryTheory.Functor.map_comp and rg
   searches for coefficient endpoint identities confirm the existing constituent and reveal
   no shorter upstream endpoint theorem. The shared-complex equality and coefficient HEq
   merely unfold the same data; the explicit congruence generator handles conversion costs.
   The only import supplies types and definitions in the public statements and must remain
   public. No longer needed lists all replaced old proof dependencies, distinguishing
   unused proof edges from definitions still used in the endpoint. The unit
   dag/units/sk-lem-failure-field.json is unchanged: its already-empty realized entries are
   a pre-existing incompleteness, and this below-unit calculation bypasses no realized step.
5. PASS: Read all three delivered nodes and compared their JSON with the originals.
   Factorization uses Mathlib functoriality, endpoint uses the three shared construction
   nodes, and assembly uses factorization and endpoint. Their proof routes now match Lean
   and are acyclic. No new node needs split-statement metadata.

Second-reading changes: restored the original Lean statement metadata in the two existing
auxiliary nodes, removing formatting-only churn; corrected the factorization provenance to
name only Functor.map_comp. No Lean proof repair was needed.
