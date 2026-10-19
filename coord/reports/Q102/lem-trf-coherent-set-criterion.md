# Stage 1 report: lem-trf-coherent-set-criterion

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-coherent-set-criterion.json`: repaired item, with the forward step expanded.
- `dag/nodes/sec-trace-formula/lem-trf-finite-locally-constant-coherent.json`: repaired statement node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-stratified-product-coherent-conservative.json`: dependency list trimmed to notions used by its statement; Mathlib searches found no match.
- `citations.json`: verbatim quotes for every node used by every item step.

Attachments: none. I searched both source checkouts under `WeilConjectures/` by the item id, coherence and constructibility terms, and the candidate declarations; no sorry-free project declaration states the item exactly.

WANTED: Orgogozo, “Modifications et cycles proches sur une base générale”, author draft §8.1 (printed pp. 17–18), for the coherence criterion and the converse coproduct argument. The document is referenced by URL in the item; no local copy is available.

What was wrong and what changed:

- E2: the old helper node falsely asserted that an arbitrary internal equivalence relation on a finite locally constant sheaf has a finite locally constant quotient. I replaced it with the intrinsic slice-topos definition of finite local constancy, removed the scheme-étale local-constancy dependencies, and state the correct hypotheses: images of maps between finite locally constant sheaves are finite locally constant, and a quotient is finite locally constant when both the sheaf and the internal equivalence relation are finite locally constant.
- E3/C1/E5: the forward item step now explicitly stratifies every generator component and every finite-limit overlap triple by the common source/base partitions. It checks the qcqs hypotheses for each stratum base change, cites the fibre-product formula from `lem-trf-oriented-product-universal`, and cites `lem-galois-flc-representable` for finite étale representables. The finite-limit, image, and quotient clauses of the corrected helper then apply to the finite coproduct, overlap relation, and quotient giving $A$.
- E3: `lem-trf-stratified-product-coherent-conservative` had padded statement dependencies; its list now contains only the notions appearing in its statement.

What I could not finish: no local copy of Orgogozo §8.1 was available, so the proof remains agent-written from the cited finite-cover site criterion and the blueprint route. No Lean was written or compiled.

## Not duplicates

- `lem-trf-finite-locally-constant-coherent` vs `lem-galois-flc-representable`: the existing node is the finite-locally-constant/finite-étale equivalence on one scheme étale site; this node is coherence and finite-operation closure for arbitrary finite-cover topoi.
- `lem-trf-finite-locally-constant-coherent` vs `lem-constructible-constant-exact`: the existing node is exactness of constant module sheaves; this node is set-valued local constancy, images and quotients in a finite-cover topos.
- `lem-trf-stratified-product-coherent-conservative` vs `lem-trf-coherent-conservative-reflection`: the existing node reflects coherence along an already coherent conservative morphism; this node constructs the finite stratified coproduct morphism.
- `lem-trf-stratified-product-coherent-conservative` vs `lem-trf-oriented-product-points-conservative`: the existing node concerns geometric points; this node concerns the family of stratum-product inverse images.

## Review by Q102

I reread the item, the returned E2/E3 diagnostics, the unit and chapter records, and every cited node. Step 1 uses the scheme-convention, finite-type-over-Noetherian, locally-Noetherian-qc-separated, qcqs triple-presentation, and finitary-site coherent-generator statements exactly as quoted; their hypotheses are the item’s Noetherian finite-presentation assumptions. Step 2 uses the coherent-generator statement to obtain a finite representable presentation and finite-limit overlap data. I checked that every component is separated étale of finite presentation and hence qcqs before applying the Stacks 03S0 stratification node. I checked that the same source and base partitions stratify the overlap fibre products. For each stratum immersion I checked the qcqs hypotheses in the base-change clause of `lem-trf-qcqs-oriented-triple-presentation`; its explicit oriented-product fibre-product formula is quoted in `citations.json`. The finite étale pieces are converted to finite locally constant representables using the complete statement of `lem-galois-flc-representable`. The corrected helper is then used only for finite limits, images, and quotients whose equivalence relation is itself finite locally constant. Step 3 uses the exact coherent-generator, stratified-product coherent/conservative, corrected finite-locally-constant, and coherent-conservative-reflection statements.

For the helper repair I tested a point topos, the empty topos, finite constant sets, finite products and coproducts, and maps of finite sets. I also tested the returned strictly henselian DVR counterexample: its quotient relation is not finite locally constant, so it is excluded by the corrected quotient clause. The item’s point, empty-scheme, zero-sheaf, and infinite-constant-sheaf edge cases remain as before. I removed the old arbitrary-topos scheme-etale citations and the padded dependency ids. No SGA 4 or SGA 4½ source is used.
- `lem-trf-finite-locally-constant-coherent` vs `lem-galois-flc-set-is-finite-sheaf`: the existing node only records finite stalks/local finiteness on one scheme étale site; this node asserts coherence and finite operations in an arbitrary finite-cover topos.
- `lem-trf-finite-locally-constant-coherent` vs `lem-galois-flc-set-stalk-finite`: the existing node proves stalk finiteness; this node proves topos coherence, finite limits, images, and quotient closure under an FLC relation.
- `lem-trf-finite-locally-constant-coherent` vs `def-weil-pbc-constructible-abelian-sheaf`: the existing definition concerns abelian sheaves on schemes; this node concerns set sheaves on finite-cover sites and includes operations and coherence.
- `lem-trf-finite-locally-constant-coherent` vs `def-weil-pbc-etale-constructible-sheaf`: the existing definition is a scheme étale module constructibility predicate; this node is a theorem for set sheaves on arbitrary finite-cover topoi.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-abelian-bounded-exponent`: the existing result is bounded-exponent abelian constructibility on schemes; this node is set-valued and site-general.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-abelian-zn-module-constructible`: the existing result concerns Z/n-module constructibility on schemes; this node concerns finite set sheaves and topos coherence.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-etale-module-sheaf-comparison`: the existing result compares two module predicates on schemes; this node gives set-valued image and quotient closure on finite-cover topoi.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-field-finite-separable-constant`: the existing result is a field-point module trivialization statement; this node is a general finite-cover topos theorem.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-module-finite-stalks`: the existing result only treats finite stalks of scheme module sheaves; this node treats coherent set objects and FLC operations.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-module-underlying-sets`: the existing result forgets a constructible module on a scheme; this node proves coherence and closure for arbitrary set sheaves on finite-cover sites.
- `lem-trf-finite-locally-constant-coherent` vs `lem-weil-pbc-constructible-torsion-modules-agree`: the existing result compares torsion-module notions on curves; this node is a site-level set-sheaf theorem.
