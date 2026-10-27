# Stage-1 delivery: lem-sfb-space-perfect-localizing-generation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-localizing-generation.json: split statement, original statement unchanged; four assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-weak-generator.json: new statement-only node; no Mathlib match; Stacks 09IY zero-detection theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-objects-compact.json: new statement-only node; no Mathlib match; perfect-to-compact direction of Stacks 09M8, in D_QCoh.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-extension-closed.json: new statement-only node; no Mathlib match; extension case of Stacks 03M1(4).
- citations.json: verbatim statement quotations for every citation in each item step.
- searches.jsonl and search_results.json: actual msearch log and full outputs, including two semantic phrasings for each new statement. The item's inherited Mathlib search records were retained and read; they already cover perfect localizing generation and give only derived-category/t-structure infrastructure.

## Attachments

None. Searched WeilConjectures for the item id, its blueprint docstring tag, perfect/compact generation, and the three new notions. Existing perfect-generator and perfect-compact declarations are for schemes, not arbitrary algebraic spaces. They cannot discharge this item. Existing sorry declarations were not treated as finished proofs. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Problems found and corrected

The item had no proof. Its reference to a perfect generator is only a zero-detection statement in 09IY: it is not by itself a proof of ambient localizing generation. The split supplies compactness, the existing general telescope theorem, and the actual closure induction. The ambient coproduct clause is proved using the ringed-site Grothendieck theorem, termwise derived sums and derived cohomology preservation. The scheme-only ambient-sum and perfect-generation nodes were deliberately not applied to spaces.

The inherited blueprint chain is broken: tools/blueprint_refs.py ancestor lem-sfb-space-perfect-localizing-generation prints None, although its long provenance names det-thm-sf-ctf-stability-direct-images. I retained from.node=null and its via list; each child prepends this item and names its precise supporting source. I read the current blueprint/latest unit and its direct-images proof (3), as well as the chapter/unit records. The auxiliary use is the inherited Stacks 0D3F first-paragraph reduction to perfect tests in the deformation/moduli branch of the direct-image route. No unit statement or route was changed and no realization fields were edited, since this is not the unit key node. Whole-blueprint searches (perfect generator, algebraic space perfect, perfect compact, 09IY, 09M8, 03M1, 07D9 and quasi-coherent extension) found no blueprint node stating the item or a new lemma. same_as is [].

While checking source locations I corrected the draft's derived-quasi-coherent definition tag to 071X; 08F3 is the direct-sums lemma. The delivered item statement needs no correction. There is no statement dispute.

## Not duplicates

lem-sfb-space-perfect-weak-generator vs lem-sfb-space-perfect-localizing-generation: the new statement is existence of one perfect zero-detector, not closure under ambient sums or localizing generation; compactness and the telescope are separate inputs and the item proves the closure argument.
lem-sfb-space-perfect-weak-generator vs lem-sfb-space-affine-pullback-perfect-detection: the latter detects isomorphisms after an affine pullback using every perfect test; it does not construct a single perfect weak generator.
lem-sfb-space-perfect-weak-generator vs lem-pc-perfect-generator-exists: the latter is only for schemes, while the new node concerns arbitrary qcqs algebraic spaces on their small etale sites.
lem-sfb-space-perfect-objects-compact vs lem-pc-perfect-object-compact: the existing theorem is for schemes, not algebraic spaces.
lem-sfb-space-perfect-objects-compact vs lem-sc-derived-qcoh-compact-is-perfect: that theorem is the reverse implication for Noetherian schemes, not the perfect-to-compact space implication used here.
lem-sfb-space-qcoh-extension-closed vs lem-sfb-space-qcoh-kernels-colimits: that node states kernel, cokernel, image and colimit closure, but does not state closure of an unknown middle term in a short exact sequence.
lem-sfb-space-qcoh-extension-closed vs lem-trf-scheme-etale-quasi-coherent-kernel: that node is kernel closure for schemes, not extension closure for spaces.
lem-sfb-space-qcoh-extension-closed vs lem-sfb-space-affine-etale-polynomial-generators: that node constructs a particular polynomial algebra surjection and its quasi-coherent kernel, not arbitrary module extensions.
lem-sfb-space-qcoh-extension-closed vs lem-sfb-space-infinitesimal-lift-pseudotorsor: that node concerns the sheaf of infinitesimal lifts and a particular quasi-coherent Hom module; it states no general extension-closure result.

## Review by NY

I read the item source in spaces-perfect.tex: lemma-quasi-coherence-direct-sums (08F3), theorem-bondal-van-den-Bergh (09IY), proposition-compact-is-perfect (09M8), the second proof of the better-coherator proposition, and lemma-pullback-and-limits (0D3F), first paragraph. I read the complete statement and proof of derived.tex lemma-write-as-colimit (09SN), including its telescope presentation. These justify using a compact weak generator within D_QCoh rather than claiming that a perfect object is compact in the ambient D(O_X).

For the new weak-generator node I read 09IY's precise equivalence and retained qcqs and a scheme base S; it asserts detection, not the item conclusion. For the new compactness node I read 09M8's first proof paragraph and the preceding section's interpretation of site-perfect complexes; its quasi-coherence assertion records that these are objects of D_QCoh, and its compactness formula is explicitly internal to that category. For the new extension node I read spaces-properties.tex lemma-properties-quasi-coherent (03M1), especially (4) and its etale-local proof. The new node uses only the extension direction, with no Noetherian assumption. All three new files have no proof, no proof_deps, and no hidden proof sketch.

I opened each cited DAG statement. Step 1 uses the small-skeleton convention, lem-pur-ringed-site-grothendieck-abelian for arbitrary small ringed sites, lem-sfb-grothendieck-k-injective for resolutions, lem-kun-grothendieck-derived-coproducts for termwise coproducts, src-weil-derived-homology-preserves-coproducts for the cohomology comparison with exact coproducts, and lem-sfb-space-qcoh-kernels-colimits for quasi-coherent sums. Every one says the input taken from it. I read injectives.tex 07D9 and sites-cohomology.tex section-unbounded, first paragraph, for this use. The short AB5-to-exact-coproduct argument is written out: finite subsums are exact, their filtered colimit is exact, and their universal property is the coproduct one. This is a routine finite-subsum calculation, not a new node. The hypotheses of the homology-preservation theorem, including K-injective resolutions and exact sums, are established before it is applied. This also shows agreement of ambient and internal coproducts, which an existence-only node would not establish.

Step 2 uses lem-sf-derived-homology-long-exact for the exact sequence of a distinguished triangle, then the existing space kernel/cokernel theorem and the new extension theorem for the explicit kernel/cokernel short exact sequence. Shift and isomorphism invariance follow from cohomology, and a retract's cohomology is the image of its split idempotent, covered by the same existing image-closure clause. The compactness node explicitly places all perfect objects in D_QCoh. I did not use the proof of a cited node as an extra statement.

Step 3 uses the new zero-detector, its compactness from the separate compactness node, and lem-pc-compact-generators-build-objects. I checked that this existing 09SN node states both the transition triangles and the final telescope triangle, not merely existence of a generator. Step 2 gives its triangulated hypothesis, step 1 gives its coproduct hypothesis, and the singleton family is small. The sign change on integer shifts gives the weak-generation convention. The size convention places Hom sets and coproduct indexing in the larger chosen universe. No assumption of ambient compactness is made.

Step 4 has no external lemma: for an arbitrary competing closure L, all attaching sums are in L, induction on n puts every X_n in L, and the cone of 1-shift on their sum puts E in L. This is the assembly, so it is marked elementary. Reverse containment is obtained because steps 1-2 showed that D_QCoh itself has all the required closure properties. This is not an application of a new node restating one of the item's clauses. The weak-generator node is a different and strictly smaller input, and there are three non-elementary assembly steps.

I checked X empty (zero category, zero generator, all detection and compactness conditions hold), empty coproducts (zero is quasi-coherent), singleton sums, arbitrary unbounded complexes (07D9 and the cohomology node have no boundedness assumptions), and arbitrary non-Noetherian qcqs spaces (09IY/09M8 require only qcqs). For extensions, zero outer terms force zero and a split extension gives a finite direct sum; both are consistent. Extension closure was not claimed for arbitrary ringed sites, only small etale structure sheaves of algebraic spaces. No new statement assumes properness, flatness, affineness or Noetherianity. The item statement is unchanged. All steps are below 2000 characters, and the written routine closure calculations hide no separate comparison lemma.

The generic off-unit inputs are declared in split_report.tool_uses with their purpose; they implement the existing Stacks route and do not replace a unit step. New-node searches were executed through the required msearch.py command and their exact queries and full outputs are retained. The plausible Mathlib hits were read: Quasicoherent.lean defines the predicate/local presentation data, LocallyFree.lean gives locally free implies quasi-coherent, and derived-category Basic/TStructure provide localizations and truncation infrastructure; none supplies the three new theorems. No Mathlib leaf was asserted. Citations use full verbatim statements so no abbreviated quote conceals a hypothesis mismatch. The preliminary server review_split passed; final deliver.py dry-run and push are the remaining mechanical steps.

## Unfinished work

The three new supporting statements intentionally remain unsplit for future items. Nothing in this item's authorized stage-1 assembly remains unfinished.
