## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-coherent-rhom-finite-injective-dimension.json`: item, statement unchanged, status split; six explicit proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-bounded-above-coherent-rhom.json`: new statement, unsplit; no Mathlib match for the assertion about complexes.
- `citations.json`: one verbatim statement excerpt for every step/node pair.
- `report.md`: this report. `searches.jsonl` is the unmodified output of the required search command.

Attachments: none. I searched the read-only slopmaster2 project under `WeilConjectures/` by the item's blueprint tag, by coherent Hom, and by finite injective dimension. No declaration states the item, nor the proposed new complex-level lemma. Upstream master is not used as evidence of a finished proof.

WANTED: none.

The item has no statement error. Its unbounded K is essential and remains unbounded. Its finite-injective-dimension hypothesis is exactly the bounded-injective-complex meaning of Stacks 0A5S, more-algebra.tex, `definition-injective-dimension`. Nothing in the argument requires a local ring, regularity, finite Krull dimension, or bounded cohomology for K. The original node was statement-only; the delivery supplies the proof rather than replacing the assertion.

The item's inherited Mathlib searches remain intact. New queries were actually run by `msearch.py`, their hits read, and their exact tool/query/result records appended. All services returned results in this run. Both the item and the new lemma were searched with two semantic phrasings; the new lemma also has LeanSearch, Loogle and source grep searches. Broad grep had irrelevant extension/extensionality hits, so I narrowed it to Algebra and CategoryTheory/Abelian. The Algebra search found `ModuleCat.finite_ext`; I read Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean, lines 27–35. It concerns modules in degree zero and natural-number Ext, not coherent complexes. Existing `lem-sc-ext-noetherian-finite` already represents it; I did not create another module Ext node or claim that the new lemma is a Mathlib leaf.

## New nodes

`lem-trf-bounded-above-coherent-rhom` is the algebra assertion explicitly stated in the proof of Stacks Tag 0D0C, perfect.tex, `lemma-coherent-internal-hom`, lines 2695–2711. Over a commutative Noetherian ring, K has finite cohomology and an upper cohomological bound u, L has finite cohomology and a lower bound v, and their derived Hom has finite cohomology and vanishes below v-u. The lower bound is also read directly from the displayed spectral sequences: p is at least -u and q at least v. No finite injective dimension is assumed in this new input.

The node contains only its self-contained statement: no proof steps, proof dependencies or hidden sketch. It cites the existing definitions of Noetherian ring, finite module, ordinary derived category, and derived internal Hom, explicitly specialized to the one-object ringed site. Its chapter and unit are inherited from the item. Its blueprint.from points to `lem-trf-local-term-locality`, with the item's whole via chain preceded by the item and an exact reference to the 0G4H proof sentence it serves.

This is not an item-clause restatement: the new input imposes a bound on the first variable and drops the finite-injective-dimension condition on the second. The delivery itself proves the passage from unbounded input to that bounded-above setting, including the cohomology comparison. The proof of this new general algebra input remains the next stage-1 item, as required for a one-level split. Its source proves it by bounded hyper-Ext spectral sequences and finite Ext of finite modules; those are future work, not additional unrecorded facts used in this item's proof.

## Not duplicates

lem-trf-bounded-above-coherent-rhom vs lem-sc-sheaf-ext-coherent: both mention Tag 0D0C, but the existing statement treats two coherent module sheaves concentrated in degree zero on a locally Noetherian scheme; it does not assert the bounded-above/bounded-below algebraic complex result.

lem-trf-bounded-above-coherent-rhom vs lem-sc-ext-support-cohomology-vanishing: both mention Tag 0D0C, but the existing statement is a support/cohomology vanishing result for a regular curve, not finite cohomology of derived Hom between algebraic complexes.

lem-trf-bounded-above-coherent-rhom vs lem-sc-ext-noetherian-finite: the existing Mathlib leaf is module Ext finiteness, not the assertion for complexes, and would need the source's convergent spectral-sequence argument to imply it.

lem-trf-bounded-above-coherent-rhom vs lem-per-bounded-above-rhom-hyperext: the existing node supplies a spectral sequence and lower bound on a ringed site, with no coherent-cohomology conclusion. Its statement alone is not the new finiteness theorem.

I searched all DAG node statements/titles for coherent Hom, bounded injectives, and finite cohomology; searched the exact tag and label; and ran blueprint_refs searches for `finite injective`, `coherent internal`, `bounded injective`, `0D0C`, `coherent Hom`, `bounded above`, and `finitely generated cohomology`. The blueprint hits about flat pullback and geometric finiteness do not state this algebraic lemma. Existing projective-Hom-model and finite-ring-derived-Hom nodes likewise assert computations or a finite-ring special case. No existing general coherent-complex Hom theorem was found. No off-unit non-Mathlib theorem is used by the item: the three existing theorem inputs are Mathlib leaves; the only new theorem is in this item's own unit.

## Review by Q80

I read Stacks dualizing.tex, Tag 0G4H, `lemma-finite-ext-into-bounded-injective`, including the entire proof. I also read more-algebra.tex, Tag 0A5S, `definition-injective-dimension`, and perfect.tex, Tag 0D0C, `lemma-coherent-internal-hom`, including its proof's algebra assertion and two spectral sequences. The item's statement agrees with 0G4H: both complexes have finite cohomology, K may be unbounded in both directions, and L has a bounded injective representative. For the new node, I checked that the source assumes only a Noetherian ring, an upper bound for K and a lower bound for L; finite injective dimension is not smuggled into its statement. The lower bound v-u is the correct shift sign.

For each proof step I opened every cited node and read its statement, not its proof. The corresponding exact excerpts are in citations.json.

1. The bounded-below-injectives node actually states that a termwise injective bounded-below complex is K-injective, for an arbitrary abelian category. The chosen bounded I satisfies this with lower bound a. The derived-internal-Hom definition explicitly permits any K-injective target representing L and any representative of the first variable. The module-total-Hom definition retains the A-module structure and gives the product and signed differential. This avoids confusing a sheaf-derived Hom, an abelian-group mapping complex, and the A-linear complex whose finite generation is wanted.

2. The truncation-cohomology node explicitly gives the kernel good truncation, the cohomology isomorphisms in degrees at most n, and vanishing above n. These are exactly what is used to know that T has finite cohomology and an upper bound. The quotient C is constructed here, not taken from the proof of another node: C is zero below n because T equals P there. I deliberately use the quotient supported from n, so the comparison does not depend on an unstated lower-truncation theorem or a sharper off-by-one bound.

3. The degree bound is written out from the module-total-Hom statement. In degree r>b-n, each factor vanishes by p<n or p+r>b. With n=b-i+1, both i and i+1 satisfy this strict inequality. This is a short calculation from the displayed product, not an uncited injective-dimension vanishing lemma.

4. The definition of injectivity explicitly says restriction along a monomorphism is surjective, so it applies to each T^p into P^p. Maps in the kernel factor uniquely through the quotient P^p/T^p. The finite product uses only p between a-r and b-r: taking lifts factor by factor proves its surjectivity and the kernel is the product of the kernels. Precomposition commutes with the differential by its explicit formula. Thus the whole degreewise short exact sequence is proved here in a few lines from the cited definitions, not hidden inside a new node or assumed as a general RHom exactness theorem. It is correctly marked elementary.

5. The short-exact-complex long-exact-sequence node is stated for any abelian category and integer-indexed cochains. The complexes here are complexes of A-modules and the required degreewise short exactness was established in Step 4. Its displayed four consecutive groups are exactly those needed. Step 3 kills both outer groups, so the middle map is an A-linear isomorphism. Step 1 identifies the two middle cohomologies with the intended derived Homs; there is no appeal to an unrecorded Hom-to-triangle identification.

6. The new node's statement gives finite cohomology under precisely the checked bounds u=n and v=a. Step 2 checks all hypotheses on QT, and the item's assumptions together with I check all hypotheses on L. The A-linear isomorphism from Step 5 transfers a finite list of generators. Since i was arbitrary, no global bound on K or on the output has been introduced.

For the small-case check, over a field take K=k[-u] and L=k[-v]: the output cohomology lies in degree v-u, confirming the new lower-bound sign and its possible equality. For A=Z and K=(Z/2)[0], L=Z[0], the degree-one Ext is allowed, so the statement does not incorrectly assert degree-zero concentration. For the item take a field, I=k[0], and K with k in every degree and zero differential. The output is still unbounded with one-dimensional cohomology in each degree, consistent with the conclusion. Here n=1-i, and the quotient Hom is zero in degrees i and i+1 exactly as claimed. K=0, L=0, the zero ring, and negative shifts require no extra hypotheses; for I=0 any a=b may be chosen.

I checked delivery-errors B–E against the actual files. There is one new statement-only node, all notions are defined inline or by the cited definition statements, TeX uses single backslashes after JSON decoding, source tags and labels were checked in the local tag table, and no fake Mathlib match or attachment is asserted. The same-tag distinctions are above. All non-elementary inputs are cited; no cited definition is used for a theorem it does not state. The explicit Hom-complex construction repairs the proof gap that a bare instruction to apply a truncation triangle would leave. No statement dispute or correction is needed. No proof step exceeds 2000 characters (maximum 769), and none conceals a separate comparison lemma. The dependency direction is from this item to existing leaves/definitions and the new strictly smaller input; the new node has no proof edges back to the item. Only sandbox files were written, and no Lean, compiler, Lake or local checking script was run.
