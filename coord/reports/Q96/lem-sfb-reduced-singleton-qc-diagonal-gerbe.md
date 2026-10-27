# Worker report: lem-sfb-reduced-singleton-qc-diagonal-gerbe

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reduced-singleton-qc-diagonal-gerbe.json`: statement, split into four steps; original statement and provenance retained. No new nodes and no Mathlib leaves.
- `citations.json`: all nine step/node pairs with verbatim statement quotations.
- `report.md`: this report. Earlier `searches.jsonl` and the sandbox construction script are retained as history; the script describes the superseded proposal and is not rerun.

## Attachments

None. Searches of live `lean/WeilConjectures/` for the blueprint tag, gerbe, AlgebraicStack, inertiaStack and inertia_stack found no declaration stating the item. Scheme singleton results do not prove the stack theorem.

## WANTED

None. All geometric inputs are in the local Stacks sources. No SGA source is used.

## Corrections and route

No statement dispute or statement change is needed. The assertion requires neither local Noetherianity nor finite type over the ground field. The inherited live item has an empty proof; the interrupted sandbox already had the four-step argument, two proposed nodes, search log and report. I read and retained its mathematical argument and searches. The first resumed dry run passed at 2c77bd16b3f. The subsequent final-delivery duplicate check found two newly landed Q132 nodes which state the proposed inputs exactly. I read those statements, removed both proposed sandbox nodes, replaced their citations with the existing nodes, and regenerated the verbatim quotations. The final delivery therefore adds no nodes.

The route is Stacks 06RC, then 0DQL, then the reduced-singleton field argument. Tag 06QK would add local Noetherianity and is not substituted. Singleton topology alone does not make an algebraic space a field spectrum: reducedness and the quasi-compact field-monomorphism input are both used.

I read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), the chapter and unit records, and the three-level rules. This is a supporting gerbe prerequisite within the inherited alteration/moduli chain, not a replacement of the unit's route. `blueprint_refs.py ancestor` reports a null imported ancestor for the inherited created.item chain; the explicit place/via chain is preserved rather than inventing an ancestor. The whole-blueprint search for gerbe returned no imported match. This is not the unit's key theorem, so no unit realization record is changed.

## Not duplicates

lem-sfb-qc-inertia-dense-open-gerbe vs lem-sfb-reduced-qc-inertia-dense-open-gerbe: equivalent assertions of 06RC; the proposed former node was removed, and step 2 cites the latter existing node.

lem-sfb-gerbe-base-qc-diagonal vs lem-sfb-gerbe-qc-diagonal-descent: equivalent relative-over-S assertions of 0DQL; the proposed former node was removed, and step 3 cites the latter existing node.

No new node remains to duplicate an elementary calculation, another DAG node, a clause of the item, or a Mathlib result. The removed proposals and their genuine search history remain described here for audit, not delivered as nodes.

## Mathlib searches

I read the actual results of the preserved `searches.jsonl`; no search was invented or repeated to reconstruct a log. The item retains its inherited searches and the logged LeanSearch query `Reduced algebraic stack quasi compact diagonal singleton point space is a gerbe over a field`. Hits concern scheme separation and reduced schemes, not stacks or gerbes. The old Loogle namespace rejection is explicitly described as rejected, with a successful typed query also present. The removed proposed inputs were searched with successful Loogle `AlgebraicGeometry.QuasiCompact`, grep `gerbe|AlgebraicStack|inertiaStack|inertia_stack`, and separate semantic phrasings; the hits concern schemes, not algebraic gerbes. All input lemmas are now existing DAG nodes, so no new-node search claim is made.

## Review by Q96

I read `stacks-morphisms.tex` Tag 06RC, proposition-open-stratum; Tag 0DQL, lemma-gerbe-diagonal-quasi-compact; `spaces-descent.tex` Tag 0GB3, lemma-reduced-local-smooth; and `decent-spaces.tex` Tag 047Z, lemma-when-field, and Tag 0H1T, lemma-factor-through-residual-space-decent. I opened the statement of every node in every proof step and checked all nine quotations literally. There are no new nodes requiring source review after duplicate removal.

Step 1 uses def-sfb-moduli-inertia for the object-and-arrow description, and def-sfb-stack-qcqs-morphism for quasi-compactness tested against every quasi-compact stack. The pullback of two diagonals consists of two objects with two isomorphisms, which reduce to one object with their ratio as automorphism. The inertia projection is therefore a base change of the given diagonal. A test of that base change is the same fibre product as the corresponding test of the old morphism. This proves the needed stability directly from the cited definition; no general unquoted base-change theorem is hidden.

Step 2 uses lem-sfb-reduced-qc-inertia-dense-open-gerbe. Its statement has exactly the reducedness and quasi-compact inertia hypotheses now available, and concludes an open dense gerbe over an algebraic space over the same base. The item has a nonempty singleton point space, so this open has every point. The final fibre-product clause of lem-sfb-smooth-presentation-closed-subsets says images commute with scheme tests. Thus the open subscheme in each test has all points and is the whole scheme. The open immersion is an equivalence. This is not an unsupported assertion that any morphism factors through an image.

Step 3 uses the smoothness, surjectivity and universal point-homeomorphism clauses of lem-sfb-gerbe-smooth-universal-homeomorphism. They make Q a nonempty singleton and make the composite of the given reduced smooth atlas with the gerbe map smooth and surjective. The exact descent direction needed is in lem-sfb-space-smooth-reduced-locality: reduced source plus smooth surjective morphism implies reduced target. The newly existing lem-sfb-gerbe-qc-diagonal-descent is the full relative-over-S version of 0DQL, with the same gerbe definition; it applies over Spec k to the item's given diagonal. Its source proof uses a surjective diagonal arrow, a cartesian square and fppf descent, all relative to that same base. No finiteness or separatedness hypothesis is added.

Step 4 uses lem-sfb-qs-space-field-monomorphism with Q's quasi-compact diagonal, obtaining a quasi-compact monomorphism j from a field spectrum representing its only point. Then lem-sfb-reduced-singleton-field-factorization applies with X=Y=Q and f=id: reducedness and singleton point image were just established. It supplies g with jg=id. Monicity gives gj=id by cancelling j from j(gj)=j. These are inverse maps over k, hence identify Q with Spec L over k. Its structure map is a unital field map k to L, necessarily injective. The fibre groupoids are identified under these inverse base maps, so the two fppf gerbe conditions are preserved. This explicitly proves the field conclusion rather than citing a clause renamed as a new node.

I tested edge cases: Spec L for arbitrary, including transcendental or infinitely generated, extensions L/k satisfies the conclusion; no finite extension hypothesis occurs. Spec(k[epsilon]/epsilon^2) is singleton but not reduced and cannot pass step 4. The empty stack has no singleton point space and is excluded in step 2. The general 06RC input allows empty stacks and many points, so it neither assumes nor supplies the singleton-field conclusion. The identity gerbe preserves the diagonal, while classifying gerbes show that no triviality of stabilizers is being inferred.

Against delivery-errors B--E, I checked self-contained statements, the actual source labels and hypotheses, source availability, recorded searches, and blueprint provenance; the two duplicate nodes have now been removed. Each non-elementary fact used is stated by a cited node, not merely mentioned in its source or proof. All proof steps are under 2000 characters and contain no hidden comparison lemma. The proof has no circular invocation and does not transfer the conclusion into a new node. The only correction required on this resumption was reusing the concurrently landed equivalent inputs. The final dry run and push are run after that correction.

## Unfinished work

None in the item's stage-1 assembly. Existing supporting nodes remain independently scheduled. No Lean file was written and no compiler or build tool was run.
