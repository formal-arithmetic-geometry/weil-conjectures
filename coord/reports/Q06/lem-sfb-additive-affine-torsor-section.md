# Stage-1 delivery: lem-sfb-additive-affine-torsor-section

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-additive-affine-torsor-section.json: statement, split; no Mathlib match. The original statement, statement dependencies, source, searches, creation metadata and blueprint lineage are retained. Four proof steps are added.
- citations.json: eleven entries, one for each step/node pair, containing verbatim statement text.
- report.md: this report.

No new nodes; zero new Mathlib leaves. The existing Amitsur exactness and descent nodes suffice.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by additive torsor, torsor/section and Amitsur terminology found no project declaration proving this item. The upstream generic Amitsur theorem is already attached to lem-pc-cech-exact; it proves only the algebraic input, not this scheme-torsor assertion. In particular, a type-level AddTorsor instance does not supply an A-point of a scheme torsor.

## WANTED

None. Milne and all supporting Stacks sources are present locally.

## Findings and changes

The item was statement-only, not mathematically disputed. Its hypotheses are adequate, including for nonreduced and non-Noetherian algebras. No statement or definition is changed. The split supplies the argument hidden behind Milne's classification/exactness sentence without introducing a new torsor-classification node: form the difference morphism directly from the given torsor isomorphism, kill its cocycle by Amitsur exactness, and descend the resulting matching morphism.

I read SETUP's three blueprint levels, GOAL.md, the chapter and unit records, the latest blueprint unit, and the latest direct-images proof (3). The inherited ancestry serves the split-solvable-torsor input far below that step. The existing blueprint.from.node is null: following created.item reaches the module item Sheaf.SixFunctors.CtfStabilityDirectImages rather than an imported DAG node. tools/blueprint_refs.py ancestor confirms None. I retained this inherited field and its detailed nonempty place/via trail; the split_report identifies the named blueprint proof and supporting clause. This does not change the unit route.

## Not duplicates

No new nodes were created. The existing lem-pc-cech-exact states the faithfully flat augmented Amitsur exactness needed here and is reused. The existing generic fpqc refinement and representable-descent nodes are also reused. Whole-blueprint searches for “additive torsor” and “torsors over” found no matching item; the search for “Amitsur” found the reused lem-pc-cech-exact. Whole-DAG searches by these concepts and fpqc/fppf descent were read before selecting the citations.

## Mathlib searches

I ran msearch.py for this item with leanfinder on “Every fppf torsor under the additive group over an affine scheme has a section” and “Faithfully flat descent additive cocycles vanish over affine schemes”; with loogle on the pattern `"torsor", "affine"`; with grep on `GaTorsor|additive.*torsor|torsor.*additive|amitsur.*exact|exact.*amitsur`; and with leansearch on “Every torsor under the additive group over an affine scheme is trivial” and the inherited query “Every additive group scheme torsor over an affine scheme is trivial”. All services answered in this run. I read every result: affine-space constructors and flatness criteria do not prove a scheme-torsor section, and abstract AddTorsor assumes nonemptiness of its underlying type, which cannot be assumed for P(A). No candidate gives the requested statement or a one-line specialization. Existing search records are retained, and this run's actual queries/results metadata are in searches.jsonl. No searches are claimed for new nodes, since there are none.

## Review by Q06

I read Milne, Algebraic Groups (2017), Example 2.72, printed page 61 (PDF page 73), together with the preceding torsor definition 2.66 and Example 2.67 on printed page 60. Milne explicitly permits an arbitrary k-algebra R_0 and uses exactness of the additive faithfully flat Cech complex. I expanded that argument rather than importing the nonabelian classification of torsors as a black box. For the supporting inputs I read topologies.tex at Tags 022C and 022E, morphisms.tex at Tag 01U5, algebra.tex at Tag 00HQ, and descent.tex at Tags 023M and 023Q. The tag/label correspondence for 023M, 023Q and 022E was checked in stacks-project/tags/tags. There are no new nodes requiring additional sources or smaller-statement tests.

For step 1 I opened every cited node. def-pc-fppf-site defines exactly flat, locally finitely presented, jointly surjective coverings, so the hypothesis on f supplies a singleton covering. lem-trf-fppf-covering-is-fpqc changes its topology; lem-galois-fpqc-singleton-affine-refinement gives both the affine flat surjective refinement and its actual map h into P. It makes no separatedness or affineness assumption on P. lem-weil-pbc-flat-morphism-affine-criterion gives flatness of the coordinate ring map; lem-weil-pbc-flat-surjective-spectrum-faithfully-flat adds faithful flatness. None of these citations is being used for a conclusion absent from its statement.

For step 2 I read lem-weil-pbc-fibre-product-affine-spectra, def-weil-affine-spectrum and def-sc-gm-ga. The first explicitly identifies both projection maps with insertion of tensor units. The spectrum definition gives the ring-map/morphism bijection; the additive-group definition gives the addition and inverse formulas on the coordinate. Polynomial evaluation and the action law then give the written cocycle equation. The step is elementary relative to these cited statements and the torsor isomorphism in the item's hypothesis: it proves its own cocycle identity, rather than citing an unstated torsor-classification theorem. The equalities are identities of scheme morphisms, via the inverse torsor isomorphism; testing only geometric points would not suffice for nonreduced bases.

For step 3 I opened lem-pc-cech-exact and checked that it allows any faithfully flat ring map and any module, with no finite-generation or Noetherian hypothesis. Substituting M=A gives exactness at B tensor_A B. I wrote both differentials and used the sign c=b_2-b_1 with the correction t=h-b. Thus t_2=h_1+c-b_2=h_1-b_1=t_1; the correction uses the group inverse specified by def-sc-gm-ga, whose statement was also read. This avoids an unproved assertion that a cohomology-class identification respects the particular torsor.

For step 4 I opened lem-weil-pbc-fpqc-representable-descent: its statement gives existence AND uniqueness of maps from a matching family into any scheme, not just a fully faithful Yoneda embedding or descent of modules. The fpqc cover is the one established in step 1 and t matches by step 3. Apply existence with target P, then uniqueness with target S to prove f composed with e equals the identity. No affineness or separatedness of P is used.

I checked delivery-errors B through E against the actual node and sources: every non-elementary input is a cited existing statement; each citation has a literal quote in citations.json; proof_deps is the union of uses; the proof carries the cocycle and translation arguments instead of moving the conclusion into another node; no lemma with missing hypotheses, hidden comparison, circular step, or degreewise/derived ambiguity is introduced. Each step is shorter than 2000 characters. Other-unit tools are declared individually in split_report.tool_uses for review, with their precise uses.

For small cases, A=0 gives the empty scheme and the unique section; the affine refinement explicitly allows the empty coproduct. For the trivial torsor P=G_a,S, writing a local point as a gives c=a_2-a_1 and the correction by b=a gives the zero section, checking the sign. For A=k[epsilon]/(epsilon^2), the inverse torsor isomorphism and tensor-ring identities still work including nilpotents. Characteristic p introduces no division or averaging, and imperfect k needs no modification. No finite-type-over-k, reducedness or perfection has entered the proof.

## Unfinished work

None in the requested stage-1 split. All lower inputs already have DAG nodes; their own proof statuses are independent of this delivery. No Lean was written, no compiler or Lake command was run, and no repository or launcher file was changed.

## Validation

The required deliver.py dry run and final delivery are run after writing this report; their result is recorded by the delivery tool and the final delivery message.
