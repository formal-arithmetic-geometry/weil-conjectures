# Worker report: lem-coef-dgcat-cone-word-normal-form

## Files written

- dag/nodes/sec-six-functors/lem-coef-dgcat-cone-word-normal-form.json: existing statement split in five steps; Mathlib verdict no match; no new nodes or Mathlib leaves.
- citations.json: exact statement excerpts for each of the three node citations.
- searches.jsonl: five actual Q22 searches, with two semantic phrasings, Loogle and source grep. The item's five inherited Q94 search records are preserved.

## Attachments

None. The project source search by exact blueprint id returned no declaration, and searches by cone/word/normal-form and dg/graded-category concepts returned unrelated smooth-local-normal-form, Frobenius and ordinary homological-category material. Neither the read-only upstream master nor slopmaster2 supplies a finished declaration stating this item.

## WANTED

WANTED: Gonçalo Tabuada, Théorie homotopique des DG-catégories, arXiv:0710.4303, Chapter 1, §1.3.1, Lemma 1.10, printed p. 29, for lem-coef-dgcat-cone-word-normal-form; the PDF is readable online but is not archived in literature. No download or repository edit was made. The proof is explicitly by agent.

## What was wrong

The item was statement-only with no proof. Its statement, statement dependencies, source, ancestry and audit records are preserved. In particular “on the labelled representables and Z=C_u” denotes the object set consisting of the representables together with that cone, as in the parent construction; it does not omit Z. There is no statement dispute or route change.

## What could not be finished

Nothing mathematical remains for this one-level split. The free-cell and formal-cone prerequisites already exist and are reused; their subsequent Lean proof is outside this stage-1 delivery.

## Not duplicates

No new node is created. DAG and whole-blueprint searches for dgcat/cone/word/normal form, contracting, and matrix components found no blueprint statement equal to this item; same_as remains []. The free-cell lemma supplies words in h, and the formal-cone lemma supplies coordinate maps, while this item removes the cone endpoint from those words. The parent equivalence-cell-calculus uses the item and cannot be cited back without a cycle. The cell-comparison-functors sibling constructs comparison functors, whereas this item proves graded generation and equality detection.

## Review by Q22

I reread delivery-errors B–E against the actual node statements and this proof. There are no new statement-only nodes to audit under B1–B8, and no restatement of the conclusion has been moved into a prerequisite (D1–D2). All notions in the statement are either defined inline or supplied by its two unchanged statement dependencies. The existing blueprint ancestry has an exact place and the proof report states its role. The unit record sk-prop-sf-biduality-general and chapter record sec-six-functors were read; the item is a prerequisite, not a key unit realization, and neither record is changed.

For the external source I read Tabuada's Lemma 1.10 online at printed p. 29 (PDF page index 28). It constructs the full category on representables and a cone, adjoins a contraction, restricts to representables, and asserts that the inverse comparison is checked directly. Here the omitted graded word computation is supplied explicitly, rather than quoted as a theorem. I also read the main-20261015 ancestor proof paragraph 2, the finite mapping-complex adjunction, and the parent equivalence-cell-calculus steps 3–6. This is its inverse-verification input and preserves that route. No SGA source is used. The two cited prerequisites are in the same unit, so no off-unit tool uses are required.

Step 1 cites the statement of lem-coef-dgcat-free-cell-calculus, read in full: it really supplies arbitrary arrow degree, an attaching closed element, the exhaustive word filtration, graded splitting, and tensor-word quotients. I verified its hypotheses with s=t=Z, degree -1 and attaching cycle 1_Z. The pure-tensor/lower-length induction justifies finite word spanning without assuming an infinite-series or associated-graded convergence result. The degree-preserving lifts are the words themselves. The differential relation dh=1 introduces no extra graded relation.

Step 2 cites the statement of lem-coef-dgcat-formal-cone-enlargement, also read in full. It supplies the maps of degrees 0,0,-1,1 and the actual graded splitting identity, not just a definition of a cone. I calculated the four degrees (-1,-2,0,-1), and their signs agree with (-b_h,-w_h,v_h,a_h). Step 3 is the two-sided distributive expansion of that identity around h; each summand has degree -1 and no factors are permuted. It uses step 2, not an uncited theorem or the proof of the prerequisite.

Step 4 uses the embedding clause of the formal-cone statement: every coefficient after expansion is an existing L-arrow between representable labels, hence exactly an A-arrow. I checked the endpoints of a_m i_alpha, pi_beta a_j i_gamma and pi_delta a_0. Replacing all m copies of h produces at most 4^m terms; only original coefficients and four entries remain. This proves the actual generation clause rather than assuming it. Step 5 needs no further theorem: the common object map and equality on generators give equality on compositions by finite induction, then on finite linear combinations by R-linearity. Homogeneous decomposition is finite by the definition of a graded module. All external facts used by a step have statement citations with literal excerpts in citations.json (C1/C3/C4).

I checked u=0 (the graded expansion is unchanged), x=y (the two labelled coordinate slots are still distinct), zero ring, zero old morphisms, arbitrary degrees, characteristic two (minus signs collapse consistently), m=0 (the embedding clause), m=1 (the four components), and m=2 (all 16 terms are typed old-object composites). Repeated h is permitted: no h^2=0 assumption is used. Closedness of coordinate maps is never invoked. These checks address E1–E6 without excluding any case. No source error was found.

For Mathlib I read the actual five new search outputs, including the second phrasing. The semantic candidates are ordinary matrix reconstruction, free R-linearization and hom-orthogonal matrix decompositions. I opened Biproducts.lean:980–1021, HomOrthogonal.lean:50–95, ModuleCat/Adjunctions.lean:235–285 and 385–414, and Mat.lean:72–95. None states the free dg adjoining construction or deletion of a shifted cone object; hom-orthogonality is not even assumed here. Loogle returned zero hits; the three grep hits were ordinary limit-cone prose. All new queries and their exact logged records have been appended to mathlib_searches, without inventing queries or replacing inherited searches.

All five steps are below 1000 characters; no non-elementary step exceeds the 2000-character review threshold. The only non-elementary inputs are the two cited existing statements. I checked that proof_deps is exactly the union of uses and that neither prerequisite depends on this item. No extra node is needed for distributivity, finite induction or functor extensionality. No Lean was written, no compiler or local DAG checker was run, no git command was run, and all authored files are in the assigned sandbox.
