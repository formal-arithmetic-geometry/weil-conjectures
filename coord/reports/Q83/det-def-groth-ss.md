# Stage 1 delivery: det-def-groth-ss

Group Q83, direct delivery, 2026-10-24.

## Files written

- `dag/nodes/sec-picard-framework/det-def-groth-ss.json`: existing definition/construction, now split into six steps. Mathlib verdict: no match for the whole compound item. Its statement is unchanged byte for byte; statement dependencies now name the notions it uses.
- `citations.json`: eleven entries, one for every step/node pair; each quote is the verbatim full statement of the node read.
- `searches.jsonl`: six actual calls of the required search wrapper, including two distinct semantic phrasings and two source patterns. Results were read before recording the verdicts.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All required facts already have nodes; creating clause nodes would duplicate them or merely restate this item.

## Attachments

None proposed. This is a split delivery, not a renewed ATTACH claim. I read the live project definitions in `CategoryTheory/SpectralSequence/Grothendieck.lean`, `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`, and the exact-couple modules `FilteredComplex.lean`, `TotalComplexFiltration.lean`, `FirstQuadrant.lean`, `DoubleComplex.lean`. These help check conventions; the report does not treat a docstring tag, a declaration for only part of the item, or a sorry declaration as an attachment of the complete item.

## WANTED

None. All literature used is already available in the repository.

## Problems found and repaired

The imported node has no statement dependencies and no argument for the mathematical claims inside its final paragraph. I filled the dependencies and wrote the actual exact-couple construction, derivation, and assembly of the image-filtration abutments. I retained every original clause and did not add left exactness to the functors.

There is an important convention issue: `def-sp-exact-couple` starts with a differential of bidegree (2,-1), while the couple of a filtered complex initially gives the page-one differential (1,0). A bare citation of that definition would be C4. Step 4 explicitly changes coordinates (P,Q)=(2p+q,-p), whose inverse is (p,q)=(-Q,P+2Q). This turns inclusion, boundary, quotient into the DAG convention, and Step 5 converts the iterated differentials back. Hence derivation number s is actual page s+1. This supplies the exact-couple assertion missing from the rejected attachment without creating another node for that clause.

The pre-existing `def-sp-acyclic`, `def-sp-composite-acyclicity` and `def-sp-left-exact-additive` impose left exactness. They cannot justify this item's definition for arbitrary additive functors. Instead Step 1 uses `lem-weil-pbc-right-derived-plus-injective`, whose statement explicitly permits additive functors and computes on bounded below injective complexes. Stacks 015A likewise defines higher derived functors for additive functors; no claim R^0v=v is made here.

I interpret the final paragraph's F separately for the two degree filtrations. The node does not assert that these two filtrations on total cohomology coincide. For a single nonzero term in bidegree (1,0), the first filtration has F^1 H^1=H^1 and the second has F^1 H^1=0, which confirms why that distinction is necessary. The statement itself needs no correction.

## Not duplicates

No new nodes. `sk-def-groth-ss` states the same compound definition and has been recorded under the item's `blueprint.same_as`; it is not used to prove itself. `thm-sp-double-complex-spectral-sequences` already supplies both sequences and the specified image-filtration abutments, so those claims do not become new nodes. The long exact sequence and derived-couple iteration also already exist.

## Review by Q83

I read `coord/delivery-errors.md` B–E in full, the current blueprint at `literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/det-def-groth-ss.md`, its chapter and unit records, the stage-1 rules, GOAL.md and SETUP's three levels. The unit concerns the Picard perfect locus; this supporting definition supplies the homological machinery used within that route, rather than replacing any perfect-locus step. I do not change the unit or chapter. Generic theorems from other units are declared in `split_report.tool_uses` with their reasons.

For sources, I read Stacks `derived.tex` at 05TI (`lemma-enough-injectives-right-derived`), 05TH (`lemma-injective-acyclic`, via its use in 05TI), and 015A (`definition-higher-derived-functors`). I read `homology.tex` at 0117 (`lemma-long-exact-sequence-cochain`), the exact-couple section 011Q/011R/011S and shifted variant 0AMJ, filtered complexes 012K/012M, induced cohomology filtration 012P and finite-per-degree convergence 012W, and double complexes 012X/0132. I checked the tags against `tags/tags`. I also read `injectives.tex` at 079H (`theorem-injective-embedding-grothendieck`) for the enough-injectives input. No new node has a source to audit, since none is created.

Step 1 uses exactly the statement of `lem-sp-grothendieck-enough-injectives` to obtain enough injectives in A and B. `lem-weil-pbc-right-derived-plus-injective` then supplies the existence, computation and uniqueness of the bounded below right derived functor for an additive functor with abelian target. Its source condition is satisfied for F and GF by A, and for G by B; no injectives in C are needed. `def-sp-injective-resolutions` specifies the resolution used, and the step writes the successive-cokernel construction rather than treating the definition as a resolution-existence theorem. The acyclicity conditions are then simply the predicates written in the item.

Step 2 uses `def-sp-spectral-sequence` for the successor-page homology isomorphism and `def-sp-filtration` for decreasing subobjects and their quotients. The vanishing proof is elementary: incoming source has negative first coordinate for r>p and outgoing target has negative second coordinate for r>q+1. Thus p+q+2 works even at p=q=0, where the stable page is 2. This proves the choice of infinity page; the abutment itself is defined, not asserted to exist for an arbitrary spectral sequence and arbitrary family H.

Step 3 uses the actual formulas in `def-sp-double-complex-total`. They state finite diagonal sums, the signed total differential, both subcomplex filtrations, and the graded pieces. The exact sequence of successive steps is degreewise split by sorting the finite summands into index exactly p and index greater than p. This is the elementary finite-biproduct argument, not a new lemma or an appeal to an unjustified preservation-of-exactness theorem.

Step 4 uses `lem-weil-pbc-complex-ses-homology-long-exact`, whose statement covers integer- or natural-indexed cochain complexes in an arbitrary abelian category and gives all three adjacent exactness conditions. Step 3 verified its degreewise short exact hypothesis for each chosen F. I read `def-sp-exact-couple` and verified all three maps, not just the composite differential: (P,Q)=(p+n,-p) turns the filtration inclusion into (-1,1), the boundary (p,n)->(p+1,n+1) into (2,-1), and the quotient into (0,0). No infinite direct sum of bigraded terms is taken; this is a family with componentwise exactness.

Step 5 uses clauses 2–4 of `lem-sp-derived-couple-exact`: the maps exist, their derived couple is exact, and iteration gives the successor homology objects. The hypothesis is precisely the reindexed exact couple proved in Step 4. The inverse coordinate change sends the derived differential (s+2,-s-1) to (s+1,-s), so its page numbering is correct. `thm-sp-double-complex-spectral-sequences` identifies its two sequences as the spectral sequences of the two filtered total complexes, with the initial graded cohomology stated there. I use that defining construction, not an unstated comparison with unrelated spectral-sequence data. Negative filtration indices give zero graded pieces, and total degree below the filtration index gives a zero complex, proving the support assertion without a hidden convergence hypothesis. I do not need the theorem's normalization of the second d1: Stacks displays a row sign for the raw total-complex convention, which can be changed by rowwise normalization. This item asserts neither a normalized d1 formula nor an equality of the two filtrations.

Step 6 quotes the part of `thm-sp-double-complex-spectral-sequences` that explicitly states the image formula, both endpoints and the graded-piece isomorphisms. It is not a citation of an abstract abutment-existence claim in place of the requested image filtration. Its hypothesis is a first-quadrant double complex in an abelian category, exactly the one supplied. Each F is the very filtration from Steps 3–5. The endpoints are also checked directly: at zero the map is identity, and F^(n+1)K has zero nth term so zero nth cohomology. The theorem's stabilization bound r>max(p,q+1) includes r=p+q+2.

Edge cases checked: the zero double complex; a single term at (0,0); a single term at (1,0) distinguishing the two filtrations; n=0 (only F^0/F^1); a double complex with unbounded nonnegative indices but finite diagonals; and an arbitrary abelian C lacking countable coproducts. Only the finite sums along individual diagonals are used, so no hidden Grothendieck condition on C is needed. An arbitrary additive functor need not be left exact, and the proof makes no R^0 identification. Every non-elementary input is a cited existing node; the full statements are copied in `citations.json`, so a C4 gap cannot be concealed by a paraphrased quote. All proof steps are under 2000 characters. New-node conditions B1–B10 are vacuous except for reuse and search: no new definition, elementary lemma, clause copy, or Mathlib result is added. There is no statement dispute, no route change, and no SGA source.

## Unfinished work

None in this stage-1 item. The independent maintainer review remains responsible for acceptance; the item's existing dependencies retain their own statuses.

## Validation

Server `review_split` passed: zero new nodes; the unit has no realization recorded yet, which is outside this supporting item. The complete `deliver.py --no-push` dry run passed server preflight, including the DAG and split checks, on 2026-10-24. The final report is included in a fresh dry run before pushing. No Lean, compiler, Lake or build command was run, and no repository or launcher file was written.
