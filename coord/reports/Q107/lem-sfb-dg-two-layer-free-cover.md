# Q107: lem-sfb-dg-two-layer-free-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-two-layer-free-cover.json: statement, now split; no Mathlib match. Seven explicit elementary construction/check steps, statement unchanged.
- citations.json: empty list, because none of the proof steps invokes another node. The existing size-convention node remains a statement dependency.
- searches.jsonl: actual new searches made by msearch.py; inherited item search records retained separately in the node.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint id and the notions two-layer, twoLayer, semi-free, DGModule, DGAlgebra, differential graded, and surjectivity on cocycles. No project declaration states this cover theorem. Hits about Hom complexes or descent cocycles are not DG-module covers.

## WANTED

None. The required source is present locally.

## Source and blueprint audit

Read Stacks dga.tex, Tag 09KN (lemma-good-quotient), its full statement and proof, and definition-shift. The item is the source's construction with explicit homogeneous generators, graded splittings and universe bounds. Also read the chapter record sec-six-functors-basics, the unit record sk-thm-sf-ctf-stability, and the current literature/blueprint/latest proof of det-thm-sf-ctf-stability-direct-images, especially (3). The inherited long support chain is retained, and this local algebra construction changes none of that route. The ancestor command returns null; no fictitious blueprint ancestor was introduced. Whole-blueprint searches for free cover, differential graded and graded found no equivalent blueprint statement.

Read the existing statements lem-sfb-dg-countable-free-cover, lem-sfb-dg-property-p-resolution, lem-pc-derived-free-complex-cover, lem-pc-zero-differential-free-coproduct and lem-sc-p1-graded-free-cover after DAG searches for Tag 09KN and the relevant words. The first has additional countability assumptions on both A and N; the property-(P) theorem supplies an iterated resolution rather than a two-layer cocycle-surjective cover. The ordinary-complex lemmas do not allow a DG algebra with a nonzero differential. The polynomial graded-cover result is a different notion of grading and requires finite generation. None can serve as the unrestricted theorem. The already-reviewed countable-cover proof was useful comparison material for checking the common coordinate construction; its countability theorem is neither cited nor used here.

## Mathlib search results

Ran msearch.py for one grep, one Loogle search, two distinct LeanFinder phrasings and one LeanSearch query, all recorded in searches.jsonl and appended to the item's search records without altering the inherited records. All services returned results. Read the hits and the source of Mathlib/Algebra/Homology/DifferentialObject.lean (ordinary differential objects versus complexes), Mathlib/Algebra/Module/GradedModule.lean at GradedModule.linearEquiv (209ff), HomComplexSingle.lean at the cochain and cocycle fromSingleMk/toSingleMk surjectivity lemmas (110ff, 201ff, 251ff, 325ff), and ModuleCat/LeftResolution.lean (ordinary module free covers and resolutions). These neither construct the disk differential over an arbitrary DG ring nor give this theorem in one specialization. No Mathlib leaf is claimed. Exact queries, returned names and verdicts are in the JSON and log.

## Source error

The last part of the proof of Tag 09KN writes A[k] mapping its unit to a cocycle of degree k. With definition-shift in the same source, A[k]^n=A^{n+k}, its unit has degree -k, so the notation there should be A[-k]. For example, A is Z in degree zero, N is Z in degree one with zero differential, and k=1: the degree-preserving map A[1] to N must be zero, whereas A[-1] sends its unit to 1 in N^1. The item already uses A[-t_w], which is correct; its statement is unchanged. This is a local sign typo in the source's proof, not a change of mathematical route.

## Review by Q107

I checked the actual source proof of 09KN and the shift definition, then compared every output clause with the unchanged item. The complete construction is given in the steps; no assertion is delegated to a restatement node, and no source lemma is used as a black box.

Step 1 introduces the tagged x, y and s symbols and the finite-support coefficient groups, and writes their action explicitly. The basis assertion follows from unique coordinates, with associativity and the unit inherited coordinatewise from A. This uses only the graded-ring/module axioms given in the item and no cited statement. The y and s symbols are in U; only x symbols are in V.

Step 2 defines D on those coordinates, checks finite support, degree, and the complete signed Leibniz expansion. I checked d_A(1)=0 by cancellation before identifying D(e_w) with delta_w. The coefficient degree is |a| and the generator degree is t_w, so the final Leibniz sign is t_w+|a|, as the item requires. No external fact is invoked.

Step 3 calculates D squared. The y and s terms vanish by d_A squared equal to zero. For x of degree k the y term has degree k+1, so the mixed coefficients are (-1)^(k+1) and (-1)^k and cancel. This is a direct calculation, including for negative k and in characteristic two. It proves the DG structure and the required triangular generator differential rather than assuming them.

Step 4 gives pi on every symbol, proves its module and degree laws, and checks commutation with D using precisely d_N squared equal to zero and the defining condition for Z. Each homogeneous m is lifted by its own x symbol, and each actual cocycle z by its own closed s symbol. No passage from cohomology classes to cocycles or unproved lifting property is needed.

Step 5 proves stability of the U coordinate submodule, writes its graded retraction, and constructs the quotient identification with V coordinates by mutually inverse maps on cosets. Its kernel is exactly the U coordinate submodule, and delta_v vanishes in that quotient. There is no appeal to a structural quotient theorem, and no claim that the retraction commutes with D.

Step 6 checks both DG shift isomorphisms on coefficients and inverse coefficient maps. For degree t the copy is A[-t], whose differential (-1)^(-t)d_A equals (-1)^t d_A, matching steps 2 and 5. The right action is unchanged in the source and in the item. This also fixes the source proof's local A[k] typo described above.

Step 7 verifies the size bound using the defining closure operations of a Grothendieck universe: subsets, Cartesian products, power sets and indexed unions. All coefficient families are functions on the set W with finite support, so their sets are subsets of sets already in u; the integer-indexed homogeneous union is in u as well. This invokes no additional theorem about small categories, filtered colimits or countability. The only ambient convention is the item's existing statement dependency def-weil-size-convention, whose statement I read; it is not used as a theorem asserting any DG construction.

Against delivery-errors B, there are no new statement-only nodes to make self-contained or search, all definitions needed for this explicit construction are in the item's statement, the TeX is written once, the Stacks place is identified by tag and label, and no unsupported Mathlib match or project attachment is claimed. Against C, there are no proof citations whose statements could fail to supply an input; citations.json is therefore empty. The proof dependency union is also empty, so no new cycle or off-unit theorem edge is introduced. Every step is elementary because it explicitly performs a finite-support construction or an algebraic calculation from the stated definitions. Against D, the proof is the actual disk-and-cocycle argument, not a reference to 09KN or new nodes restating clauses; no induction or omitted standard lemma is hidden. Against E, I checked the input hypotheses at each use: arbitrary associative unital DG A, arbitrary unbounded right DG N, both in u. No flatness, commutativity, countability or boundedness is used. I reviewed the lengths too: all seven steps are below 2000 characters.

For edge cases, N=0 leaves tagged zero generators, which still map surjectively to zero; A=0 forces every unital N to be zero, and coordinate construction and coefficient maps remain valid. In degree t with t negative the same parity formulas hold. If d_N=0 all elements get closed s lifts while x still maps to the corresponding element and y maps to zero. Nonzero d_A is handled by both terms in D, and noncommutativity is harmless because every displayed product retains its original right-action order. No statement repair or new node was needed.

## Unfinished work

No mathematical part remains. Required delivery checks and push are performed after this report is written.
