# Stage-1 report: lem-sfb-borel-maximal-torus-conjugacy

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-borel-maximal-torus-conjugacy.json: existing statement, now split into five steps; no Mathlib match.
- citations.json: one checked verbatim statement excerpt for every step/node citation.
- searches.jsonl: actual search-command output records for this attempt.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The item's statement, statement dependencies, source and provenance are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and maximal-torus/Borel notions; no declaration states this item. No Lean was written or compiled.

## WANTED

None. Read literature/milne-algebraic-groups_iAG2017.pdf directly with pdftotext. The proof follows Milne, not SGA; Milne's incidental historical reference is not a source used by this split.

## What needed repair

The item was statement-only. Its source's first sentence, “When G is solvable”, needed an actual dependency-level argument. Existing lem-sfb-solvable-torus-complements states that each maximal torus maps isomorphically onto the torus quotient, but does not itself state conjugacy. Step 3 therefore constructs the two inverse sections and applies the existing section-conjugacy node, with its required smooth quotient verified.

The general Borel flag-variety node cannot be used here: its proof depends on lem-sfb-borel-scheme-normalizer, whose proof uses this item. Instead step 2 proves Borel conjugacy directly from the existing homogeneous quotient, properness, and solvable fixed-point statements. This is Milne's proof of 17.9(b), below the unit route. No statement dispute or source correction was needed.

## Unfinished work

None for this stage-1 split. Existing dependency nodes remain their owners' work. This delivery supplies no Lean proofs and makes no claim of completing those nodes.

## Not duplicates

No new nodes were created. Whole-DAG keyword and source-place searches found the existing nine inputs now cited, including the already finer triangular-section assertions. tools/blueprint_refs.py search was run for Borel and maximal torus over all imported nodes: no imported node states this item. The Borel results concern Borel--Moore homology. blueprint.same_as is therefore empty. The ancestor command returns None, as already recorded by this item's inherited blueprint chain; no invented ancestor was substituted.

## Review by Q10

I read the chapter and unit records, SETUP's three route levels, GOAL, stages/1-dag.md, coord/brief-stage1.md, and both copies of delivery-errors B--E. I read the current latest blueprint direct-image proof (3). The long inherited from.place chain supplies a supporting algebraic-group prerequisite for that route, not a replacement of its alteration or sheaf argument.

For the item I read Milne 17.9 and 17.10 on printed pp.354--355 and the paragraph after Definition 17.12 on p.355. For the solvable expansion I read Theorems 16.26--16.27 on pp.332--333, Summary 16.29 and Lie--Kolchin on pp.334--335, and 16.33 on p.336. I also read quotient Definition 5.20 and Propositions 5.21--5.27 and Theorem 5.28 on pp.104--105; the torus characterization on p.236; the maximum-dimension method on p.134; and Borel fixed-point Corollary 17.3 on p.353. There are no new nodes needing independent literature sources.

Step 1 uses the explicit smoothness/connectedness assertion of lem-sfb-multiplicative-type-largest-subtorus and the strict dimension increase and finite ambient bound in lem-sfb-solvable-normal-subgroup-products. The latter assertion applies to arbitrary closed inclusions of smooth connected groups; its separate product assertion's normality assumptions are not being imported. Choosing a greatest dimension in a nonempty bounded set of nonnegative integers is elementary. The trivial torus starts the set; commutativity makes a torus solvable. Thus this step proves existence and containment without assuming any Borel-conjugacy theorem.

Step 2 uses lem-sfb-homogeneous-orbit-quotient-geometry for the represented fppf coset quotient, torsor fibre identity and lifting of F-points. I checked its whole statement, not just the quoted lifting clause. The left action follows directly from multiplication on the coset sheaf: changing g to gb leaves hgB unchanged. lem-sfb-borel-quotient-proper-geometry applies because B is closed, smooth and connected, and maximal solvable; it gives properness for that same quotient. lem-sfb-solvable-proper-fixed-point applies to C, which is smooth connected solvable, acting on the nonempty proper finite-type quotient. Its conclusion fixes the point over every algebra, so g^{-1}Cg lies in B scheme-theoretically. Borel maximality supplies equality; no assertion about scheme stabilizers or normalizers of a Borel is used.

Step 3 checks all five cited statements. Lie--Kolchin supplies a closed triangular realization of H; the derived series in the item is already a normal series with commutative quotients. The triangular diagonal-kernel node supplies exactly V=J intersect U_n, its normality and unipotence, the represented quotient, and smoothness and connectedness of V and D. Its closed embedding of D in a torus and the smooth-connected multiplicative-type characterization show D is a torus. These are precisely the hypotheses of solvable-torus-complements, applied with U=V. Inverting q restricted to S_i produces actual group-scheme sections, not merely sections of F-points. Section conjugacy requires D smooth, verified above, and yields the equality of morphisms and hence equality of their subgroup images over every algebra. No unsupported conjugacy clause was attributed to the complement node.

Step 4 uses only the previously established steps: maximality in G implies maximality in the containing Borel; conjugation preserves inclusions and torus structure. The product bg has the correct direction, sending T_1 to T_2. Step 5 likewise uses only steps 1 and 2, transporting an ambient maximal torus into the prescribed Borel. These two steps are elementary assembly and cite no further node. All five steps are under 2000 characters and hide no additional comparison or standard lemma.

I checked small cases: the trivial group and rank-zero torus; G a torus (its only Borel is G); G unipotent (maximal tori trivial); and upper triangular GL_2 (distinct complements are related by the section-conjugacy step). The proof never requires reductivity, positive rank, characteristic zero, a smooth nonreduced stabilizer, or detection of subgroup schemes by F-points. The quotient fixedness and the section equality are explicitly over all F-algebras, so infinitesimal algebras are covered.

For delivery-errors B, no new statements or hollow data were introduced, all TeX in the unchanged statement is retained, and real search records are appended without inventing queries. For C, every cited statement was opened, its used hypotheses checked above, every step/node pair has a verbatim excerpt in citations.json, and the nine dependency closures were checked to avoid a return path to this item. All nine inputs have the same unit as the item. For D, the actual argument is in the item, with no relabelled clauses or new wrapper nodes. For E, the edge cases and the full scheme-theoretic interpretation were checked as above. Mathlib search hits concerned abstract groups, Cartan subalgebras, or root-system constructions; none asserts an algebraic-group-scheme conjugacy theorem. No new node or leaf was warranted.

The first dry run required the step-1 torus quotation to be at least 40 characters. I extended it verbatim to include the next sentence; the argument and cited assertion are unchanged.
