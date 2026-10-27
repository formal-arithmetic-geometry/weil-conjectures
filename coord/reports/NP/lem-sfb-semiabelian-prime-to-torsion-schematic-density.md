# Stage-1 report: lem-sfb-semiabelian-prime-to-torsion-schematic-density

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-prime-to-torsion-schematic-density.json`: the item is split into six proof steps; its statement and statement dependencies are unchanged. Mathlib searches give no match.
- `citations.json`: 15 exact quotations, one per cited node per step.
- New nodes: 0. Mathlib leaves: 0. All needed non-elementary inputs already have nodes.
- `searches.jsonl`: actual searches made using the required msearch command. `write_split.py` is sandbox-only bookkeeping, not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint id, semiabelian/semiAbelian/SemiAbelian, and torsion-density phrases. No project declaration states this result. The existing smooth geometrically reduced and rational-point nodes already carry their project declarations; those are used through their node statements.

## WANTED

No additional document is required for this split. The source field's local Milne AV PDF does not itself state semiabelian schematic density, and the already existing abelian-density node records its own outstanding request for the 2022 Milne article. This delivery does not claim that missing article was read or use it as its proof source.

## Changes and source audit

The imported item was statement-only, not a previous completed split. Its source correctly labels the semiabelian extension as agent-formulated. I read Milne, *Algebraic Groups* (local iAG2017 PDF), Theorems 12.32–12.33, printed pp.242–243, and Aside 12.51, printed p.248: the latter explicitly records prime-to-characteristic density for toroidal groups and preservation under extensions, but does not give the desired fibrewise argument. I also read the local Milne AV I section 10, printed pp.42–45, which provides torsion/isogeny background rather than a verbatim density statement. Accordingly `proof_origin.by` is `agent`; the proof itself contains the extension argument, using the already existing abelian and torus density statements.

The chapter record and unit record were read, then compared with the current `literature/blueprint/latest` (main-20261024) unit and proof. This is an inherited auxiliary node deep below the independent power-prolongation route, not a statement of a blueprint unit. `blueprint_refs.py ancestor` prints None; I preserve its inherited from.node, via chain and the already specific from.place. Whole-DAG and blueprint searches for semiabelian, torsion, prime-to, torsor frame, fppf open and smooth affine group torsor found existing supporting nodes rather than a missing dependency. No chapter or unit route is changed.

## Not duplicates

There are no new nodes and hence no new/existing-node pairs to compare. In particular I reused `lem-sfb-abelian-prime-to-torsion-dense`, `lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density` and `lem-sfb-smooth-affine-group-torsor-representability`, rather than inventing a semiabelian-density restatement, a torsion-fibre density lemma or a new openness lemma.

## Review by NP

I checked every step against the full statements of its cited nodes and the relevant local sources, not just their titles.

Step 1 uses the explicit exact fppf sequence in `def-sfb-semiabelian-geometric-fibres` at the identity geometric point. This really supplies a split torus kernel and an abelian quotient, with local lifts; it does not automatically assert smoothness or openness of that quotient. I therefore prove the torus's smoothness from `def-sbc-smooth-morphisms` by its finite Laurent presentation and the explicit square-zero unit-lifting formula. This is a short definition-level calculation, not a new lemma. It works for the empty list of coordinates. The Laurent monomial description also verifies the Hopf-algebra hypothesis of the diagonalizable-density node used later.

Step 2 obtains local translation trivializations from the kernel and fppf local lifts on all test schemes, as in Stacks groupoids.tex 0499 (`lemma-characterize-trivial-pseudo-torsors`) and 049B (`lemma-torsor`), whose complete statements I read. I read 049C (`remark-fun-with-torsors`), descent.tex 02VL (`lemma-descending-property-smooth`), and morphisms.tex 056G (`lemma-smooth-open`) for the generic represented-torsor input. The cited torsor node explicitly gives smoothness, surjectivity and universal openness, so this is not a definition node being used as a theorem. Its hypotheses are affine/smooth/finitely presented for the group over the base, verified for the torus in step 1, and fppf local equivariant triviality, verified by the displayed inverse formulas. The exact-sequence definition is already phrased in fppf sheaves. The cited Yoneda node gives precisely the bijection between morphisms and natural transformations needed to identify the representing scheme with the given G. I do not use the more general Hom(h_A,F)=F(A) version of Yoneda.

Step 3 applies that same torsor theorem over Spec F directly to each rational fibre, so it does not assume a rational lift merely from fppf epimorphy. Its conclusion makes the fibre nonempty and smooth, and `lem-pc-rational-points-dense` explicitly says that such a scheme has a rational point over a separably closed field. Algebraic closedness implies separably closedness by the polynomial-root argument written in the step. I checked each correction equation: q(ny)=0, ny=i(a), nt=a and n(y-i(t))=0. Coordinate n-th roots are nonzero because their n-th powers are units. This uses exactly the polynomial-root clause of `def-weil-algebraic-closure`.

Step 4 is the central density argument and is written in full. I checked the translation inverse on all test schemes, rather than just F-points. Stacks schemes.tex 01JU (`lemma-fibre-product-immersion`) is the source of the cited closed-subscheme pullback theorem, whose statement really makes W closed. The product nm remains invertible in F, so every translated invertible-order torus torsion point factors through Z by the item's hypothesis. Pointwise containment alone is not silently promoted to scheme containment: the diagonalizable-density node explicitly states that every allowed torus kernel is a finite disjoint union of Spec F, and only then are its component maps assembled. Its schematic-density conclusion gives W=T. Milne 12.32 is the source of this input, not a supposed general theorem about all commutative groups. This step is 1271 characters, and hides no separately assumed torsion-lifting comparison.

Step 5 uses exactly the topological closed-subset conclusion of the existing abelian-density node and the open quotient proved in step 2. If G minus |Z| is nonempty its image is a nonempty open; hence it meets an abelian torsion point's image. Such a rational point has residue field F, so the fibre over it is the ordinary topological inverse image (no geometric-point extension ambiguity); step 4 excludes that intersection. This proves full support without assuming q is proper or closed.

Step 6 uses the actual conclusion of `sbc-lem-smooth-geometrically-reduced` (the fibre G is geometrically reduced), and the affine reduced-ring equivalence in `def-pc-reduced-scheme`. I read Stacks varieties.tex 056T (`lemma-smooth-geometrically-normal`), schemes.tex 01J1 (`lemma-reduced`) and varieties.tex 09NW (`remark-conductor`). The final cited reduced-ideals node explicitly states I intersect J=0 when their vanishing loci cover Spec R, so applying it with both ideals equal to I proves I=0. Thus full support is correctly upgraded to equality of closed subschemes. No tacit nilradical theorem is needed.

I checked delivery-errors B1–B10: no new nodes, no missing definition in the unchanged item statement, TeX is stored once, citations use the actual Stacks tags and labels, actual Mathlib queries are recorded, no false Mathlib leaf or project attachment is claimed, and blueprint provenance is preserved. C1–C8: every substantive input is an existing cited statement, every one was opened, quotes in citations.json are verbatim full statements, and generic off-unit inputs are declared in split_report.tool_uses for review. D1–D5: the six steps carry the lift/translation/open-image/reduced-ideal argument itself; there is no new node restating a clause or carrying the whole result. E1–E7: no properness of G or connectedness beyond the semiabelian definition is smuggled in; no factorization is inferred merely from topological containment in a nonreduced target; multiplication by n is surjective on the split torus's F-points by roots, and no analogous assertion for arbitrary group schemes is used.

Small cases checked: r=0, B of dimension zero, G the trivial group, n=1, characteristic zero (all positive integers allowed), and characteristic p>0 (only integers nonzero in F are used; nm is again nonzero). Nonreduced test algebras are respected in the translation isomorphisms; reducedness is used only for the final source G. Every proof step has fewer than 2000 characters. No statement dispute was found. No Lean file, compiler, Lake tool or repository git command was used.

## Unfinished work

None in this one-level split. The cited existing nodes retain their own separate stage states and proofs. Dry-run and delivery results are recorded by the required delivery command.
