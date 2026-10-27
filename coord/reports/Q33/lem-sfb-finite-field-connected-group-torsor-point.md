# Q33 stage-1 report

Item: lem-sfb-finite-field-connected-group-torsor-point. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-connected-group-torsor-point.json: statement split using existing nodes; Mathlib searches found no match.
- citations.json: one verbatim statement quotation for each node used in each proof step.
- report.md: this report. searches.jsonl was produced by the required msearch.py commands.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag, Lang theorem, and connected-group torsor rational points found no declaration stating this item. The semilinear Frobenius Lang–Steinberg results concern additive vector spaces, and the finite-monodromy torsors concern a different assertion. No compiler or build command was run.

## WANTED

None for this split. The source used is already present: literature/milne-algebraic-groups_iAG2017.pdf.

## Corrections and route

The live item had no proof. Its statement is mathematically correct and was retained. I removed doubled TeX backslashes in its statement, a rendering defect only. Its inherited creation record, blueprint place and via chain were retained. blueprint_refs.py ancestor returned None for this chain; I retained that null ancestor instead of inventing one. Whole-blueprint searches for Lang, connected group variety and torsor rational point supplied no matching blueprint item. I read the latest direct-images proof and the latest unit section, and the chapter and unit DAG records. This split serves the inherited finite-field prerequisite to Milne 25.9(b), below the direct-image/alteration route; no chapter or unit route changes.

The proof is the point version of Milne's crossed-homomorphism proof: choose a geometric point, form its Frobenius displacement, remove it by the existing Lang-surjectivity theorem, then descend the fixed point. It does not replace the conclusion with a new node asserting H^1 triviality. In particular it does not use the converse torsor assertion to prove Lang surjectivity.

## Mathlib searches

The five searches recorded by msearch.py are appended verbatim to the inherited item records: leanfinder for torsor rational points; loogle for "Lang"; grep for Lang/torsor terms in AlgebraicGeometry; leansearch for principal homogeneous spaces; and leanfinder with a second phrasing using triviality of principal homogeneous spaces. Read the results. The affine-space hits and finite Galois-category transitivity hits do not concern algebraic-group torsors. FixedPoints and Frobenius-order results do not supply Lang's equation. Read Mathlib/Algebra/Torsor/Defs.lean:57–73: its abstract torsor structures already include nonemptiness. Read Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean:107: the cohomology vanishing concerns units of a finite field extension, not arbitrary smooth connected affine algebraic groups. No search service was unavailable. I preserved the inherited search records and added only the actual Q33 searches logged in searches.jsonl.

## Not duplicates

No new nodes were created. The existing lem-sfb-lang-finite-field-group-surjectivity states the required equation, and lem-weil-unique-subfield-of-closure already contains the fixed-scalar identity. I reused them instead of creating Lang, torsor-triviality, or Frobenius-fixed-point descent nodes. The affine-chart corestriction is a few lines from those cited statements and definitions and is written out in the proof.

## Review by Q33

I read Milne Corollaries 17.97–17.98 and their proofs, printed pp.382–383 (PDF pp.394–395), Definition 2.66 and Proposition 2.69, p.60 (PDF p.72), and Proposition 3.50 and its proof, p.80 (PDF p.92). These identify the torsor equation, its Frobenius cocycle and Lang's correction. There are no new-node sources to review. I also read the precise statements of every cited node, rather than relying on its title, and stored those statements verbatim in citations.json.

Step 1 uses the existence assertion of def-weil-algebraic-closure. lem-trf-fppf-covering-base-change explicitly preserves an fppf covering, with flat, locally finitely presented, jointly surjective maps; its singleton case gives both nonemptiness and local finite presentation after extension to K. The item supplies all three covering hypotheses, with no quasi-compactness needed. def-sbc-locally-finite-presentation and def-weil-finite-type-morphism give the elementary finite-generators implication. lem-sc-lft-over-field-jacobson-space explicitly gives density of closed points in every closed subset; taking the whole nonempty Y_K gives a closed point. lem-weil-pbc-closed-point-residue-field-base explicitly identifies its residue extension with K because K is algebraically closed and Y_K is locally of finite type. I checked these sources in Stacks topologies.tex, Tag 021O, lemma-fppf (3); varieties.tex, Tag 0478, lemma-locally-finite-type-Jacobson; algebra.tex, Tag 00FV, theorem-nullstellensatz; and morphisms.tex, Tag 01TB, lemma-jacobson-finite-type-points. I do not assume Y is affine or already has a k-point.

Step 2 uses the exact arithmetic q-power automorphism of def-weil-frobenius-substitution, the finite-field cardinality convention, and the contravariance in def-weil-affine-spectrum. Evaluating the assumed isomorphism gives the unique displacement a. The compatibility sigma(yh)=sigma(y)sigma(h) follows by composing the action diagram with Spec(sigma). This is an elementary definition-and-functoriality step, not a new torsor theorem.

Step 3 uses only the statement of lem-sfb-lang-finite-field-group-surjectivity: for every a there is g with g^{-1}sigma(g)=a. I verified the hypotheses one by one: finite base field, algebraic closure, smooth affine group of finite type, and connectedness supplied by geometric connectedness. Its coordinate definition of sigma agrees with precomposition. The calculation uses z=y g^{-1}, not y g; sigma(g)=g a, hence sigma(z)=y a (g a)^{-1}=y g^{-1}. This keeps the noncommutative factor order. The existing Lang node's dependency list contains no use of this torsor-point item.

Step 4 uses clause 3 of lem-weil-unique-subfield-of-closure, at n=1: the q-power-fixed elements of K are exactly the image of k. Its statement contains this identity explicitly, not just uniqueness of an unnamed finite subfield. An affine chart around the image of z suffices even without a global affineness hypothesis. The chart map A to K is fixed coefficient by coefficient; its image lies in k, and corestriction followed by the inverse field embedding is a k-algebra homomorphism. def-weil-affine-spectrum explicitly gives the corresponding scheme morphism. This writes the descent argument out instead of citing an unstated Galois descent theorem. The finite prime-power presentation of q is provided by def-weil-finite-field-q-elements in step 2.

I checked delivery-errors B–E against the files: no unsplit new nodes or unintroduced objects, exact statement citations (C4), no uncited non-elementary input (C1), no copied clause or disguised restatement, and no induction or circular premise. The only outside-unit statements used as tools are declared in split_report.tool_uses with their purpose. The inherited statement dependency list still covers the unchanged mathematical statement. Every step is below 2000 characters (785, 488, 582, 771), and the final chart computation hides no separate lemma.

Edge cases checked: the trivial group makes the unique geometric torsor point already fixed; additive groups and tori use the same equation without reductivity; noncommutative groups require exactly the displayed order. An empty Y is excluded by surjectivity. No connectedness, reducedness, finite type, or affineness of Y is assumed in the point selection or chart descent. Disconnected groups are excluded as required: a nontrivial finite-field finite etale torsor can have no rational point. No smoothness or connectedness hypothesis was silently dropped from the group.

## Unfinished work

None in the one-level split. The existing dependencies keep their current proof/queue states; this delivery makes no claim that every dependency is already formalized. Server dry run and push are the remaining delivery operations.
