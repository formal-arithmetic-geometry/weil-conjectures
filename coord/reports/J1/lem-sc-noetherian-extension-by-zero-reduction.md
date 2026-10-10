1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-noetherian-extension-by-zero-reduction.json`: item, split; Mathlib searches found no exact match.
- `dag/nodes/sec-curve-estimates/lem-sc-topological-filtered-cohomology.json`: statement-only dependency, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-constant-subsheaf-finite-filtration.json`: statement-only dependency, no Mathlib match.

2. Attachments: none.

3. WANTED: none; the Stacks pages for 01FF, 0A38, and 02UX were read online, while the repository copy of `cohomology.tex` is absent.

4. The imported item already had the corrected `j_! Z_U` statement but no proof. I followed 02UX: finite generated subsheaves and filtered-colimit continuity (01FF), induction on the number of generators, the one-section quotient by extension by zero, and the finite filtration of its kernel (0A38). The two non-elementary results absent from the DAG are the two new statement-only nodes. No Lean declaration with the item tag or exact statement was found in slopmaster2.

## Review by J1

I checked the item statement against Stacks 02UX line by line, including quasi-compactness, the quasi-compact-open basis, quasi-compact intersections, and the bound `p>d`. I read the exact statements of every cited node: `def-sc-topological-abelian-cohomology` supplies the long exact sequence; the filtered-colimit node supplies the canonical isomorphism for all quasi-compact opens; and the finite-filtration node supplies the successive short exact sequences of extension-by-zero constant sheaves. Steps 1 and 5 use only the filtered-colimit statement plus the stalk argument; Step 2 is the elementary induction on generators using the cited long exact sequence; Step 3 records the one-section quotient and kernel reduction from 02UX; Step 4 applies the finite filtration and the hypothesis to each quotient. I tested the reduction on the zero sheaf, a one-section sheaf, and a finite filtration of length one. The only correction made was preserving the imported `j_! Z_U` notation and adding the complete proof and dependencies.

5. Unfinished: the new dependency nodes are intentionally statement-only for the next stage.

## Not duplicates

lem-sc-topological-filtered-cohomology vs lem-weil-pbc-scheme-modules-coproduct-finite-subsums: the existing node concerns finite subcoproducts of O_X-modules on a scheme, while the new node is filtered-colimit continuity of abelian sheaf cohomology on any topological space.
lem-sc-topological-filtered-cohomology vs lem-weil-pbc-module-cech-vanishing-basis: the existing node is a Cech vanishing criterion for O_X-modules on a scheme; the new node asserts cohomology-colimit isomorphisms for arbitrary abelian sheaves.
lem-sc-topological-filtered-cohomology vs lem-weil-pbc-qcqs-cohomology-direct-sum: the existing node is direct sums of O_X-modules on qcqs schemes; the new node treats arbitrary filtered systems of abelian sheaves on topological spaces.
lem-sc-topological-filtered-cohomology vs lem-weil-pbc-qs-scheme-cohomology-directed-colimit: the existing node assumes a scheme and O_X-module system, whereas the new statement is for topological spaces and abelian sheaves.
lem-sc-topological-filtered-cohomology vs lem-weil-pbc-scheme-modules-functorial-injective-embeddings: the existing node constructs injective embeddings of scheme modules and does not state cohomology continuity.

## Second reading by J1

- Item statement: checked against Stacks tag 02UX, label `cohomology-lemma-vanishing-generated-one-section`, and the definitions of constant sheaf and topological extension by zero; verdict: hypotheses and conclusion match, with extension by zero made explicit.
- Step 1: checked against tags 01FF and 02UX and the stalk generation argument; verdict: the finite-generation colimit identification is written out and marked elementary, and the filtered-cohomology citation applies with U=X.
- Step 2: checked against the 02UX induction paragraph and the long exact sequence statement; verdict: the induction base, step, and one-generator reduction are explicit.
- Step 3: checked against the 02UX kernel reduction and the exact filtered-colimit theorem for abelian sheaves; verdict: the quotient system and its colimit are stated, and the exactness dependency is cited.
- Step 4: checked against tag 0A38, label `cohomology-lemma-subsheaf-of-constant-sheaf`, and the long exact sequence; verdict: the finite-filtration induction uses correctly typed topological extension-by-zero sheaves.
- Step 5: checked against the conclusion of 02UX and Step 1; verdict: passage from finitely generated subsheaves to the original sheaf is valid.
- `lem-sc-topological-filtered-cohomology`: checked against tag 01FF, label `cohomology-lemma-quasi-separated-cohomology-colimit`, and all recorded searches; verdict: statement-only dependency is self-contained and not duplicated.
- `lem-sc-constant-subsheaf-finite-filtration`: checked against tag 0A38 and the existing topological extension-by-zero node; verdict: TeX, notation, and dependency now describe abelian sheaves on a topological space rather than etale sheaves on schemes.

Changes made: corrected the item source label and `created.item`; replaced the etale extension-by-zero dependency with `lem-sc-topological-extension-by-zero-stalks`; made Step 1's stalk argument explicit; expanded the generator induction; repaired the filtered quotient reduction and cited `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`; corrected the filtration node's TeX and source label; and synchronized `citations.json` with the repaired statements. Edge cases checked: the zero sheaf, one generator, empty open, and a filtration of length one. Dry run passed at commit `d3796709`.
