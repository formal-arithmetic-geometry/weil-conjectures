1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-degree-zero-fibre-criterion.json`: split item with four proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-cut-complex-degree-zero.json`: statement-only child, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-finite-locally-free-residue-isomorphism.json`: statement-only child, no Mathlib match.
- `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The item has no sorry-free Lean declaration. I checked the source proof of Stacks Tag 0E62 (`literature/stacks-project/perfect.tex`, label `lemma-proper-flat-h0`) and retained its hypotheses and conclusions. The proof is split at the three non-elementary inputs actually used there: the local cut-complex lemma (Tag 0A1U), flat perfect degree-zero cohomology being finite locally free (the middle paragraph of Tag 0E62), and the residue-field criterion for finite locally free modules (Tag 00O0). No existing DAG node states any of these in the required scheme-level form; searches for the tags and key phrases were made across `dag/nodes` and the blueprint. The child nodes are statement-only as required.

## Not duplicates

lem-sc-perfect-cut-complex-degree-zero vs lem-sc-perfect-h0-locally-closed: the new node gives a local direct-sum splitting from a surjective fibre map, while the existing node constructs a locally closed rank locus.
lem-sc-finite-locally-free-residue-isomorphism vs lem-pc-hilb-representable: the new node states the residue-field isomorphism criterion for finite locally free modules, while the existing node is Hilbert-scheme representability and only lists Tag 00O0 as an external reference.
lem-sc-finite-locally-free-residue-isomorphism vs lem-pc-perfect-summand: the new node detects an isomorphism from all residue fibres, while the existing node proves perfectness of a direct summand.

## Review by J1

I read Tag 0E62 line by line, including the preceding perfect-direct-image argument that supplies nonnegative Tor-amplitude, and checked each item hypothesis against the copied statement. Step 1 cites the existing Tor-amplitude testing node for the passage from residue-field vanishing to nonnegative amplitude. Step 2 cites the new cut-complex statement, whose conclusion is exactly the local splitting and whose hypothesis is the surjectivity obtained from the assumed fibre isomorphism. Step 3 uses the existing affine bounded-projective model and spells out the short finite-flat calculation as elementary. Step 4 cites the new residue-field criterion and checks that both source and target are finite locally free before applying it. The citation quotes are verbatim substrings of the cited statements.

I tested the statements on the identity complex O_S, on S=Spec(k) with K=k in degree zero, and on a split complex O_S\\oplus P with P concentrated in positive degrees. The Mathlib searches for the item and all three children were run with LeanFinder, Loogle, Mathlib grep, and LeanSearch; LeanSearch was unavailable and is recorded as such. The searches found only generic complex truncation and module free-locus results, so none of the scheme-level children is a Mathlib leaf. The source's local finite-projective and residue-field arguments are represented by the new statement-only children rather than hidden in uncited steps.

5. What remains: the second worker should re-read the split and run the dry run.

## Second reading by J1

- Item statement: checked against Stacks `perfect.tex`, Tag 0E62, label `lemma-proper-flat-h0`; the fibre hypotheses and both conclusions agree with the source, with the `D_{\\mathrm{QCoh}}` context made explicit.
- Step 1: checked against Tag 0E62's first Tor-amplitude reduction and `[lem-pc-tor-amplitude-qcoh-test]`; the cited statement supplies exactly the needed implication.
- Step 2: checked against Tag 0E62 and Tag 0A1U; the cut argument requires nonnegative Tor-amplitude, which the repaired cited statement now assumes.
- Step 3: checked against Tag 0E62's flat-perfect paragraph, Tag 08EB, and Tag 0658; this finite-projective calculation is non-elementary and is now explicitly cited.
- Step 4: checked against Tag 0E62's final paragraph and Tag 00O0; both source and target are finite locally free before applying the residue-field criterion.
- `lem-sc-perfect-cut-complex-degree-zero`: checked against Tag 0A1U and tested on `O`, a field, and `O[-1] \\oplus O`; the former bounded-above statement was false, so `[0,\\infty)` was added.
- `lem-sc-finite-locally-free-residue-isomorphism`: checked against Tag 00O0, including zero-module and field cases; correct and not duplicated.
- Existing `lem-weil-pbc-finitely-presented-flat-module-projective`: checked against Tag 00NX; it states the exact finitely-presented-flat implication used after the bounded finite-projective model, so the proposed duplicate child was removed.

Changes made: corrected the cut node's false hypothesis; made the `D_{\\mathrm{QCoh}}` context explicit; removed the duplicate flat-perfect child and cited the existing finitely-presented-flat module node; changed Step 3 from an unjustified elementary claim to a cited non-elementary step; and updated `citations.json` with verbatim repaired statements.
