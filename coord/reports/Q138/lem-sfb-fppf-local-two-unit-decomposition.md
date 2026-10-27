## Worker report

Q138 split `lem-sfb-fppf-local-two-unit-decomposition` at stage 1, without writing Lean or running a compiler. The original statement is unchanged.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-local-two-unit-decomposition.json`: split, no Mathlib match. Four steps construct a single covering scheme as an open subscheme of the affine line.
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl`: queries and results recorded by the required search command.
- `report.md`: this report.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. The smoothness, open-subscheme composition, smooth-implies-flat-and-lfp, polynomial-domain and basic-open inputs already exist in the DAG. The kernel-prime and unit-inverse calculations are explicit elementary steps, not new lemma nodes.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, two-unit decompositions, sums of two units, and fppf/unit combinations found no declaration asserting the item. Declarations about two adjunction units are unrelated.

## Sources and searches

WANTED: Brian Conrad, *Reductive group schemes*, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed p.129 after (4.3.1), local copy for this item. Read the online primary source on 2026-10-24; no literature file was downloaded or written. The cited paragraph gives a local decomposition in the context of an additional invertibility assumption on 1+uv. The item deliberately asserts a stronger avoidance fact. The four-step proof is marked agent-written and establishes that stronger fact directly, so it does not import the contextual assumption. This uses no SGA source.

I read the relevant Stacks text in `schemes.tex`, Tag 01HZ, label lemma-f-open, for openness and the invertible restriction; `morphisms.tex`, Tags 01VA/01VC, labels lemma-composition-smooth / lemma-open-immersion-smooth, and 01VE/01VF, labels lemma-smooth-locally-finite-presentation / lemma-smooth-flat; and `topologies.tex`, Tag 021L, section-fppf and definition-fppf-covering. The affine-space node identifies the local polynomial charts; its smoothness source is Algebra Tag 00T7, lemma-standard-smooth.

The latest blueprint chapter and unit, and the direct-images proof (3), were read in `literature/blueprint/latest/`. This is a low-level prerequisite along the already assigned central-extension/root-calculation chain; it changes no chapter or unit route. `tools/blueprint_refs.py ancestor` returns None for this legacy-created chain. I retained the item's existing null ancestor and exact supporting place rather than invent an ancestor. Whole-blueprint searches for “two units”, “sum of two units”, “three unit”, “decomposition u”, “affine line”, and “localization”, and DAG keyword searches, identified no blueprint statement equivalent to the item. The geometric and algebraic inputs found by those searches are reused.

For the item I ran the mandatory leanfinder, loogle, grep and leansearch commands, including two distinct semantic phrasings. All four services ran. The hits state basic-open membership, invertibility on a basic open, smoothness/flatness, and local-ring alternatives; none gives the simultaneous three-unit assertion on a covering. The required commands' exact query text and result summaries have been appended to mathlib_searches; the imported Q102 searches are preserved as history. No new nodes require additional searches. The second semantic search is not being counted as evidence that the standard smoothness lemmas are absent: those are cited through existing nodes.

## Not duplicates

No new nodes were created. The broad smoothness and basic-open results were found and reused, rather than repackaged under new names.

## Review by Q138

I checked the statement against Conrad's printed p.129 and the node's explicit strengthening: u and v are arbitrary, and 1+uv is never used as a unit. The open W is defined by the actual polynomial x(u-x)(1+xv); it is not chosen from an unproved existence claim. The proof origin identifies the extra argument as mine. No source error or statement correction is claimed.

Step 1 cites def-sbc-affine-space for the compatible polynomial-coordinate description over every affine open, lem-weil-pbc-basic-open-function for openness of D(P), and def-weil-open-immersion for its open-subscheme inclusion. I opened all three statements: the first gives the precise local charts, the second supplies the claimed open, and the third identifies its inclusion as an open immersion. These citations supply exactly the construction, without asserting smoothness from a definition alone.

Step 2 cites sbc-lem-affine-space-smooth with n=1, lem-pc-open-immersion-smooth-composition, and only the forward implication of sbc-lem-smooth-criterion. I opened each node and checked that its statement gives, respectively, smoothness of p, smoothness of pj, and flatness plus local finite presentation of pj. Their hypotheses require only schemes and the open immersion from step 1; there is no Noetherian, finite-type-over-a-field, affine-base or nonempty-base restriction. The two non-leaf smoothness nodes are declared as generic tool uses in split_report; they do not replace the unit's mathematical route.

Step 3 cites def-sbc-affine-space for p inverse U = Spec R[X], def-weil-affine-spectrum for the description of points and the contraction map, def-weil-residue-field for kappa(t), lem-weil-pbc-polynomial-ring-domain for the domain k[X], and lem-weil-pbc-basic-open-function for the nonvanishing description of D(P). I read these statements, and none is being used for a hidden surjectivity theorem. The kernel prime is explicitly verified: a product maps to zero only if a factor does, and 1 does not map to zero. Its contraction is the kernel of R to kappa(t), namely the prime of t. The three nonzero polynomial factors are checked by coefficients, so their product avoids that kernel. This is a prime of the polynomial ring above t, not a falsely assumed rational point of the affine-line fibre. The routine polynomial ring in one variable is the singleton-variable case of the cited domain statement.

Step 4 cites lem-weil-pbc-basic-open-function for the global inverse of P restricted to W and def-pc-fppf-site for the three covering conditions. Those are exactly the clauses I quote in citations.json. The individual inverses are written as products with that inverse, using only commutative-ring multiplication. Flatness, local finite presentation and surjectivity have all been established before the definition of covering is invoked. The sections a and b are global on W and satisfy the asserted equality by their definitions; no descent or gluing lemma is hidden in this step.

For the B--E checklist: no new statement-only node, duplicate, clause-restatement, missing definition or Mathlib leaf is introduced (B1--B10, D1--D4). Every non-elementary fact is supplied by an existing cited statement; the explicit kernel and inverse arguments explain the elementary steps (C1--C5 and D5). Proof dependencies are exactly the union of uses, and no dependency refers back through the root-extension chain (C6). Generic tools are declared, with no attempt to alter maintainer tool_uses (C7--C8). The longest proof step is below 1000 characters; none hides a >2000-character lemma.

I tested the relevant small cases mathematically (E1--E7). If v=0, the third factor is 1. If u=0, the first two factors are x and -x, both units on W. If 1+uv=0, no part of the construction changes. Over F2 with u=1 and v=0 the open has no F2-valued point, but the kernel construction still gives the generic point; this is precisely why choosing a residue-field element would have been invalid. Nilpotents or disconnected components in the base cause no problem, because nonvanishing is checked in each residue-field polynomial domain. For the empty base the covering condition is vacuous and all unit equations hold in the zero section ring. No characteristic, invertibility or quasi-compactness hypothesis was added. The arbitrary-base singleton family is a covering under the actual fppf definition cited, which requires locally finite presentation rather than a separate global finiteness hypothesis.

The principal correction made during self-review was to cite the basic-open-function node also in the surjectivity step, so that the passage from avoiding P to belonging to W is explicitly backed by the node's nonvanishing clause. All cited statements are recorded verbatim in citations.json. There are no unfinished mathematical clauses or requested new literature-dependent lemmas.
