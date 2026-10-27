# Stage-1 delivery: lem-sfb-bounded-hilbert-grassmann-chart

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-hilbert-grassmann-chart.json`: item, split into eight steps. No statement change. The recorded searches find module Grassmannians and individual Proj charts, not this representing scheme and its inverse family correspondence.
- `citations.json`: 26 entries, one for every node cited by every proof step; each quote is copied verbatim from that node's statement.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log. `write_split.py` is a sandbox-only construction script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the exact blueprint tag and Hilbert/Grassmannian terminology in `lean/WeilConjectures/`, then inspected `AlgebraicGeometry/Hilbert/Representability.lean`. Its representability theorem concerns finite locally free subschemes of fixed degree. It does not give arbitrary projective subschemes of fixed Hilbert polynomial or this degree-m quotient chart. No exact attachment was found.

## WANTED

WANTED: Grothendieck, Bourbaki Expose 221, *Techniques de construction et theoremes d'existence en geometrie algebrique IV: les schemas de Hilbert*, Lemmas 3.3--3.4, printed pp.261--264, archival local PDF at `literature/grothendieck-bourbaki-221-hilbert-schemes.pdf`, for lem-sfb-bounded-hilbert-grassmann-chart. The primary Numdam PDF https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf was read online; no literature file was downloaded or repository file edited. The proof is marked agent-written as required for the missing local document.

## Problems found and repaired

The item was statement-only, without a proof. Its statement already assumes a uniform bound for every test scheme, including generation and arbitrary base change. I retained that statement exactly and used those assumptions explicitly rather than re-proving or weakening them.

The apparent issue of degree-zero equations from a nonflat E is handled by applying the rank-stratum theorem with the polynomial algebra as the algebra and B as its cyclic graded module. Applying it with B itself as algebra would incorrectly require B_0 = O_G. The flat-Proj theorem allows degree-zero equations, so its application is valid. I use unrestricted relative-Proj base change only via the separately named arbitrary-base-change lemma; the functoriality node's own base-change clause assumes flatness.

The two inverse assertions are proved inside the item. No new node restates either clause. In particular Step 6 compares the actual sheaf ideals using the assumed surjective evaluation map, and Step 7 proves an isomorphism of quotient maps, not equality of their ranks alone. I found no false imported statement requiring a STATEMENT-DISPUTED correction.

## Unfinished work

None in this one-level split. Existing dependency nodes remain the project's responsibility; this delivery does not claim their Lean proofs are finished. No Lean file, compiler, Lake, repository git command, or local server-only checker was used.

## Not duplicates

No new nodes were created. Whole-DAG keyword searches and whole-blueprint `blueprint_refs.py search graded` and `search Hilbert` identified the existing graded-tail rank and flat-Proj statements, which are cited directly. The ancestor command reports `blueprint.from.node = None`; the inherited item provenance has that value, and its precise Hilbert-construction place and via chain are preserved. The blueprint Hilbert-of-points results do not state this fixed-polynomial Grassmannian chart.

## Review by Q11

I read the complete delivery-errors sections B--E (both copies), the stage-1 brief, worker role, GOAL, the three SETUP levels and tool-lemma rule, the chapter record and the assigned unit record. This is a prerequisite below the existing Hilbert-construction route, and does not alter the chapter or unit statements. I read the primary Expose 221 PDF, especially the degree-m quotient construction before Lemma 3.3, its conditions (i)--(ii), the surjection between equal-rank locally free modules, and Lemma 3.4's universal graded rank stratum. The original simplifies test schemes to locally Noetherian ones. The present proof supplies its extra arbitrary-test-scheme verification from the item's stronger uniform hypotheses and existing arbitrary-base-change interfaces. I also read the local Stacks sources constructions.tex (01M7, 07ZK, 01O3), morphisms.tex (01T6), and algebra.tex (00FN). No SGA source is used.

For Step 1 I opened the Grassmannian statement: it supplies H-projectivity for all ranks, including endpoints. The projective-implies-proper statement and properness definition supply finite type, and the finite-type-over-Noetherian statement supplies exactly Noetherianity of G. The affine-open and finite-type-algebra Noetherian statements justify Noetherian polynomial charts. The quasi-coherent image/cokernel node supplies degreewise images and quotients on affine opens. The remaining local splitting and homogeneous-generator arguments are written explicitly. For Step 2 I read the whole graded-tail-rank-stratum statement: it permits any finitely generated graded module over a degree-one generated algebra with degree-zero piece O_G, gives a finite-type immersion, and quantifies over arbitrary T. I checked every one of these hypotheses, using the polynomial algebra rather than its quotient.

For Step 3 I read the whole flat-graded-tail-Proj statement: it allows a homogeneous ideal with degree-zero equations, requires only the parameter base to be locally Noetherian, gives flatness and finite presentation, and identifies pulled-back equations and embeddings. The base Y is Noetherian by the already cited finite-type theorem. I opened the relative-Proj functoriality statement for its surjective-map closed immersion, and the separate arbitrary-base-change statement to identify E_Y. No flatness of E was inferred. For Step 4 I read the flatness-base-change statement, clause (3) of qcqs-morphism-permanence (explicitly including finite presentation), and the fibre-polynomial-locality statement (explicitly including arbitrary pullback). These supply precisely the properties asserted on every test scheme. Module pullback supplies the tensor definition; the displayed quotient identity is checked by its algebra universal property, so no injection of a tensor-pulled ideal is presumed.

For Step 5 I reopened the Grassmannian's quotient-functor statement, which gives the unique map for the actual surjection onto q_*O_Z(m). The equality (J_T)_d = K_d is proved by both inclusions: generation gives one and vanishing of all equations gives the other. Every rank, multiplication and restriction-exactness assertion here is a hypothesis of the item. For Step 6 I opened the standard-open statement and the graded-Proj quotient/twist-comparison statement, which states both the quotient-chart ring map and its canonical polynomial-section formula. I checked the evaluation image against these chart equations; the item's assumed evaluation surjectivity makes the image exactly the existing sheaf ideal of Z. This proves equality of embedded closed subschemes, including nonreduced schemes, without identifying them merely from their points or presuming saturation.

For Step 7 the same graded quotient/twist statement makes the equations vanish as sections, giving the factored restriction map. The uniform bound gives its target rank and surjectivity. A surjective matrix between equal finite ranks is invertible locally: its reduction over the residue field has nonzero determinant, and the cited adjugate-identity statement gives the inverse at the stalk. These local inverses glue uniquely. The Grassmannian universal property and unique factorization through the rank stratum then recover the original map. Step 8 uses the Grassmannian's stated arbitrary-base-change compatibility, the uniform bound's base-change assumption, and the flat-Proj statement's embedded coefficient-pullback clause to write both naturality identities.

I checked the edge cases n=0, r=0, r=N, P=0, the empty base/test scheme, nonreduced test schemes, and non-Noetherian test schemes. The Grassmannian endpoint clauses handle r=0 and r=N. Zero rank does not obstruct the square-matrix argument. For P=0, a tail of rank zero gives the empty Proj, and the assumed bound still yields the prescribed zero quotient. Degree-zero equations can force empty parameter fibres and are allowed throughout. No simultaneous choice of local frames for infinitely many degrees is made. The degreewise arguments take one d at a time. Equations use images after tensoring; no test-base Noetherianity, flatness or reducedness is introduced. All eight steps are below 2000 characters and none hides a general lemma requiring a new node. The generic tools filed in other units are declared individually in split_report.tool_uses; none replaces a unit proof step. I verified each citations.json quote directly against the current node statement.

The server review_split check passed with zero new nodes before the final dry run.
