# Q19 stage-1 report: lem-trf-coefficient-order-hilbert-equality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coefficient-order-hilbert-equality.json`: statement, split; six proof steps; no Mathlib match.
- `citations.json`: every cited node in every item step, with its statement copied verbatim.
- `report.md`: this report. Search results are in `searches.jsonl`.

No new DAG nodes; zero Mathlib leaves. The scratch script `write_split.py` only writes these sandbox files and is not part of the mathematical delivery.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, coefficient-order/Hilbert equality names and concepts; no project declaration states this item. Existing supported-division and coefficient-data interfaces in `Sheaf/` do not prove this equality. No compiler or Lake command was run.

## WANTED

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant, Invent. Math. 128 (1997), pp.207--302, especially (7.1)--(7.2), Theorem 7.14, Remarks 9.1 and 9.5 and the end of Theorem 9.6, for repository-local literature supporting this item. It is absent from `literature/`, but I read these passages online in the journal PDF at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf . No download was written. The proof is marked agent-written because its algebraic extension to nonclosed points and the detailed assembly are not literally a proof in the local ILO PDF.

## Source error / STATEMENT-DISPUTED

STATEMENT-DISPUTED: the imported statement omitted that the transverse variables are precisely the essential variables of the vertex monomials. This is explicit in BM (7.1), printed pp.261--262, and in the statement of the parent `lem-trf-regular-hilbert-coefficient-data`.

Counterexample to the imported version: take any characteristic-zero field, U=X=A^1_k, a=0, N={0}, and D empty, with the empty f-list. All order, division, supported-generation and block assumptions are vacuous (K_a=0, and the identity monomial family gives division). The coefficient locus is S=N, whereas the Hilbert function of X in the one retained Taylor variable is t+1 at every point of U. Thus its equality locus is all of U, which is not N on any open neighbourhood of 0. The asserted formal identity also reads 0=(Z). Requiring the Z variables to be exactly the essential variables excludes this example; in the empty case it forces zero transverse variables and N=U near a. This repairs the intended statement without changing the parent's input or any target.

There is also a typographical inconsistency in the final paragraph of BM Theorem 9.6, printed p.282: its derivative inequality is printed non-strict, while Remarks 9.5(1), Definition 7.9 and the order locus require strict inequality. I retain the item's correct strict inequality. For f=z^2+w^3, the strict coefficient ideal is (w^2); allowing derivative order 2 of w^3 would give (w), a different coherent ideal.

The imported proof was empty. No metadata, existing citations, prior searches or blueprint fields were deleted. No new source tag was invented: no single Stacks tag states this Hilbert-stratum result.

## Not duplicates

No new nodes. In particular I reused `lem-trf-formal-hilbert-stratum-minors` rather than introducing another formal determinantal comparison, and `lem-trf-implicit-taylor-coordinate-calculus` rather than duplicating coherent ideal descent. Whole-DAG keyword searches and whole-blueprint searches for Hilbert, derivative, coefficient and Hilbert Samuel stratum found no imported blueprint statement of the item. The nearest blueprint ancestor is `lem-trf-local-term-locality`; its latest proof now uses contracting correspondences. This is the already-existing historical lower resolution/local-presentation branch, and this split does not change the chapter or unit route.

## What remains unfinished

Nothing required for this stage-1 split. Its cited nodes remain the existing DAG's obligations; no Lean proof is claimed.

## Review by Q19

I read the chapter and unit records, GOAL.md, the three blueprint levels in SETUP.md, the latest ancestor statement and proof, the worker/stage-1 rules, and delivery-errors B--E in full. I read the item's complete statement and its parent's six-step assembly to identify exactly which clause the parent needs: equality of the coefficient-order and extended Hilbert-function loci. I read ILO VIII 2.3.11--2.3.13 (PDF pp.99--100, printed pp.93--94); these paragraphs only refer to resolution algorithms, so I do not treat them as a proof of this coefficient assertion. In the online BM source I checked the essential-variable convention and five conditions (7.1)--(7.2), Theorem 7.14, Remarks 9.1 and 9.5(1)--(2), and the closing paragraph of Theorem 9.6. For the algebraic descent I additionally read Stacks algebra.tex `lemma-faithfully-flat-universally-injective` (05CK), and coherent.tex `lemma-local-isomorphism` (01Y3). These support the existing calculus node's descent clauses; I do not create copies of them.

Step 1 cites `lem-trf-jet-diagram-hilbert-control` for precisely its dimension formula from the initial diagram and its local finite-value assertion. I opened and read that node's statement. It applies in characteristic zero to the smooth etale chart with coherent ideal here and explicitly retains the relative Taylor variables at nonclosed points. The step also cites `lem-trf-formal-hilbert-stratum-minors` for its finite-type compatibility and equality-locus clauses. I read that statement and all thirteen existing proof steps. The order, every-prefix division, supported-generation, invertible block Jacobian and later-block derivative hypotheses match ours at a; q may exceed Q because the theorem only uses derivative bounds through max d_i-1. The finite set of local function values supplies a finite distinguishing q.

Step 2 again uses the formal-minors theorem for JA=E, with its change of finite generators, and `lem-trf-fitting-ideal-independence-base-change` for the presentation independence of the finite quotient module. I read its statement: it states both independence of the surjection and compatibility with every ring homomorphism. The formal straightening is justified by the explicitly invertible substitution Y -> F(X+Y)-F(X) in the truncated jet algebra. It is not an assertion that straightened formal coordinates are regular functions. This also handles the zero-dimensional-fibre case separately, where the minors are oversized rather than a negative-index Fitting ideal.

Step 3 is a direct matrix and coefficient calculation, not a hidden new lemma. At the last block every Z variable is essential after the repaired hypothesis. Each selected derivative is among the generators of E; formal membership in (Z) and the invertible Jacobian give g=UZ with U invertible. Reducing low derivatives modulo (Z) gives exactly factorial times coefficient derivatives, with the strict bound |delta|+|gamma|<d_i. Conversely each prescribed coefficient derivative is obtained this way. This establishes the equality of ideals, not merely equality of their radicals or zero sets. Its 769-character argument is elementary and creates no clause-restatement node.

Step 4 cites `lem-trf-etale-coordinate-derivations-jacobian` for regularity and Taylor compatibility of coefficient derivatives, and `lem-trf-implicit-taylor-coordinate-calculus` for the graph ideal, restriction identity, faithful-flat Taylor map at arbitrary points, contraction of equal extended ideals and spreading equality of coherent stalk ideals. I read both full statements and the latter node's existing proof. It states each of these conclusions explicitly, so I do not borrow a fact that occurs only in its proof. The finite low coefficient/derivative index sets ensure coherence and ensure only one shrinking is used. Inverse image under O_U -> O_N is the intended ideal; adjoining equations to chosen lifts is independent of the lifts.

Step 5 cites the actual statement of `lem-trf-taylor-normal-cone-splitting`, not merely the definition of order. I checked that it covers a possibly nonclosed point in a smooth characteristic-zero chart, and explicitly identifies the local associated graded ring with a polynomial ring in independent linear Taylor forms. Applied with I=(c), this makes the first nonzero ordinary local initial form remain nonzero in the full Taylor ring. Thus ordinary local order and full Taylor order agree on regular coefficient germs, although local completion itself has fewer parameters at a nonclosed point. The step proves the two implications explicitly. The coordinate-derivations node supplies the Taylor derivative formula, and characteristic zero supplies the invertible factorial. Consequently the zero locus of C really is S at every point, not just at closed points.

Step 6 only assembles preceding equalities and checks degenerate cases. Empty vertices require N=U after repair, supported generation forces K_a=0 and coherent descent kills the finite minors ideal near a. Degree-zero vertices cannot occur at a point of X, since their generator would be a unit in its proper Taylor ideal. Ambient dimension zero and zero coefficients cause no exception.

I tested the concrete hypersurface f=z^2+w^3 with N=(z=0), D generated by z^2 and Q>=1: E=(z,w^2), the coefficient derivative ideal is (w^2), and the equality locus is its support. For X=(z^d) in A^2 with N=(z), the ideals are (z) and the coefficient ideal is zero; the locus is N. The nonclosed generic point of N has local coefficient order zero for nonzero rational coefficients, consistently with their nonzero constant Taylor term. The empty case above exposed and repaired the omitted essential-variable condition. I checked no step exceeds 2000 characters, no step uses a node dependent on this item, and all cited statements are in the same unit. No new nodes or off-unit generic-tool declarations are needed.

I read the actual search hits from both phrasings, not just the hit counts: univariate Weierstrass division, polynomial leading-coefficient ideals, homogeneous-ideal extensionality and submersive-presentation Jacobian identities do not state this coefficient-order/Hilbert-stratum theorem. All newly recorded searches were run through the required msearch command; the inherited 2026-10-22 searches remain intact. The citations JSON has one verbatim statement quote for every citation in every step.
