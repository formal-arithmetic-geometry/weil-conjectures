## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-affinoid-spectral-equation.json`: item, split into eight proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-tate-torsionfree-fibre-polynomial.json`: new statement-only node, unsplit; no Mathlib match. It states the principal evaluation kernel and maximal-fibre formula over a Tate algebra for a finite torsion-free extension, Bosch 1.4 Lemma 12(i)-(ii).
- `citations.json`: one exact statement quotation per step/node pair (11 pairs).

## Attachments

None. Searches of the live `lean/WeilConjectures/` and `lean/Sheaf/` for the item tag and the affinoid/Tate concepts found no declaration asserting the item or the new node. No Lean files were written, and no compiler or Lake command was run.

## Wanted literature

WANTED: Siegfried Bosch, Lectures on Formal and Rigid Geometry, April 2008, Section 1.4 Lemmas 11–13, printed pp.25–28, for lem-trf-finite-affinoid-spectral-equation and lem-trf-tate-torsionfree-fibre-polynomial. The archival path `literature/bosch-formal-rigid-geometry-2008.pdf` is absent in this checkout. I read the primary PDF at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, especially PDF pages 26–29, through its text view. I did not download or write literature; the item's proof_origin is agent as required for this archival absence.

## What was wrong or incomplete

The imported item had no proof. Its statement is faithful to Bosch 1.4 Lemma 13 and is unchanged. In particular a finite map need not be injective and neither algebra need be reduced. The normalization must be of the image B/ker(phi), lifted through a presentation of B, rather than an assumed inclusion of B in A. After minimal-prime reduction the product equation is initially only nilpotent on a, and requires a positive power. I made both arguments explicit. The zero-seminorm case uses pointwise root bounds and coefficient convolution, with no cancellation of a zero real number.

The current latest blueprint ancestor `lem-trf-local-term-locality` has the Varshavsky contracting-correspondence proof; its current unit differs from the older recorded unit text. The created.item chain already places this item in a historical analytic supporting branch. I preserve that provenance, do not modify the chapter/unit, and do not claim that analytic normalization replaces a step of the current contracting proof. The blueprint from.place and split_report say this explicitly.

## What could not be finished

Nothing in the requested one-level split remains. The new Tate lemma deliberately has no proof or proof_deps and joins the unsplit queue. The archival PDF still needs to be obtained by the project.

## Not duplicates

lem-trf-tate-torsionfree-fibre-polynomial vs lem-trf-finite-affinoid-spectral-equation: the new node gives a principal evaluation kernel and a formula on every maximal fibre for a finite torsion-free extension of a Tate algebra. The item treats an arbitrary finite map of possibly nonreduced affinoid algebras and needs lifted normalization, coefficient transport through a possibly noninjective B, minimal-prime reduction, and a nilpotent power. Its proof carries these arguments, rather than applying an affinoid-equation restatement.

lem-trf-tate-torsionfree-fibre-polynomial vs lem-trf-tate-normalization-lift: normalization constructs an embedded Tate algebra over which a quotient is finite; it supplies no evaluation kernel or fibre formula. It is reused, not duplicated.

lem-trf-tate-torsionfree-fibre-polynomial vs lem-trf-affinoid-supremum-seminorm-calculus: calculus defines the maximal-ideal seminorm and gives boundedness, powers, and contraction; it supplies no minimal polynomial or optimal coefficient equality. It is reused, not duplicated.

lem-trf-tate-torsionfree-fibre-polynomial vs lem-trf-affinoid-polynomial-closed-point-comparison: the existing node gives Noetherianity and completed local-ring comparison for polynomial ideals extended to a Tate algebra. It does not give an arbitrary finite extension's evaluation kernel or maximal-fibre formula. Its J=0 clause is reused to obtain Noetherianity of a Tate algebra; therefore the candidate new affinoid-Noetherian node was not created.

DAG/source searches included affinoid, minimal polynomial, spectral coefficient, torsion-free Tate, and Bosch Lemma 12; whole-blueprint searches included affinoid (zero matches), torsion-free (zero), minimal polynomial (three unrelated field/root definitions), and spectral. None states the new lemma. No Stacks tag is attached to the new analytic node, so there are no same-tag duplicate pairs. Algebraic Stacks facts are cited through existing nodes instead.

## Mathlib searches and candidates read

All fresh searches were run through the required msearch.py command; searches.jsonl records their exact tools and queries. The new node records the five searches concerning its own statement (two LeanFinder phrasings, Loogle spectralValue, grep, and LeanSearch). I read the field hypotheses and proofs of norm_root_le_spectralValue and max_norm_root_eq_spectralValue in Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean, lines 240–330. They are field root estimates, not the principal-kernel and affinoid-fibre theorem. LeanSearch's minpoly and IsAdjoinRootMonic hits concern algebraic minimal polynomials, without the fibre formula. The grep found no TateAlgebra or affinoid implementation. Generic integral-equation and ideal-power coefficient hits for the item do not give optimal spectral coefficient bounds over B. Additional searches about affinoid Noetherianity found only formal power series, polynomials and quotient preservation; no new node was ultimately needed because the existing analytic comparison suffices.

## Review by NG

I read Bosch's Lemma 13 in full against its preceding Lemmas 11 and 12, including the proof of the fibre formula: passage to the singly generated subalgebra, the polynomial quotient over the finite residue field, and the root calculation. I also read the existing normalization and supremum-calculus statements, and the J=0 clause of the analytic comparison statement. For the algebraic reduction I read Stacks algebra.tex lemma-Noetherian-irreducible-components (00FR) and lemma-Zariski-topology (00E0), parts (4) and (7), and opened the three cited DAG leaves. Their statements give finite minimal primes, a minimal prime below each prime, and the radical/intersection equality respectively. No conclusion is borrowed from another node's proof.

Step 1 cites the calculus node for the actual residue-field values, finite supremum, and contraction. Strong triangle and product inequalities follow directly at each residue field. The root contradiction is written pointwise, so it does not assume multiplicativity of rho on A or B. Step 2 proves convolution bounds by its finite coefficient sum; it needs only step 1 and has no hidden citation. Both are elementary calculations, not new lemma nodes.

Step 3 cites lifted normalization exactly with I=ker(phi pi), not ker pi. Its source Tate algebra and all quotients are over the given complete nontrivially valued K, and I is proper. The finite spanning-set multiplication and the domain argument establish finiteness and torsion-freeness needed for the new theorem; no unproved flatness assertion occurs. Step 4 cites the new node's actual kernel polynomial and every-fibre equality. The calculus node gives finite residue fields, allowing the contraction-is-maximal argument. Taking suprema is explained in both directions without assuming maximum attainment. Step 5 uses only coefficient transport and the calculus node's contraction, combined with the proved root bound. In particular it does not identify rho on B with rho on its quotient image.

Step 6 uses precisely Noetherianity from the analytic comparison at J=0, applied to a fresh Tate presentation of A. I corrected the notation here so it cannot be confused with the presentation of B in step 3. Quotient Noetherianity is proved by inverse-image ideals, after which the existing 00FR leaf applies. The two 00E0 leaves establish the coverage by minimal primes and nonemptiness. Maximal-ideal correspondence for a quotient is direct: inverse image and quotient are inverse ideal operations preserving maximality and their residue fields are identical. Quotients by prime ideals are nonzero domains; images of the original B-spanning set prove their finiteness. Step 7 reuses the already-proved domain case, rather than creating a node for that clause. One factor vanishes modulo each minimal prime, and the cited prime-containment and radical statements imply the evaluation of the product is nilpotent. Step 8 uses only the two elementary bounds established in steps 1 and 2.

I checked d=0 (the Tate algebra is K), a=0 (a positive-degree polynomial Z suffices), nilpotent a in K[epsilon]/(epsilon^2) (Z^2 and all coefficients of seminorm zero), a product of two domains (two components and the product of their equations), a noninjective map such as K<T> to K by T=0, and the rank-one free torsion-free example C=T[epsilon]/(epsilon^2). The last also checks that the new lemma must allow nonreduced C and repeated roots. A zero algebra is excluded where needed in both statements; a zero-dimensional normalization is allowed. Every proof step has fewer than 2000 characters, so none triggers the long-step review. The single new statement has all its objects and hypotheses introduced, its notions either defined inline or cited, and no proof sketch. No SGA source is used. A transitive dependency read found no path from the reused analytic nodes to this item, so these citations introduce no cycle.
