# Q34 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-point-power-section-bound.json`: statement item, split into six proof steps, unchanged statement; not a Mathlib leaf.
- `citations.json`: one verbatim statement quote for each use in each step.
- `report.md`: this report.

No new nodes; no new Mathlib leaves; no unit record changed. Only sandbox files were written, and no compiler, Lake or git command was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, point ideals, point powers and linear series found no declaration stating this estimate. Curve Picard restriction lemmas and elliptic-curve ideals do not give the arbitrary embedded-curve estimate.

## WANTED

WANTED: D. Gieseker, Lectures on Moduli of Curves, Proposition 1.0.3, printed pp.33--34, for lem-sfb-projective-point-power-section-bound. The source PDF named in the node is absent locally. I read the online transcription at https://doczz.net/doc/7664568/lectures-on-moduli-of-curves---school-of-mathematics--tifr (the point-ideal observations (i)--(iv) on printed pp.33--34). The proof delivered here is explicitly agent-written, using the locally present Stacks sources and existing DAG statements, rather than attributing the explicit interpolation argument to the book.

## Findings and corrections

The item is true as stated; no STATEMENT-DISPUTED correction is needed. The previous proof was empty. The book estimate uses asymptotic vanishing with small-weight exceptions. Here the embedding itself supplies a direct jet interpolation calculation for all 1 <= t <= m, so the final additive constant only has to dominate the Hilbert polynomial constant. There is no passage to a normalization and no smoothness assumption at the point. The original statement, source, created fields, unit, and blueprint ancestry are preserved. Added the definition dependencies for algebraic closedness and irreducible components, both notions already present in the statement.

The ancestor command returns None. This is inherited through a created.item chain ending in a stage-3 module name; the prior accepted parent report identifies the same issue. I preserved from.node=null and the complete from.place/via rather than inventing ancestry. I read the current latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof: the current proof is shorter and this supporting algebraic estimate serves the already established alteration/moduli prerequisite below its proper-image input. No chapter or unit route is replaced.

## Searches and reuse

Read the whole-DAG statements selected by title/concept searches, including the linear-series degree bound (smooth curve of genus >=2, hence inapplicable here), the normalization-section-defect node (generically reduced and connected, hence insufficient), the Hilbert dimension comparison, the actual quotient tail node, Nakayama nodes and projective charts. Whole-blueprint searches: linear series, Hilbert polynomial, jet, point ideal. Jet and point ideal returned zero; the Hilbert hits are numerical polynomial/degree definitions and results, not this estimate. Searches of the latest blueprint found the renamed direct-images proof and it was read.

Ran and read msearch LeanFinder twice with different phrasings, Loogle twice, grep twice and LeanSearch once. The first semantic results are Weierstrass coordinate ideals, the second division-polynomial degrees. Loogle jet has no hits; Loogle section gives structure-sheaf sections and flat pushout section maps. Grep finds Proj ideal powers and the IdealSheaf power definition, then no jet/point-power bound. LeanSearch gives Proj section operations and vanishing ideals. None states this section-dimension estimate. Exact queries and actual log summaries are appended to the item; the inherited earlier searches are retained. No new lemma is needed: the local calculations are explicitly written in the item's steps and the non-elementary inputs already have nodes.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to justify. The coordinate-tail isomorphism, projective charts, point-residue-field theorem, sobriety and Nakayama are reused directly.

## Review by Q34

I read delivery-errors B--E in full, the worker brief, stage-1 instructions, the three blueprint levels in SETUP and GOAL. I checked the item against the Gieseker online point-ideal observations and checked its local argument against Stacks coherent.tex Tag 0AG7 (lemma-recover-tail-graded-module), algebra.tex Tag 00DV (lemma-NAK), and schemes.tex Tags 01IN (lemma-closed-subspace-scheme) and 01IS (lemma-scheme-sober). The quotient-tail and ambient-twist statements were read in the DAG, not inferred from their proofs. No new node needs a source review.

Step 1 uses the actual homogeneous vanishing ideal node, the coordinate predicate definition, the coordinate-quotient section-polynomial tail node and the twist definition. The first identifies the *given* embedding with Proj of its quotient; the predicate really uses the same vanishing subspace, since that subspace is already linear. The tail node explicitly gives a finite-dimensional coordinate piece, the canonical section isomorphism and the same ambient pullback twist. Thus the eventual equality is for the coordinate polynomial in the hypothesis, not a different Euler polynomial. The bound m0 is chosen once, before t.

Step 2 uses the projective-space standard-charts statement (its cover, trivialization and polynomial-coordinate clauses), the closed-immersion affine-quotient equivalence, the closed-point residue-field statement, the prime-localization definition, and the ideal-sheaf/power definitions. These really give A as a quotient of a finite polynomial ring, k(P)=k, and the maximal ideal stalks. The residue-field theorem needs local finite type only: every chart here is explicitly a finite polynomial quotient. The centered variables generate the point ideal by subtracting polynomial constant terms. The standard-charts citation is a generic geometric tool from another unit, declared in split_report.tool_uses; it does not replace a step of the parent unit route.

Step 3 is the explicit finite geometric-series calculation, followed by polynomial truncation and homogenization. The only external definition cited is the twist transition rule, which makes the homogeneous formula a global section with the asserted local value. It does not require a general jet-surjectivity theorem. The inequality |alpha|<t<=m ensures the homogenizing exponent is nonnegative. For every localized denominator the residue b is nonzero, which is exactly what makes the inverse formula valid. No uniform Serre vanishing in the moving ideal I^t is assumed. This step is elementary: all of the algebraic identity and the section formula are displayed.

Step 4 uses sobriety only for existence of the generic point of the positive-dimensional component through P, and Nakayama only for the finitely generated R-module m^j. The prime q lies strictly below the point maximal ideal: the component is one-dimensional, so its generic point is not this closed point. All generalizations of P lie in its chosen chart. The argument with a in n minus q proves every power m^j is nonzero even with nilpotents and embedded primes. Finite generation needs no unstated Noetherian theorem: m is generated by the finite coordinate family, hence its powers by their products. Nakayama applies because m is the maximal ideal of the local ring, hence its Jacobson radical. Each nonzero filtration factor is a subquotient of the already finite-dimensional jet space, so dimension additivity gives the lower bound t.

Step 5 uses exactly the cited ideal and power definitions for its germwise kernel computation. Tensoring an ideal inclusion by a line bundle is locally the original inclusion times a free basis; no general tensor-flatness theorem is hidden. Away from the reduced point the ideal is the unit ideal, while at the point the germ condition is precisely reduction modulo m^t. Membership in a sheaf submodule is local, and unique local lifts glue, so no unstated exact global-sections theorem is required. Finite-dimensional rank-nullity then subtracts the jet dimension. Step 6 is scalar arithmetic and the separate t=0 case; K is chosen as an integer at least both 1 and c. All proof steps are under 2000 characters.

Small cases checked: a projective line gives h0(I_P^t(m))=m-t+1 (including t=m and t=0); a disconnected union with a finite point adds a constant but leaves the local calculation intact; a multiple line and a curve with an embedded point still have a strictly smaller prime under the point maximal ideal, so the nonzero-power argument survives. A solely isolated zero-dimensional point would fail the strict-prime argument and could not satisfy a uniform loss t, precisely why the statement assumes a one-dimensional component through P. At a node or cusp the jet length can be greater than t, which only improves the inequality. The empty case is excluded by the specified point. The ambient projective dimension zero admits no such component, so that case is vacuous.

I verified every use against the current statement and generated one verbatim quote per pair in citations.json. No cited node is used for a claim only in its proof. No new node is elementary, a duplicate, or a clause moved out of the item, because no new nodes are created. No long step hides a lemma, no SGA source is used, and the route remains the existing supporting estimate. There was no previous attempt or report in the sandbox to discard. Required dry-run and delivery follow this review.

## Unfinished work

None in this one-level split. The already existing dependency nodes retain their own statuses. The missing local Gieseker PDF is reported above; all mathematical inputs to this agent proof are present as cited existing statements and local Stacks sources.
