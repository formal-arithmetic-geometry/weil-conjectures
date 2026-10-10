# Stage 1 report: pqf-lem-finite-type-algebra-finite-spectrum

## Files written

- `dag/nodes/sec-abelian-varieties/pqf-lem-finite-type-algebra-finite-spectrum.json`: split item.
- `dag/nodes/sec-abelian-varieties/lem-pqf-finite-spectrum-maximal-primes.json`: statement-only unsplit child; Mathlib searches found no exact declaration.
- `citations.json`: verbatim citations for the two non-elementary proof steps.

## Attachments

None.

## WANTED

None.

## Not duplicates

lem-pqf-finite-spectrum-maximal-primes vs pqf-lem-finite-type-algebra-finite-spectrum: the new node states only the implication from finite prime spectrum to maximality of every prime, while the item also concludes finite-dimensionality and discreteness.
lem-pqf-finite-spectrum-maximal-primes vs lem-weil-pbc-finite-type-algebra-dim-zero-finite: the new node proves the converse direction (finite spectrum implies dimension zero), while the existing node assumes dimension zero/every prime maximal and concludes finite-dimensionality.

## Review by C1

I read the item's imported statement and its source reference to Stacks Lemma 0ALW, and searched the slopmaster2 WeilConjectures tree for the blueprint tag and relevant finite-spectrum declarations; no sorry-free declaration states this item. I also read the existing node `lem-weil-pbc-finite-type-algebra-dim-zero-finite`, whose statement exactly supplies finite-dimensionality for a finite-type field algebra in which every prime is maximal. The new child records the other 0ALW implication, from finite prime spectrum to maximality of every prime, with all objects and the zero-ring case stated explicitly.

Step 1 uses the new child's exact conclusion, so its cited statement says precisely what is needed. Step 2 uses the existing Mathlib-backed node with the field, finite-type, and maximal-prime hypotheses verified from the item and step 1. Step 3 is elementary: in an affine spectrum closed points are maximal ideals, and a finite space with all singleton points closed is discrete by taking complements of finite unions of closed singletons; the empty spectrum of the zero ring is checked separately. I tested the edge cases `B = 0`, `B = k`, `B = k[x]/(x^n)`, and a finite product of such algebras. The split keeps the item's three conclusions and does not introduce a duplicate of the existing dimension-zero finite-dimensionality node. The cross-unit algebraic leaf is declared as a tool use because this affine-fibre route has no replacement for that general algebra theorem.

## What was checked

- The item and new child have complete statements, source tags, blueprint references, and recorded LeanFinder, Loogle, grep, and LeanSearch queries (unavailable services are recorded as unavailable).
- The new child is statement-only, as required for an unsplit non-Mathlib node.
- `proof_deps` is the union of the non-elementary step uses, and every citation in `citations.json` is copied verbatim from the cited node statement.
- No existing project declaration or DAG node states the finite-spectrum-to-maximal-primes implication in this setting.

## Second reading by C1

- Item statement: checked against Stacks Algebra Lemma 0ALW (finite type algebra with finitely many prime ideals), together with the finite-dimensionality consequence used from 0ALW/00KH; the field, finite-type, finite-spectrum, and zero-ring hypotheses and all three conclusions agree.
- New node `lem-pqf-finite-spectrum-maximal-primes`: checked against 0ALW, equivalence of finite prime spectrum and maximality of every prime; the statement is self-contained, cites both definition nodes, has the correct Stacks tag, and has no proof body.
- Item step 1: the cited child statement exactly gives maximality of every prime under the item hypotheses.
- Item step 2: the cited finite-dimensionality node exactly supplies finite-dimensionality from finite type and maximal primes; its field and zero-ring hypotheses are inherited.
- Item step 3: checked directly from the Zariski definition: in a finite space whose points are closed, the complement of each singleton is a finite union of closed singletons, so each singleton is open; the zero spectrum is handled separately. This is elementary.
- Existing-node and Mathlib searches: searched the DAG and slopmaster2 declarations, and retained the recorded LeanFinder, Loogle, grep, and LeanSearch results; no exact child theorem was found, while the finite-dimensionality theorem is already the cited Mathlib-backed node.
- Edge cases checked: `B = 0` (empty spectrum), `B = k` (one-point spectrum), `B = k[x]/(x^n)` (one maximal prime), and finite products of such algebras.
- Changes made: none to the mathematical statements or proof steps; this second-reading section records the source, dependency, form, search, and edge-case checks required before delivery.
