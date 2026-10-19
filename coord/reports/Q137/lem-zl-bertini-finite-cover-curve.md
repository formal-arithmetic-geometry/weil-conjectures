# Worker report

## Files written

- `lem-zl-bertini-finite-cover-curve.json`: statement updated to the current main-20261015 formulation and split proof.
- `lem-zl-bertini-sections.json`: statement-only Stacks 0FD5 input; no Mathlib match.
- `lem-zl-bertini-smooth-member.json`: statement-only Stacks 0FD6 input; no Mathlib match.
- `lem-zl-bertini-irreducible-member.json`: statement-only Stacks 0G4F input; no Mathlib match.
- `lem-zl-bertini-finite-field-descent.json`: statement-only finite-field descent input; no Mathlib match.
- `citations.json`: verbatim statement quotations for every citation in every proof step.

## Attachments

The declaration `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` in `WeilConjectures/AlgebraicGeometry/Bertini.lean:53-71` matches the item but contains `sorry`; it is therefore not an attachment.

## WANTED

None. The Stacks sources and the current blueprint proof are present locally.

## Not duplicates

- `lem-zl-bertini-sections` vs `lem-zl-bertini-finite-cover-curve`: the child is the 0FD5 linear-system input on a proper scheme, while the item constructs a curve preserving a finite etale cover.
- `lem-zl-bertini-smooth-member` vs `lem-zl-bertini-finite-cover-curve`: the child is the 0FD6 smooth-general-member theorem, while the item includes prescribed points, iteration, connected pullback, and descent.
- `lem-zl-bertini-irreducible-member` vs `lem-zl-bertini-finite-cover-curve`: the child is the 0G4F irreducibility criterion for one linear system, while the item applies it simultaneously to a finite cover and iterates.
- `lem-zl-bertini-finite-field-descent` vs `lem-zl-bertini-finite-cover-curve`: the child is the coefficient-level finite-field descent fact, while the item combines it with Bertini and connectedness.

## What I checked

I read the imported item, the current main-20261015 item and proof files, the chapter and unit records, and the matching Lean declaration. The Lean declaration has the exact target-shaped conclusion but is sorry-backed. The current blueprint statement is stronger and more specific than the imported arbitrary-algebraically-closed-field statement, so I replaced the statement with the finite-field geometric-fiber formulation required by the blueprint update and retained the exact Frobenius-stability clause.

For Step 1 I read Stacks Tag 0FD5 in `varieties.tex`: it gives generation away from the prescribed closed subscheme and an immersion. I also read the existing Serre-vanishing node `lem-pc-serre-vanishing`; its statement gives eventual vanishing of higher cohomology for coherent twists by an ample invertible sheaf, which is the input used for the first-infinitesimal-neighborhood derivative surjectivity. For Step 2 I read Tag 0FD6 and cited the new smooth-member node, whose hypotheses are exactly smoothness, generation, and immersion of the linear system. For Step 3 I read Tag 0G4F in `more-morphisms.tex` and checked that the codimension-two hypotheses stated in the new irreducible-member node are the ones used by the source. The finite inverse image of the finite base locus has codimension at least two because the cover is finite and the ambient dimension is at least two.

Step 4 was checked against the fourth proof paragraph: closed subschemes of the affine scheme remain affine, smooth geometrically irreducible zero loci are connected, finite etale base change remains finite etale, and the construction can be iterated while the dimension is at least two. Step 5 was checked against the blueprint's finite-coefficient argument: only finitely many coefficients occur, so one finite extension contains them all and a Frobenius power stabilizes the resulting data. I tested edge cases conceptually: dimension two gives one final curve cut; a singleton prescribed set still has a nonempty derivative-open condition; and a trivial finite etale cover remains connected after every cut. I corrected the imported statement, replaced its empty dependency list with the actual cited nodes, and added the required search records and verbatim citation quotes.

## Source error

The imported node's statement and Lean declaration were out of date relative to `blueprint_update`: the imported statement allowed an arbitrary algebraically closed field and omitted the geometric-fiber/Frobenius model data, while the current blueprint requires $X_0/\mathbf F_q$, $X=X_0\times k$, and Frobenius stability. I corrected the node to the current statement rather than silently proving the older one.

## What could not be finished

The four child lemmas are intentionally statement-only stage-1 nodes; their proofs and any Lean implementation belong to later stages.

## Review by Q137

I checked the source and hypotheses for each step as described above, opened every cited node, verified that each quoted sentence in `citations.json` is verbatim, searched the whole DAG and blueprint for duplicate Bertini or descent nodes, and recorded all four required Mathlib search kinds for the item and each new node. No SGA source was used.
