# Stage 1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-surjective-coherent-generic-support.json`: statement split into six proof steps following Stacks Tag 01YO; existing three-kind Mathlib verdict remains no match.

No new nodes were needed.

## Attachments

None.

## WANTED

None. The pinned Stacks source was read from the fetched project literature at `coherent.tex` lines 3487-3521, and the cited labels were checked in `tags/tags`.

## Problems found

The accepted statement agrees hypothesis by hypothesis with Stacks 01YO. The unsplit node had no proof. Stacks leaves several facts implicit, now exposed in the steps: the image of the reduced closure is exactly `Z`; the morphism factors through the closed subscheme `Z`; the pushed-forward structure sheaf is coherent; the generic stalk is computed as `(B/q)_p = kappa(xi')` using finite integrality and incomparability; and closedness of coherent support upgrades nonvanishing at the generic point to support equal to all of `Z`.

The existing source metadata gives `coherent.tex line 3479`; in the pinned local Stacks checkout the lemma begins at line 3479 and its proof occupies lines 3487-3521, so the tag and label are correct.

## Could not finish

Nothing. No Lean was written or compiled, as required for Stage 1.

## Review by E1

I read Cohomology of Schemes Lemma 01YO and checked the parent statement's finite, surjective, locally Noetherian, integral closed subscheme, support, and generic-stalk clauses against it. Step 1 obtains a lift of the generic point and the reduced integral closure using the cited nodes. Step 2 uses finite closedness to identify its image with $Z$ and the reduced-source factorization statement to obtain $Z'\to Z$. Step 3 applies finite pushforward coherence to the closed inclusion. Step 4 computes the stalk on an affine neighbourhood: integrality and incomparability make the chosen generic point the only prime above $\mathfrak p$ in $Z'$, so $(B/\mathfrak q)_\mathfrak p$ is the fraction field $\kappa(\xi')$. Step 5 uses the local residue-field map to kill the maximal ideal. Step 6 uses closed support of a finite-type coherent module and the closed-pushforward stalk formula to make support exactly $Z$. These are the statements of the cited nodes, and the remaining identifications are elementary. I checked the identity finite map and an irreducible component as edge cases. No new node, duplicate, cycle, added hypothesis, or route departure occurs. The report and item form one commit; no correction was sent back.
