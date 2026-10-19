# Worker report: lem-coef-finite-scalar-mate-realization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-scalar-mate-realization.json`: repaired item split; no new node.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, title, and finite scalar-mate terminology; no sorry-free declaration under `WeilConjectures/` states this item.

## WANTED

None.

## What was wrong in the returned split and what changed

The previous Step 5 applied `lem-pur-compact-support-roos-cofinality`, whose statement is for modules over a constant ring and whose unit belongs to `sk-thm-sf-compatibility`; it did not justify the completed-sheaf towers used here. I replaced it with the existing `lem-pur-compact-support-integral-coefficient-comparison`, whose statement covers completed coefficient sheaves, finite-Tor constructible inputs, the fixed compactification, and the cofinal strict reduction towers before derived limits. I declared that off-unit statement as a generic tool use and checked its hypotheses in the step. Step 7 previously asserted that the integral mate identity could be transported from finite projections without stating that the integral adjunction itself is the total-limit adjunction. It now cites and applies `lem-pur-normalized-reconstruction-adjunction-calculus`, comparing the adjuncts as system maps via the reduction/limit unit and counit. Step 6 now cites `lem-coef-integral-finite-extension` for exactness and preservation of the constructible categories before applying the S-adjunction. I restored the missing `$...$` delimiters and backslashes in Steps 1 and 3--8. The item statement is unchanged and no new node was created.

## Review by Q30

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-coef-rational-operations.proof.md`, including the finite scalar-extension paragraph at lines 80--92, and checked the current item statement against it. I read the complete statements of every node cited in the eight steps, including the two repair citations `lem-pur-compact-support-integral-coefficient-comparison` and `lem-pur-normalized-reconstruction-adjunction-calculus`.

Step 1 uses the fixed compactification node and the finite-free extension node for finite freeness of $B_n/A_n$ and the projection comparison, then constructs the displayed finite compact-support map. Step 2 uses the finite adjunction-diagram realization, whose statement places $M_n$ in $D^b_{ctf}(Y,A_n)$ and supplies actual evaluation and transpose maps. Step 3 uses the finite-free coefficient-reduction compatibility, the simultaneous adjunction realization, and the normalized-system calculus; these statements justify strict chain-map coefficient squares and normalized transitions. Step 4 uses the system tensor-Hom evaluation/transposition and the finite exceptional quotient cocycle, so the coherent transpose is formed as a system morphism before taking limits.

For Step 5 I verified the hypotheses of the completed-sheaf compact-support comparison: $E\subset L$ is finite, $f$ is separated finite type between separated finite-type schemes, the fixed compactification is used, and $M$ is derived-complete constructible with finite Tor amplitude. Its cited statement explicitly gives compatible finite tensor comparisons on cofinal $B_n=S/v^{en}$ strict towers before derived limits and identifies them with the prescribed integral compact-support construction. The coherent realization clause of `prop-coef-integral-exceptional-adjoint` supplies the same reduction/limit realization for the exceptional target. Step 6 uses the completed finite-free scalar comparison and the integral scalar-extension definition, and now explicitly invokes `lem-coef-integral-finite-extension` to check that $T_XG_RM$ and $T_YM$ lie in the $S$ constructible categories before $F_S$ and $G_S$ are applied. The finite adjunction and integral exceptional realization then identify the total-limit source and target.

Step 7 uses the coherent integral realization, the system evaluation calculus, and the normalized reconstruction adjunction calculus. The latter states that $\mathcal L\mathcal F\mathcal R$ is left adjoint to $\mathcal L\mathcal E\mathcal R$ and that its adjunct transpose is the total limit of the system counit composite. Thus the two adjuncts are compared as actual system maps using the unit/counit identities; equality is not inferred from levelwise reductions. Step 8 uses the naturality clauses of the finite extension, finite exceptional, system calculus, integral realization, and completed-sheaf compact-support comparison; the listed edge cases $E=L$, $f=\mathrm{id}$, $M=0$, $n=1$, and empty schemes reduce to identity or zero systems. I checked every `citations.json` quote verbatim against its node statement and kept `proof_deps` equal to the union of step uses. No Lean files, compilers, or build tools were run.

## What remains

Nothing remains for this repair before the required dry run and delivery.
