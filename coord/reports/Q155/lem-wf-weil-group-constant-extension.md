# Q155: lem-wf-weil-group-constant-extension

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-weil-group-constant-extension.json`: existing target, split into two proof steps; statement and hypotheses retained.
- `dag/nodes/sec-purity-real-sheaves/lem-wf-weil-group-constant-extension-pi1-base-change.json`: new statement-only supporting node; Mathlib verdict no match.
- `citations.json`: verbatim statement quotes for every cited node in each step.
- No Lean files, compiler, Lake build, or live-project files were changed.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, the item title, and Weil-group/fundamental-group constant-extension terminology. No declaration states this target without `sorry`; the existing Weil-group declarations cover only the definitions and exact sequence used below.

## WANTED

None. The blueprint proof is available locally. The new supporting node is statement-only and records the finite-etale/Galois descent comparison as an unsplit input rather than claiming a Mathlib theorem.

## Corrections and limitations

The imported statement is mathematically consistent, including the normalized degree formula and the final degree-one assertion. I corrected the imported dependency bookkeeping: the statement names the finite-field datum, Frobenius convention, Weil-group definition and arithmetic fundamental representation, so these are now in `stmt_deps`. The imported proof's first paragraph hid the non-elementary finite-etale/Galois descent comparison; that comparison is now the separate supporting node. The target's second paragraph remains the Weil-group/Frobenius argument and does not restate a target clause as a new node.

## Not duplicates

`lem-wf-weil-group-constant-extension-pi1-base-change` vs `lem-wf-weil-group-exact-sequence`: the existing node proves exactness of the degree sequence for one Weil group; the new node compares arithmetic fundamental groups under the finite constant-field base change and states the unchanged geometric kernel.

`lem-wf-weil-group-constant-extension-pi1-base-change` vs `def-wf-weil-group`: the existing definition constructs the inverse image of the integer Frobenius subgroup inside one arithmetic fundamental group; the new node identifies the arithmetic fundamental group of $X_0^{(m)}$ itself with an inverse image of a finite-field Galois subgroup.

`lem-wf-weil-group-constant-extension-pi1-base-change` vs `def-weil-finite-field-fiber`: the existing definition fixes the finite-field datum and geometric fibers; the new node is the nontrivial base-change theorem for arithmetic fundamental groups and finite étale covers.

## Mathlib searches

For the item I ran LeanFinder with the finite constant-field Weil-group formulation, Loogle with the expected fundamental-group/finite-field names, grep over `AlgebraicGeometry/` and `FieldTheory/`, and LeanSearch with the arithmetic fundamental-group formulation. The hits were abstract Galois-group or finite-field Frobenius declarations; no Mathlib declaration states the scheme Weil-group result. Loogle reported an unknown identifier, so its record is marked unavailable rather than treated as evidence of absence.

For the new node I ran the same three search families with its own id and read every returned candidate. LeanFinder and LeanSearch returned abstract Galois groups, while grep returned unrelated Galois connections and the generic etale finite-limit instance. No result is an exact statement or a one-line specialization. The exact queries and returned names are recorded in the node and in `searches.jsonl`.

## Review by Q155

I read the target node, its chapter `sec-purity-real-sheaves`, its unit `sk-d-real-weil`, and the full master blueprint source `literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-d-real-weil/lem-wf-weil-group-constant-extension.md`. I also read the full statements of `def-weil-finite-field-fiber`, `def-tw-frobenius-action`, `def-wf-fundamental-representation`, `def-wf-weil-group`, and `lem-wf-weil-group-exact-sequence` from the DAG. The source's first paragraph explicitly uses finite-etale cover descent and identifies the arithmetic fundamental group with the inverse image of `Gal(k/F_{q^m})`; that is exactly the statement of the new supporting node. Its second paragraph uses geometric Frobenius becoming the $m$-th power, the Weil-group inverse-image definition and degree map, and exactness of the degree sequence; these are the four citations in step 2.

For step 1, the finite-field datum supplies $k_0$, $k$, $\mathbf F_{q^m}$ and the base-change scheme, while the new node supplies the arithmetic fundamental-group comparison and the unchanged geometric kernel. The final restriction to the cyclic Frobenius subgroup is the definition of the Weil group, so no unstated descent construction is being taken from a node's proof. For step 2, the Frobenius-action definition supplies the convention that geometric Frobenius over $\mathbf F_{q^m}$ is the $m$-fold iterate. The Weil-group definition supplies the projection and degree, and the exact-sequence statement supplies the kernel $\pi_1(X)$ and degree-one Frobenius lifts. The new node supplies the subgroup restriction after constant extension. Dividing the old degree by $m$ therefore gives the normalized degree, and $s^m$ has normalized degree one.

I checked edge cases $m=1$ (the comparison is the identity and the normalized degree is unchanged), $X_0=\operatorname{Spec}\mathbf F_q$ (the geometric subgroup is trivial and the statement reduces to $m\mathbf Z\subseteq\mathbf Z$), and a degree-one lift $s$ (its $m$-th power has old degree $m$ and new degree $1$). No hypothesis was added or dropped, and no SGA source was used. The new node is strictly smaller than the target and has no cycle back to the item.

No step exceeds 2000 characters or hides a second lemma beyond the new node. Every non-elementary fact used by each step is cited, and every citation quote in `citations.json` is copied verbatim from the corresponding node statement.
