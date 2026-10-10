Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-duality.json` — item split; no new Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-sc-finite-duality-trace.json` — new trace-comparison statement node; Mathlib search verdict is no direct sheaf-level match.

Attachments:

- `AlgebraicGeometry.Scheme.exists_isIso_pushforwardHomObjComparison_unit` belongs to `lem-sc-finite-duality-trace`.
- `AlgebraicGeometry.Scheme.nonempty_homObj_pushforward_iso` is the closed slopmaster2 declaration matching the item; its proof depends on the trace comparison declaration above.

WANTED: Hartshorne, *Algebraic Geometry*, III (6.10), (6.12), and Serre, *Local Fields*, Ch. II §4 are cited by the imported blueprint but are not present as local literature files; the trace node records the theorem statement and source location.

The trace-comparison node is new in this delivery. Before creating it I searched the whole DAG with `grep -rl` for `trace`, `codifferent`, and `pushforwardHomObjComparison`, and searched the imported blueprint with `tools/blueprint_refs.py search trace codifferent finite`; no existing node stated this comparison.

## Source error

The blueprint's local calculation using `u=x^e`, the dual-basis generator `x^{-(e-1)}/e`, and division by `e` is invalid for wild ramification. For example, in characteristic $p$, a degree-$p$ Artin–Schreier or Frobenius-type cover has ramification index $e=p$, which is zero in $k$, so division by $e$ is impossible. I removed that calculation from the item's proof and retained the trace theorem as the cited non-elementary result.

## Review by E1

I read the item blueprint and `WeilConjectures/AlgebraicGeometry/Curve/SerreDuality.lean`, lines 527–615. The new trace node was checked against the declaration at lines 527–541: its $k$ is an arbitrary field, $X$ has a smooth morphism to $\\operatorname{Spec}k$ of relative dimension one (the source's `SmoothOfRelativeDimension 1`), and $f$ is over $k$, finite, and flat. I therefore removed the incompatible citations to the algebraically closed-only curve and Kähler-differential definition nodes, defined relative differentials by their affine generators and relations, and added [def-sc-p1-standard] for $\\mathbf P^1_k$. The statement says that $\\tau$ is an $\\mathcal O_{\\mathbf P^1_k}$-linear morphism and that the comparison $\\omega\\mapsto(a\\mapsto\\tau(a\\omega))$ is $f_*\\mathcal O_X$-linear; it does not call $\\tau$ canonical, since the Lean declaration only asserts existence.

For the item's three proof steps, I checked the cited content against the blueprint. Step one is the explicit restriction-of-scalars adjunction on affine opens, with localization giving the sheaf adjunction, and is elementary. Step two uses the new trace node, whose statement is exactly the finite-flat differential comparison required by the Lean theorem; it does not use the invalid tame uniformizer calculation. Step three uses the trace node and [lem-sc-invertible-dual]. The trace comparison is $f_*\\mathcal O_C$-linear, which is what lets it pass through the adjunction of step one; finite local freeness gives the tensor-Hom isomorphism locally, including rank zero, and the invertible-dual node gives the specialization to $\\mathcal M^{-1}$. I added [def-sc-p1-standard] to the item's statement dependencies, verified every cited id exists, and checked that `proof_deps` is the union of the step uses. The item blueprint references still identify the first, second, and final proof paragraphs, while the new node's `blueprint.from` points to the trace-identification sentence.

I also checked the B1–B7 form requirements: all displayed mathematics uses TeX delimiters and single backslashes in rendered text, every node is self-contained, and the new node carries the three required Mathlib search kinds (LeanSearch, Loogle/LeanFinder, and source grep) with no direct match. The source-error counterexample above records why the removed division-by-$e$ argument cannot be retained.

What remains for the maintainer is the mathematical review of the imported classical Hartshorne/Serre source; no further node was needed.
