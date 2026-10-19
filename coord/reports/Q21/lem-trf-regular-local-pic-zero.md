# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-local-pic-zero.json`: split statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-localized-finite-module-spread.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-regular-local-finite-free-resolution.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-invertible-module-k0-class.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-k0-class-trivial-invertible.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim statement quotes for each proof step.

## Attachments

No finished Lean declaration was found in `WeilConjectures/` or the upstream reference source.

## WANTED

None. The cited Stacks sources are present locally.

## Not duplicates

- `lem-trf-localized-finite-module-spread` vs existing localization-finiteness nodes: those nodes preserve finite generation under localization, while this node descends an arbitrary finite module over `R_f`.
- `lem-trf-regular-local-finite-free-resolution` vs existing regular-local finite-global-dimension nodes: those nodes state projective-dimension bounds, while this node gives an explicit finite free resolution of a finite module.
- `lem-trf-invertible-module-k0-class` vs existing perfect-complex nodes: those nodes concern derived complexes or finite projective local freeness, while this node gives the alternating K_0 class of a finite free resolution of an invertible module.
- `lem-trf-k0-class-trivial-invertible` vs existing Picard nodes: those nodes concern Picard groups or free modules, while this node is the determinant map implication from a K_0 equality to an explicit module isomorphism.

## What I checked

I read the imported item and its source, Stacks `more-algebra.tex` Tag 0AFZ at lines 36780–36797. The source first treats an invertible `R_f`-module as finite, descends it by Algebra Tag 05N5, resolves the descended finite module by Proposition 00O7, and applies Tags 0AFY and 0AFX; Tags 0B8I and 00NX supply the equivalence between invertible and finite locally free rank one. The item statement has exactly the corresponding regular-local, localization, finite-projective, and every-prime rank-one hypotheses.

Step 1 uses the equivalence in Tags 0B8I and 00NX, which matches the item's finite projective module and prime-local rank-one condition. Step 2 uses the finite-module descent statement with the powers of `f` as multiplicative set. Step 3 uses the finite-free-resolution statement over the regular local ring and explicitly notes that localizing an exact finite free resolution remains exact and finite free; this localization calculation is elementary from the localization definitions. Step 4 uses the K_0 statement exactly for the finite free resolution obtained in Step 3. Step 5 uses the determinant/Picard statement exactly for the equality `[P] = n[A_f]` and yields the required module isomorphism.

I checked the hypotheses on edge cases: `f = 0` gives the zero localization, where the conclusion is vacuous for the only module; `f` a unit gives `A_f = A`; a zero-dimensional regular local ring is a field; and rank one is essential (higher-rank free modules are not isomorphic to the ring). I searched the whole DAG and the main blueprint for the Stacks tags and key phrases and found no duplicate supporting node. I ran LeanSearch, LeanFinder, Loogle, and Mathlib grep searches for the item and each new node; the logs are in `searches.jsonl` files in this sandbox. Mathlib contains only general Picard and localization ingredients, not these Stacks results.

## Review by Q21

I checked every cited node's statement against the proof step that cites it and recorded verbatim quotes in `citations.json`. The item's five steps are strictly smaller than the item: the elementary rank-one invertibility identification, module descent, regular-local resolution, K_0 class calculation, and determinant triviality. The new nodes are statement-only because their proofs are sourced Stacks results and none is a Mathlib leaf. I verified all statement dependencies and retained the item's chapter and unit metadata. No source error or statement correction was needed.

## What could not be finished

No Lean code was written or compiled, as required for stage 1.

- `stage3-b4-bounded-finite-free-resolution` is an existing node used for the finite-free resolution step; the temporary duplicate node was removed.
- `lem-trf-k0-class-trivial-invertible` vs `lem-trf-regular-local-pic-zero`: the new node states the general determinant criterion from a K_0 equality, while the item states the specialized regular-local localization conclusion.
- `lem-trf-k0-class-trivial-invertible` vs `lem-pur-pid-invertible-module-trivial`: the existing node assumes a principal ideal domain and an evaluation-map hypothesis; the new node applies to arbitrary commutative rings and a K_0 determinant equality.
