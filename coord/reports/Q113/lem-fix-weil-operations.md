## Files written

- `dag/nodes/sec-six-functors/lem-fix-weil-operations.json`: the existing statement node, completed as a stage-1 split (`status: split`), with its ten proof steps and existing dependency set retained; no new nodes.
- `citations.json`: 49 step-to-node citations, each quoting the cited node statement verbatim.
- `report.md`: this report.

## Attachments

None. The source checkout has no declaration tagged `(blueprint: lem-fix-weil-operations)` that states the full item. The declaration `AlgebraicGeometry.Etale.isWeilPairing_mixedSupportCupProduct` in `WeilConjectures/SixFunctors/Etale/Derived/WeilFrobenius.lean:387` proves only the cup-product clause and therefore is not an attachment for this item.

## WANTED

None.

## What was checked and corrected

The imported node was already split and had a maintainer review record, but remained `unsplit`; I changed only its status to `split`, preserved its statement, ten proof steps, dependencies, blueprint metadata, tool-use metadata, and review history, and supplied the required citations file. I checked the whole DAG for duplicate nodes before retaining the existing dependencies; every cited id exists and the union of the step uses is exactly `proof_deps`. The item has no new node to search or split. The item-level Mathlib searches were rerun with `msearch.py` (LeanFinder, Loogle, grep, and LeanSearch, including the prior query set); the returned generic category-theory and sheaf results do not state the all-stage geometric Weil-operation assertion, so `mathlib_match` remains null.

## What could not be finished

Nothing at the stage-1 natural-language level. No Lean files were written and no compiler or build tool was run, as required.

## Review by Q113

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.md` and its proof, the inherited statement and ten-step split, and the corresponding source declarations in `WeilConjectures/SixFunctors/Etale/Derived/WeilFrobenius.lean`. The source declaration found there is only the mixed-support cup-product pairing, so it does not cover the full item. I also read `def-fix-six-functor-datum`, `def-weil-weil-sheaf-complex`, `def-weil-frobenius-detailed`, and every node cited by each step. Steps 1–3 use the finite-field conventions, fixed-pair category, Frobenius square, exchange data, and compact-support operation data exactly as those statements define them. Steps 4–6 use the existing pullback, inverse-image, tensor, internal-Hom, K-injective, K-flat, scalar-extension, and constructible tensor-completion statements; the long Step 6 is the explicit signed evaluation and completed-tensor transport calculation, with no hidden separate lemma. Step 7 uses the stated adjunction/mate and admissibility nodes for the exceptional adjoint and proves unit/counit equivariance by the triangle identities. Step 8 uses the exchange pasting, pullback-composition, integral reduction, and mate-pasting statements for composition and exchange maps; its long tower argument explicitly invokes the cited completed-pullback reduction node. Step 9 expands the projection transformation into tensor, counit, exchange, extension-by-zero, and compactification comparison maps, each covered by the cited statements. Step 10 uses the coefficient-twist definitions and the scalar Frobenius lemma, including the cases of negative and zero twists. For every step, `citations.json` records a verbatim statement quote for every cited node; all hypotheses and coefficient-domain restrictions were checked against those node statements. I tested the edge cases called out by the proof (inverse Frobenius square, non-invertible finite-coefficient Frobenius morphisms, negative and zero twists, and the restricted constructible domains) and found no statement correction required. The only correction made in this worker copy was changing the already-complete split's stale `status` from `unsplit` to `split`.
