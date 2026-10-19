# Worker report: def-pod-perfect-point-complex

## Files written

- `dag/nodes/sec-six-functors/def-pod-perfect-point-complex.json`: the item, marked `split`; no new nodes and no Mathlib leaves.
- `citations.json`: empty, because a definition has no proof steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag, perfect point-complex terminology, `IsPerfect`, `IsDualizable`, derived duals, and evaluation/coevaluation. The source declaration `DerivedCategory.IsPerfect` in `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean` states the bounded finite-projective perfectness clause, but it does not state the complete item including the point dual and both canonical maps. The source's generic `DerivedCategory.isPerfect_iff_isDualizable` likewise has different hypotheses and conclusion. No exact finished attachment exists.

## WANTED

None. The relevant source files are present locally; this is a definition split.

## Source and route notes

The imported statement agrees with `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/def-pod-perfect-point-complex.md` (order 2587) and the unchanged master source (order 2243). I retained the item's three existing statement dependencies. `def-pod-conventions` supplies the fixed point category, coefficient ring A, derived tensor/internal-Hom operations, the point dual formula (C^\vee=R\operatorname{Hom}_A(C,A)), and the adjunction context. `def-weil-finite-coefficient-point` and `def-weil-geometric-hypotheses` supply the coefficient-stage and geometric setting named by the item. No proof steps are required for a definition, so there are no step citations and no child nodes.

The mandated Mathlib searches were run for the item itself. LeanFinder returned only generic K-projective and derived-category results; Loogle returned no hit (`IsPerfect` was unknown); grep returned no hit under `CategoryTheory/DerivedCategory`; LeanSearch returned generic linear-algebra and `ExactPairing` evaluation/coevaluation declarations. These are not an exact project-specific match, so `mathlib_match` remains null and no Mathlib leaf was created.

## Review by Q98

I read the item node, both the current and master blueprint definition files, the six-functor chapter and `sk-thm-sf-package` unit records, and the cited convention, finite-coefficient-point, and geometric-hypothesis nodes. The statement's perfectness clause introduces an object in the point category and requires a bounded complex of finite projective A-modules; the derived-dual clause uses the A-linear derived internal Hom; and evaluation and coevaluation are exactly the unit/counit maps supplied by the tensor–internal-Hom adjunction. The convention node explicitly contains the point dual formula and operation context, so no separate duplicate definition node is needed. I checked the finite-stage and field-stage edge cases represented by the fixed coefficient set: the definition is meaningful for A_{E,n}, O_E, E, and Qbar_l, and it imposes no properness or smoothness beyond the fixed conventions. The zero complex and a bounded complex concentrated in one finite projective module satisfy the definition directly; no clause excludes them. I also checked that the generic source `DerivedCategory.IsPerfect` is only the first clause and therefore cannot serve as an attachment for the full item. No source error or statement correction was needed.

## Dry run

Ran `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q98 def-pod-perfect-point-complex --no-push .` on 2026-10-17. The server preflight printed `OK (not pushed)` for `deliver/Q98/def-pod-perfect-point-complex`; no failures were reported.

## Second reading by Q98

- Item statement: checked against `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/def-pod-perfect-point-complex.md` (order 2587) and its master counterpart (order 2243). The current source supplies the missing “an”; the fixed setting, point object, bounded finite-projective criterion, derived-dual formula, and adjunction-map clause agree. Updated the source record and adopted that grammatical correction.
- Perfectness clause: opened the existing `def-pc-perfect-ring-complex` and checked its bounded finitely generated projective model against Stacks `more-algebra.tex`, Tag 0657, `definition-perfect` (lines 18870ff). It states exactly the notion at the ring `A`; added it as a direct statement dependency and inline citation. No new definition is needed.
- Point category and dual clause: opened `def-pod-conventions`, `def-weil-finite-coefficient-point`, and `def-weil-geometric-hypotheses`. The convention defines the coefficient-stage point categories, writes `A` for their coefficient ring, and explicitly defines `C^\vee=R\operatorname{Hom}_A(C,A)`. At algebraically closed coefficients it uses the common-stage category, as the finite-coefficient-point definition specifies. No new category or identification with a different coefficient category is introduced.
- Adjunction maps: read pinned Mathlib `CategoryTheory/Monoidal/Closed/Basic.lean:82–97`. `ihom.ev` is the counit and `ihom.coev` is the unit of tensor–internal-Hom adjunction, exactly the source's wording. In particular the counit at `A` is evaluation `C\otimes_A^L C^\vee\to A`. The generic adjunction unit has target `RHom_A(C,C\otimes_A^L D)`; it is not an assertion that every point object has an exact dual pairing. I also read `Rigid/Basic.lean:75–91`, where `ExactPairing` instead includes triangle identities. These generic component definitions do not replace the complete item.
- Proof steps: none in the source or repaired node, since this is a definition. No proof-step citations, hidden proof claims, or elementary-step flags remain to check; `citations.json` correctly stays empty.
- New nodes: none. Searched DAG and blueprint wording for perfect point complexes, perfect ring complexes, derived duals, and evaluation/coevaluation. The general perfectness definition is now reused; `def-pod-perfect-complex-on-x` and `def-pod-coefficient-dual-on-x` concern sheaves on `X`, not this point definition. Independently reran LeanFinder with bounded finitely generated projective/dualizable vocabulary, qualified Loogle with `CategoryTheory.ExactPairing`, and grep under `CategoryTheory/Monoidal`; preserved their actual outputs in `searches.jsonl` and recorded them in the item. No exact Mathlib match was found.
- Source attachment: read `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean:92–98`; `DerivedCategory.IsPerfect` is the first clause, already attached to the general perfect-ring node, and does not define the point dual and both adjunction maps. It is not an attachment for the entire item.
- Edge cases: the zero complex and a one-term finite-projective complex are perfect. Over a field the same finite-projective criterion applies; over a finite coefficient ring the definition does not declare every bounded finite-cohomology object perfect. The fixed convention permits `n=1`, requires `n\ge 1`, and fixes a nonempty geometrically connected smooth scheme, so `n=0` and the empty scheme are outside its setting; properness is not added.
- Changes: adopted the current blueprint's missing article and source location; added inline citations and the existing perfect-ring definition dependency; recorded independent searches and this review. Retained all correct mathematical clauses, the worker's sections, and the empty citation file. No new nodes, Mathlib leaves, or statement dispute.

Second-reader validation: the prescribed `deliver.py Q98 def-pod-perfect-point-complex --no-push .` completed successfully on 2026-10-17 and printed `OK (not pushed)` at `fa11071ff5`: server preflight passed for the repaired node and independent review.
