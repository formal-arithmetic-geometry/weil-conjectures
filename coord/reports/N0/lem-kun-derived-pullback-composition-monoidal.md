# Stage 1 report: lem-kun-derived-pullback-composition-monoidal

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-derived-pullback-composition-monoidal.json`: statement node, split with seven proof steps; no new nodes.
- `citations.json`: 29 verbatim step/node citations.

## Attachments

None. I searched the project source for the item id and for the derived pullback composition/tensor declarations. The source has narrower declarations (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`, `leftDerivedUpperStarComp_assoc'`, and the unit comparison lemma), but no declaration states this full constant-coefficient package exactly.

## WANTED

None.

## Not duplicates

No new node was created, so there are no duplicate pairs to record.

## Source or statement issues

The imported statement is retained. Its source explicitly identifies the displayed coherence equations as an agent-stated comparison extracted from the Kunneth compatibility proof; the proof below follows that route and does not silently change coefficient categories or hypotheses. The item’s existing Mathlib searches were read and retained; they found only generic or underived infrastructure, not this derived étale statement.

## What remains

No unfinished sub-node or proof obligation remains in this sandbox. The item is stage-1 split; no Lean file was written and no compiler or build tool was run.

## Review by N0

I read the item node, its `sk-thm-sf-compatibility` unit, the `sec-smooth-purity` chapter record, the main-20261015 Kunneth proof, and the relevant declarations in `WeilConjectures/SixFunctors/Etale/Derived/UpperStarMonoidal/Comp.lean`, `Unit.lean`, `UpperStarCompCoherence.lean`, and `UpperLowerStar/MonoidalComp.lean`. The source confirms the same three ingredients used by the split: termwise pullback monoidality, normalized composition comparisons, and associativity of composition comparisons. I also checked that no source declaration carries the item’s blueprint tag or exact full statement.

Step 1 reduces all equations to K-flat complexes with flat terms. I checked that `def-kun-derived-tensor` defines the total tensor model, `lem-weil-pbc-site-derived-tensor-descent` states both the K-flat localization equivalence and uniqueness of natural transformations from K-flat representatives, `prop-weil-pbc-inverse-image-modules-exact` supplies exact module inverse image, and `lem-weil-pbc-exact-functor-derived-factorization` supplies the termwise derived factorization. Thus the reduction uses the cited hypotheses and does not assume boundedness.

Step 2 reads the exact module composition statement in `lem-weil-pbc-inverse-image-composition-module-linear` and the derived tensor pullback statement in `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; both apply to the constant ring on the small étale sites. The displayed termwise calculation is on the total tensor summands, so the same Koszul signs occur on both paths. Step 3 then invokes the descent statement and gives the item’s tensor-composition equation, with naturality inherited from the cited bifunctorial comparisons.

Step 4 uses exactly the constant-sheaf comparison from `lem-kun-pullback-constant`, the two unit constraints from `lem-kun-tensor-unit`, and the composite-adjunction normalization in the module-composition node. I verified that the equation has the item’s direction for `gamma` (the inverse of `c`) and that K-flat descent extends it to the unbounded derived category.

Step 5 checks both left and right unit equations on the same K-flat representatives. The cited 07A4-derived pullback comparison is natural, `lem-kun-inverse-image-monoidal` supplies its bifunctorial isomorphism, and the constant comparison plus both unit constraints identify the endpoints. No symmetry is used, and the equation is then descended by the K-flat equivalence.

Step 6 uses the full statement of `lem-weil-pbc-inverse-image-composition`: each module composition map is uniquely characterized by transport of the composite-adjunction unit. `lem-cat-right-adjoint-composition` identifies that unit with the pasted unit. Therefore the two threefold composites have the same normalization; taking inverses gives precisely the item’s associativity equation. Step 7 records that all maps are natural and that only canonical associators and identity identifications are used.

I checked every `uses` entry against the cited node statement and wrote a verbatim quote for every step/node pair in `citations.json`. The longest proof step is below 2000 characters and contains no hidden lemma beyond the cited K-flat and adjunction statements. `srvcheck.py ... check_dag` returned `check_dag OK` on the completed sandbox.
