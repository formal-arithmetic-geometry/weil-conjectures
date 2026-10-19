# Stage-1 report: lem-sf-rational-term-hom-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-rational-term-hom-comparison.json`: item split into three proof steps; no new nodes.
- `citations.json`: ten step/node quotations for the existing dependencies.

## Attachments

- No attachment. A repository search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, its title, rational Hom comparison terms, and the relevant blueprint names found no sorry-free declaration stating this item exactly.

## WANTED

WANTED: none.

## What was checked and corrected

The imported statement was retained. I added `def-pur-sheaf-hom` to `stmt_deps`, because the statement forms the ordinary sheaf Hom $B(F)=\mathcal Hom_R(F,R)[0]`. The blueprint ancestry remains `prop-sf-dualizable`; its `from.place` now points to the first sentence of `prop-sf-dualizable.proof.md`, where the finite-projective dual model is used. The full DAG and blueprint were searched for an equivalent node. The existing `lem-weil-pbc-ringed-site-bounded-free-rhom-model` is more general for bounded finite-projective complexes before scalar localization, but it does not state the present localized retraction result; it is cited as a tool and no duplicate node was made.

## Review by Q35

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-dualizable-biduality.json`, the imported item, the current blueprint files `prop-sf-dualizable.md` and `prop-sf-dualizable.proof.md`, and the Stacks source at Tag 08JI. I also read the complete statements of `lem-weil-pbc-ringed-site-bounded-free-rhom-model`, `def-pur-derived-internal-hom`, `def-pur-hom-complex`, and `def-weil-linear-scalar-localization` before writing the citations.

Step 1 specializes the existing bounded-free ringed-site Hom model to $E=R^{\oplus m}$ in degree zero and uses the stated K-injective representation of derived internal Hom. The standard-basis calculation identifies the comparison with the finite direct sum of the resolution map $j$; the zero-rank case was checked explicitly. Step 2 uses the two Hom-complex statements for contravariant precomposition and the scalar-localization definition for the Hom tensor and composition laws. It spells out why the comparison square extends $A[1/t]$-linearly to localized module maps. Step 3 applies that naturality to the given retraction $F[0]\rightleftarrows R^{\oplus m}[0]$. I checked the variance carefully: both $B$ and $T$ are contravariant, so $B(i)B(p)=1$ and $T(i)T(p)=1$; the inverse $T(p)c_E^{-1}B(i)$ has both composites equal to the identity by the two naturality equations. The same maps exhibit $Q_t(B(F))$ as a direct summand of the finite-free object, with $m=0$ included.

I ran the required item Mathlib searches through `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch, and repeated the search with alternate wording. The hits were generic K-injective/Hom-complex or sheaf-Hom declarations; none states this localized sheaf result, so `mathlib_match` remains null. No Lean source was written and no compiler, Lake, or build tool was run.

## Not duplicates

`lem-sf-rational-term-hom-comparison` vs `lem-weil-pbc-ringed-site-bounded-free-rhom-model`: the existing node computes derived Hom for an actual bounded-above finite-projective complex before scalar localization; this item starts with a degree-zero module that is only a retract after localization and additionally proves the localized comparison, direct-summand assertion, and localized naturality.

## What could not be finished

Nothing remains unfinished in this stage-1 split.
