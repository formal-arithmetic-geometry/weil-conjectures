# Stage 1 report: `lem-weil-pbc-module-filtered-colimit-finite-presentation`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-filtered-colimit-finite-presentation.json`: parent statement split into seven proof steps; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-presentation-representatives.json`: statement node for the set of isomorphism representatives; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-type-submodule-extension.json`: statement node for Properties 01PF; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-presentation-extension.json`: statement node for Properties 01PI; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-presentation-direct-sum.json`: finite direct-sum closure node; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-presentation-cokernel.json`: finite-presentation cokernel closure node; Mathlib verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-stalk-filtered-colimit.json`: stalk/filtered-colimit interchange node; Mathlib verdict is no match.

## Attachments

None. The node has no Lean declarations in either source checkout.

## WANTED

None. `literature/stacks-project/properties.tex`, `modules.tex`, and `sheaves.tex` contain the cited proofs.

## Findings

- The imported statement is correct and matches Properties Lemma 01PJ.
- The imported node was unsplit despite its proof depending on the representative-set construction, 01PF, 01PI, finite direct sums and cokernels of finite-presentation modules, and stalks commuting with filtered colimits. These are now public child nodes.
- The proof follows 01PJ: construct the category of finite-presentation maps to `F`; establish nonemptiness, common successors, and equalizers; identify the colimit stalkwise; prove injectivity by extending a finite-type kernel submodule; prove surjectivity by extending a map from `O_U`; conclude by stalkwise isomorphism detection.
- On return, all six child statements were made self-contained and their exact Stacks tags/places recorded: 01BC, 01PF, 01PI, 01BN, 0H96, and 009E. In the injectivity step the cyclic submodule is now explicitly the image of `O_U -> F_i|_U`; `lem-weil-pbc-quasi-coherent-module-cokernel-image` proves it quasi-coherent, and its quotient presentation proves it finite type before 01PF is applied.
- The possible existing duplicate `lem-kun-stalks-commute-colimits` concerns geometric stalks on the small etale site and arbitrary colimits of etale sheaves. The new `lem-weil-pbc-module-stalk-filtered-colimit` concerns ordinary Zariski stalks of sheaves of `O_X`-modules and supplies the linear colimit cocone used by 01PJ, so it is not a duplicate and remains a child.
- `python3 tools/check_dag.py` reports 0 cycles; `python3 tools/review_split.py lem-weil-pbc-module-filtered-colimit-finite-presentation` passes.

## Unfinished

The six new children are intentionally `unsplit` and join the Stage 1 queue. No Lean code was written or compiled.

## Review by E1

I checked the seven parent steps against Properties 01PJ and the cited 01BC, 01PF, and 01PI arguments. The filtered-category construction, stalkwise colimit map, kernel extension, surjectivity extension, and final stalkwise isomorphism are explicit. Each new child now introduces its objects and exact source tag, and Step 5 identifies the cyclic image as a finite-type quasi-coherent submodule before invoking 01PF, with the existing public cokernel-image node cited. The stalk-colimit child is distinct from the geometric etale-stalk node. I accept the repaired split.
