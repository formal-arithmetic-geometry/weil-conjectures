## What changed

Closed the body of `AlgebraicGeometry.Etale.pullbackSections_comparison` by a real reduction. Its existing signature, docstring, and the complete definition of `pullbackSectionsEquiv` remain unchanged. The definitional private helper `pullbackSectionsEquiv_apply` identifies that construction with the explicitly constructed `etaleObjectSectionsIso` followed by the inverse-image composition map.

The reduction first applies `etaleObjectSections_baseChange` to `H = f^* G`. Evaluation-isomorphism naturality moves the comparison `h^* f^* G → g^* G` through evaluation. Two applications of the existing proved `upperStarComp_hom_app_map_upperStarComp_inv_app` establish the missing coherence. Global-sections pullback naturality is proved locally from unit naturality, sheaf-map naturality, and terminal evaluation naturality. This last argument follows the already proved private `sections_naturality` in `Sheaf.Paper.EtaleHypercohomologyPullbackMaps`, without importing that large module or adding a duplicate public theorem.

Added `Sheaf.AlgebraicGeometry.EtaleObjectSections`, containing an explicit natural evaluation/global-sections isomorphism and one named lower theorem. Added its missing DAG node and updated the original node's actual proof route. Its source and full natural-language proof describe the remaining terminal-evaluation and pullback-pasting identifications. There are no data chosen from unproved existence statements.

The new main-module imports are plain proof imports of `Sheaf.AlgebraicGeometry.EtaleObjectSections` and `WeilConjectures.SixFunctors.BaseChange.Pasting`. The two original public imports remain. No new public import is added to the existing module. Elaboration options are scoped to the target proof; the heartbeat increase has an explanatory comment. The unused-variable linter is scoped off because it misreports the projection equality referenced through proof-irrelevant comparison arguments.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.pullbackSections_comparison` (node `lem-weil-pbc-pullback-sections-comparison`). No sorry remains in the item's module.

Hole added: `AlgebraicGeometry.Etale.etaleObjectSections_baseChange` in `Sheaf.AlgebraicGeometry.EtaleObjectSections` (node `lem-weil-pbc-etale-object-sections-base-change`). Its proof is exactly `:= by sorry`, with its source and complete proof in the docstring. No other hole is added. The new isomorphism construction and private definitional application lemma contain no sorry.

This is a decomposition, not a net proof: one original hole closes and one strictly lower compatibility hole is added (net zero holes). The lower theorem concerns arbitrary `H` and only the unit/evaluation square; the original theorem additionally transports `h^* f^* G` to `g^* G` and compares both compositions to the pullbacks of `G`. Those additional steps are now kernel-checked proofs, rather than a restatement of the target under another name.

Both modules compile without warnings. Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound` for `pullbackSectionsEquiv`, `pullbackSectionsEquiv_apply`, and `etaleObjectSectionsIso`. The target and the named lower theorem additionally show `sorryAx`, as expected for this decomposition. Scratch copies were removed before delivery.

## No longer needed

Removed the original direct proof import `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition` and its node `lem-weil-pbc-derived-inverse-image-composition` from the item's direct `proof_deps`: the proved source-library sheaf component associativity lemmas suffice, without derived-category coherence.

Removed the main module's import of `Sheaf.Paper.EtaleRestrictionPullbackUnit`. Its node `lem-weil-pbc-etale-restriction-pullback-unit` is no longer a direct dependency of the target proof; it remains the planned input of the new lower theorem, imported there, and is not claimed globally pruned.

Removed the redundant proof import `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its declarations are already exposed by the existing public imports. The other old proof dependencies remain. No whole module is claimed to have left the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker left a partial target proof containing a trailing sorry, added a lower sorry with no node, duplicated its import as public and plain, and changed occurrences of the statement's coefficient abbreviation. The partial proof's `Hbase` and `Happly` did not close any original hole. The claim that the coherence was unavailable was incorrect: the source-library component associativity lemmas finish it. All existing signatures have been restored byte for byte, and the unfinished proof has been replaced by the checked reduction above.

The remaining lower compatibility cannot be obtained merely by applying the restriction theorem: one must construct the cartesian identification, identify two terminal-object maps and the lowerStarComp component, and transport terminal evaluation through the composition comparison. These are the precise remaining steps, recorded in its docstring and node; I did not find a short ready-made lemma for these identifications.

Source check: [Stacks Tag 03CF](https://stacks.math.columbia.edu/tag/03CF) gives localization compatibility, [03EF](https://stacks.math.columbia.edu/tag/03EF) the finite-limit formulation, and [03S2](https://stacks.math.columbia.edu/tag/03S2), the paragraph following Definition 59.70.1, gives the étale restriction formula. The lower compatibility is the unit-side specialization and explicit terminal-evaluation transport, rather than a verbatim statement of any tag.

## Second reading by M3

1. Compared each existing declaration with the repository using the project declaration parser and a text diff. PASS: both existing signatures and docstrings are identical, and the entire `pullbackSectionsEquiv` body is identical. No existing definition or statement changes; no change record is needed. The additional module is new.

2. Compiled both modules locally using only `lcompile.py`, and checked all delivered declarations for forbidden constructs and hollow data. PASS with one explicitly documented lower sorry. Scratch `#print axioms` checks gave the standard three axioms, plus only `sorryAx` for the two theorems that depend on the lower hole. The original theorem's proof body contains no sorry.

3. Read the new compatibility statement and its full docstring proof. PASS as a strictly lower unit/evaluation compatibility statement; the target's additional composition transport is proved separately. In the identity square it specializes to unit/terminal-evaluation naturality with inverse comparisons cancelling; for the zero sheaf both maps are zero; for an empty étale object the terminal/global-section comparison remains valid and no nonemptiness assumption is needed. The cartesian-map equations determine `m` uniquely, including these cases. Independent msearch searches (LeanFinder, Loogle, source grep) and project `rg` found no exact existing statement; LeanSearch was also attempted and recorded as unavailable (Internal Server Error). The restriction-level theorem is an input, not the same terminal-evaluation statement.

4. Read the reduction from the top, replacing the missing coherence by the existing source component lemmas and reproducing only the local naturality argument already available privately upstream. PASS: the original explicit equivalence and lower restriction/unit route are retained. `dag/units/sk-prop-h2.json` was read; its `realized` record is unchanged, and this auxiliary node is not a realized statement or step. The complete old direct dependency removals are listed above; none bypasses a realized unit step.

5. Read both DAG nodes against the Lean declarations. PASS: the new node contains its whole statement, source, full proof steps, dependency union, the required search categories, creation/blueprint/chapter/unit fields, and verbatim Lean signature. The original node now records the actual specialization, naturality, and composition-coherence reduction.

Second-reading changes: restored existing signatures, removed the accidental public and duplicate import, completed the target reduction, repaired compiler warnings, added the missing lower node and updated the original route, checked axioms, and corrected the report to count the result as a decomposition.

## New nodes

`lem-weil-pbc-etale-object-sections-base-change` in `dag/nodes/sec-curve-estimates/` states the lower unit/evaluation comparison for an arbitrary sheaf on `Y`. It isolates the cartesian and terminal-evaluation identifications from the now-proved inverse-image composition transport. It is implemented by the explicit `etaleObjectSectionsIso` and the named open theorem `etaleObjectSections_baseChange`. No change record is required because no existing statement or definition changes.
