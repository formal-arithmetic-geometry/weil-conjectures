## What changed

Completed the proof of `rawModuleAbelianHomMap_naturality` from two expansion formulas and the existing `rawModuleScalar_coefficient_square`. Added three modules: a concrete source-prefix definition, a module-side source expansion, and an abelian-side expansion. The original theorem signature and every existing definition are unchanged. Its two new imports are proof-only.

The common prefix is constructed by categorical composition and derived scalar forgetting; no data are chosen from an unproved existence theorem. The two expansion statements leave different coefficient tails, and the existing coefficient square is necessary to identify them. Neither expansion restates the original naturality conclusion.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_naturality` (1 original hole).

Added: `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_source_formula` (`lem-sbc-raw-module-abelian-hom-source-formula`) and `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_target_formula` (`lem-sbc-raw-module-abelian-hom-target-formula`). Each has exactly `:= by sorry` and a full proof in its docstring. There are no other new holes. This is a decomposition: 1 hole closed, 2 holes added, net -1 before downstream pruning. The existing coefficient-square prerequisite retains its own pre-existing holes outside this delivery.

`rawModuleScalarSourcePrefix` is an explicit, sorry-free construction.

The edge cases checked structurally are zero class, zero coefficient, identity arrow, empty test object and q = 0: the same functoriality and naturality equations apply, with no cancellation of the scalar Hom map and no positive-degree or nonempty assumption.

## No longer needed

No modules pruned. No original import was removed. Removed from the direct `proof_deps`: `lem-weil-pbc-inverse-image-composition`; it remains used transitively through the sheaf-composition calculation and is not pruned. The former direct inverse-image-composition proof dependency is replaced by the expansion statements and coefficient square; inverse-image composition is still needed transitively and is not claimed as pruned. All imports of the delivered modules are required by their statements or proof.

## Where the brief, the DAG or earlier work was wrong

The source-square and coefficient-square APIs cannot currently be imported together: they both declare `AlgebraicGeometry.Etale.RawModuleScalarComparison.derivedPullbackIso`. Likewise `RawModuleScalarMapFormula` duplicates `scalarSourceFactor` and `scalarCoefficientFactor` from the canonical factor modules. A direct route through those statements therefore fails at import loading. The new source expansion instead specifies the route through `rawModuleScalar_sheaf_composition` and `Functor.plus_single_source_square_core`, without importing the conflicting concrete source-square module. The target expansion uses only definitions and `rawModuleScalar_pullback_abelian_formula`.

An attempted direct proof exposed expensive definitional checks in the existing nested additive scalar-map construction. Experimental edits to unclaimed modules were discarded because the forced-adaptation rule did not authorize changing them. No edits to existing dependency modules, adaptations, or change records remain in this delivery.

## New nodes

`def-sbc-raw-module-scalar-source-prefix`: concrete source comparison followed by the image of the scalar source factor composed with the derived class; module `RawModuleScalarSourcePrefix`.

`lem-sbc-raw-module-abelian-hom-source-formula`: module-side source/class coherence with the coefficient tail retained; module `RawModuleAbelianHomSourceFormula`.

`lem-sbc-raw-module-abelian-hom-target-formula`: abelian raw pullback expansion with the scalar coefficient separated; module `RawModuleAbelianHomTargetFormula`.

## Second reading by T3

1. Compared all four delivered modules against the repository. Only the naturality module
already exists. Its complete theorem signature is byte-for-byte identical, and its only
other edits are proof-local transparency and proof-only imports. The existing node differs
only in `proof`, `proof_deps`, and `proof_origin`. No existing definition or target changes.
Verdict: pass.

2. Read the composition proof and the explicit source-prefix construction. There is no
arbitrary witness selection in the prefix, no data hole, and no forbidden declaration.
Final compilation and axiom-probe results are recorded below.

3. Read both expansion statements and their full docstring arguments against the source,
class, and coefficient factors. The source expansion retains the module coefficient tail;
the target expansion retains the abelian tail. The existing coefficient-square theorem is
still necessary to connect them, so neither restates naturality. Checked zero class, zero
ring/coefficient, identity arrow, degree zero, and empty test-object cases: none of the
arguments cancels a class or assumes a nonzero object, positive degree, or bijective Hom
map. Independent msearch queries used `NatTrans.naturality` (loogle), natural-isomorphism
naturality and composition (leanfinder), and `map_comp|naturality_assoc` (grep). Direct rg
of the project and upstream sources found the generic coherence results and known
factorizations, but no already stated expansion with this concrete prefix. The reported
source/coefficient import-name conflict is visible in the source. Verdict: pass.

4. Checked the top-level transitivity argument and the old dependency list. No original
import is removed; inverse-image composition is replaced as a direct proof dependency but
retained transitively. Read `dag/units/sk-lem-failure-field.json`: this is a subordinate
raw-comparison calculation, and the unit's statement, steps and existing `realized` fields
are unchanged. Added the source expansion's planned prerequisites as proof-only imports.
Verdict: route preserved.

5. Checked all new nodes' statements, Lean records, provenance, three search kinds, and
blueprint/unit linkage. The existing node's proof steps and dependency union match the
three equalities used in Lean. The new source-prefix node describes actual composition.
Verdict: pass, subject to the final compiler and preflight checks below.

Changes in this second reading: normalized spacing to preserve the existing signature
exactly; added proof-only imports of the source expansion's planned module-pullback,
sheaf-composition and generic source-square prerequisites; attempted to close the elementary
abelian expansion without changing its statement.

The abelian expansion remains a named hole. Its structural computation reduced to
functoriality, but rewriting through the existing instance-heavy scalar Hom construction
requires transparency that exceeded the single-file limit. Reverted all attempted proof
code; no compiler error or partial proof remains. The second reading adds its planned
abelian-pullback formula as a proof-only import. The final result remains the reported
decomposition: one original hole closed and two strictly smaller holes added (net -1
before any global pruning). No changes to unclaimed definitions were made.

Final verification: all four delivered modules compiled without errors or warnings,
each in 15.7–17.9 seconds. A scratch copy with `#print axioms` for all four declarations
compiled successfully. `rawModuleScalarSourcePrefix` uses exactly `propext`,
`Classical.choice`, and `Quot.sound`; the two expansion lemmas and naturality use only
those plus `sorryAx`, as expected for the reported decomposition and existing open
prerequisites. The scratch copy was removed. Point 2 verdict: pass for a decomposition,
not an axiom-free proof. The dependency unions and existence of every referenced node
were also checked. Point 5 verdict: pass.
