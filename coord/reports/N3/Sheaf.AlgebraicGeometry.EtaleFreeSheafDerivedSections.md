## What changed

Completed the existing sandbox proof of
`AlgebraicGeometry.Scheme.nonempty_freeSheafDerivedSectionsIso` in
`Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections`, preserving its signature and
existing docstring. The proof identifies shifted bounded-below derived Hom with Ext,
computes Ext on an injective resolution, explicitly identifies its Hom complex with
terminal sections, and compares classical right derived sections with the unbounded
cohomology functor. Private, fully proved sections-comparison helpers establish the needed naturality,
using existing generic postcomposition helpers from
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`.
The terminal-section comparison is additive, and exact forgetting of module structure
commutes with homology. No arbitrary data is selected from an unproved existence theorem.

Repaired the earlier attempt's `Functor.preimage_map` argument and the naturality proof
for the inclusion's shift isomorphism. Explicitly omitted unused section instances.
The repaired module compiles cleanly through lcompile.py. The proof uses the injective Ext,
Ext naturality, and PlusCompatibility APIs already available through the retained
public CohomologyPresheaf import; redundant added direct imports were removed by
the second reading.
The node's proof and proof dependencies now describe this implemented route.
The required record for scoped private-helper context commands is
`coord/changes/free-sheaf-derived-sections-private-context.md`; downstream signatures
and calls require no adaptation.

Return repair (reviewer X-8f30d, head 8f30d9b30): added the proof-only
`import all Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` so its private
generic helpers are available without exporting them. Deleted both original
`FreeSheafComparisonAux` generic helper blocks, including the three flagged duplicate
lemmas. All uses now refer to `EtaleComparisonAux.postMap`, `postClass`,
`homologyClass_naturality`, and `extClass_naturality`. This reuses the existing
proofs directly; no theorem was renamed or restated. The public signature and
all existing public imports remain unchanged. Updated the DAG dependency and
proof description and the private-context change record accordingly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.nonempty_freeSheafDerivedSectionsIso`
(node `lem-weil-pbc-free-sheaf-derived-sections`).
No holes remain in this module; no holes or new theorem modules were added.
This is a proof, not a decomposition. All auxiliary definitions have explicit
constructions and all auxiliary lemmas are proved. Standard injective resolutions
and the library's existing derived-functor comparison are reused.

## No longer needed

Removed the direct import `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` and
its planned dependency `lem-weil-pbc-module-sheaves-enough-injectives`.
The required EnoughInjectives instance for the actual ModuleCat-valued sheaf category
is already inferred from the retained library imports; the removed theorem concerns
SheafOfModules over a constant ring sheaf and abelian sheaves instead.
The module `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian` is therefore
also not needed through that removed import. These modules may remain needed elsewhere.

Removed the direct `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
import because the used PlusCompatibility module already publicly imports it.
Its node `lem-sp-derived-functor-single-identification` remains needed and retained.
Removed the separate planned dependency `lem-weil-pbc-homotopic-maps-equal-cohomology`:
naturality of all comparison maps is proved with a common injective-resolution lift,
using the existing Ext and right-derived naturality APIs. Their internal homotopy theory
remains in Mathlib; no claim is made to prune it globally.

Retained `lem-weil-pbc-bounded-below-injectives-kinjective`,
`lem-weil-pbc-kinjective-hom-derived`, and `lem-weil-pbc-sheaf-free-separator` as the
mathematical ingredients realized by the existing Ext and free-sheaf APIs.
The second reading also removed the redundant direct proof-only imports
`Mathlib.CategoryTheory.Abelian.Injective.Ext`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
Their declarations remain used through the retained public import, so this cleanup
does not prune their mathematical ingredients.

The duplicated private declarations `FreeSheafComparisonAux.postMap`,
`postCocycle`, `postClass`, `postClass_mk`, `postHomologyData`,
`homologyClass_naturality`, and `extClass_naturality` are no longer needed here.
The existing versions in `EtaleComparisonAux` are reused through the new
proof-only import; its node `lem-weil-pbc-sheafH-ext-derived-comparison` is retained
as an actual proof dependency. No claim is made to prune that module.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had no report or node update and did not compile:
`Functor.preimage_map` has one explicit morphism argument, and the shift comparison's
naturality needs explicit reduction of the additive-equivalence application followed
by the commShiftIso naturality equation. These are repaired.

No statement correction was needed. The node is below the unit's realized theorem;
the fixed unit route is preserved. The proof imposes no extra hypotheses on the scheme
or ring and works uniformly at q = 0, for the zero ring, and for the empty scheme.
The search found existing Mathlib injective Ext computations, but no one-step theorem
for this module-coefficient free-sheaf comparison. The nearby abelian sheaf comparison supplies exactly the generic postcomposition
constructions and naturality lemmas needed here; its final abelian-sheaf theorem
does not replace the module-coefficient comparison.

The returned delivery duplicated three generic naturality statements already
proved in the abelian-sheaf comparison module. The landing rejection was correct.
Lean module-system `import all` permits direct reuse of these private declarations
within the repaired proof, and avoids any visibility change or adaptation of the
existing module. The previous second-reading section was removed because it
validated the superseded delivery; the next reader must review this repair.

## Second reading by N3

1. **Statements and interfaces.** Compared the delivered module with the repository version. The
   target declaration and all existing declaration signatures are unchanged byte for byte; only
   proof code and proof-only imports differ. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds with no warnings. The
   file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof
   constructs the comparison isomorphisms explicitly and selects no data from an undetermined
   existence theorem. A scratch-copy `#print axioms` of the public theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.
3. **Split statements and dependencies.** No split-off statements or new theorem modules were
   added. The DAG node records the implemented route and its actual dependencies, including the
   reused `EtaleComparisonAux` declarations. Verdict: pass.
4. **Pruning and route.** Verified the removed imports are not needed by the proof, including the redundant
   injective-Ext, exact-sequence, PlusSingle, and PlusCompatibility imports. The terminal free-sheaf
   adjunction, injective-resolution Ext computation, and derived-functor compatibility route remain
   present, so the unit route and realized steps are preserved. Verdict: pass.
5. **DAG agreement.** Checked the node's statement, proof steps, `proof_deps`, and `proof_origin`
   against the Lean proof. They agree; no node or change record requires alteration. Verdict: pass.

Changed only this review record after the prior repair: no Lean declarations, statements, or DAG
content were changed.
