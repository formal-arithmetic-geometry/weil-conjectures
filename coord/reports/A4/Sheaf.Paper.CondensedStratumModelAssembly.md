## What changed

`Sheaf.Paper.CondensedStratumModelAssembly` now performs well-founded induction on
`TopologicalSpace.Closeds T`, proving models for pullbacks along all closed immersions
with image in the current support. It specializes the result to the identity immersion
and uses `profinitePointModuleIdentity` to recover the original module.

The new proof-only module `Sheaf.Paper.CondensedStratumModelInductionStep` states the
remaining geometric step, with models on every **strictly smaller** closed support as
an explicit hypothesis. Its source-based docstring details the empty case, open-stratum
model, proper closed complement, localization extension, and finite-stage descent of the
extension class. The original target signature and public imports are unchanged.
No existing definition, theorem signature, or other group's module was changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_model_of_stratum_models`
(node `lem-weil-pbc-condensed-stratum-model-assembly`) now has a complete Lean induction proof.

Hole added and left: `AlgebraicGeometry.ProEtale.exists_finiteCoefficient_model_on_closed_support_step`
(node `lem-weil-pbc-condensed-stratum-model-induction-step`) has proof exactly `by sorry`.
There are no other delivered holes. This is a decomposition: one upper hole closed and
one strictly smaller geometric induction-step hole added, net zero holes closed. Neither
the target nor the new step is axiom-closed: their axiom probes report exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the recorded open step.
No definition chooses arbitrary data from an unproved existence theorem.

## No longer needed

No modules or lower route nodes are pruned from the import closure. The previous claim
that the geometric route was no longer needed was incorrect: its imports and complete
proof-dependency plan are retained on the new open step.

The assembly file removes these direct proof-only imports, which now belong to the step:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.CondensedSheafExtContinuity`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`

The following old `proof_deps` are no longer used **directly** by the assembly proof;
all remain in the new step's dependency plan, so none is claimed globally unnecessary:

- `def-constructible-stratification`
- `def-weil-closed-immersion`
- `def-weil-finite-subextension-directed-set`
- `def-weil-pbc-condensed-e-module-category`
- `def-weil-pbc-proetale-covering`
- `def-weil-proetale-inverse-image`
- `lem-sc-derived-adjunction-from-underived`
- `lem-sc-noetherian-finite-irreducible-components`
- `lem-weil-pbc-closed-subset-closed-subscheme`
- `lem-weil-pbc-condensed-constructible-serre`
- `lem-weil-pbc-condensed-sheaf-ext-continuity`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-ext-one-extension-classification`
- `lem-weil-pbc-finite-dimensional-linear-homeomorphism`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-proetale-ringed-open-closed`

`lem-weil-pbc-profinite-point-pullback` is retained directly for the final identity
comparison. The assembly's only other direct proof dependency is the new step node.

## Where the brief, the DAG or earlier work was wrong

The first worker's unconditional theorem on all closed supports transferred the whole
assembly problem to a stronger statement. Specializing that theorem at the identity
was not a genuine reduction. The second reader rejected that split and replaced it by
a conditional **one-step** theorem, with the well-founded induction performed in Lean
in the original target. The old new module/node were never landed and are not delivered.

The earlier report called this a proved target and claimed geometric dependencies were
pruned. Both claims overstated progress; the corrected report records a decomposition
with net zero hole reduction and no pruning. The alleged earlier timeout is not evidence
of a needed definition change: the repaired delivered modules compile within the limit.

## New nodes

`lem-weil-pbc-condensed-stratum-model-induction-step` records the geometric inductive step.
It assumes models on all strictly smaller closed supports, uses those models only for
the proper closed complement of a nonempty open piece, and supplies the model on the
current closed subscheme. The original detailed assembly plan is retained on this node;
its source, all dependency fields, three real Mathlib searches, creation metadata, and
verbatim Lean statement are recorded. LeanSearch was also attempted and returned an
Internal Server Error, recorded without a verdict. The Mathlib results supply the standard
well-foundedness instance, not the coefficient-descent step.

No change record is needed: every existing signature, definition, and public import is
unchanged. The new statement replaces only an undelivered new statement.

## Second reading by A4

1. **Visible interfaces — pass after repair.** Diffed every delivered module against the
   repository (the step is new) and separately checked the existing theorem signature
   byte for byte. The only existing declaration keeps exactly its hypotheses and conclusion;
   its three public imports are identical. All other import changes are proof-only. No
   changes to another group's module or to definitions are delivered.

2. **Proof and axioms — pass with the declared open step.** Both delivered modules compile
   in import order using `lcompile.py`. The assembly proof is actual well-founded induction,
   not merely application of the old unconditional stronger theorem. A scratch axiom audit
   reports only the three allowed foundational axioms plus `sorryAx` for the recorded step.
   A source scan finds exactly one named `sorry` and no forbidden declarations or attributes.
   There are no new definitions or arbitrary data choices.

3. **Split statement — repaired.** Removed the unconditional support theorem, which moved
   rather than reduced the problem. The replacement has the strictly smaller-support
   induction hypothesis. Checked the empty support/empty scheme, empty stratification,
   identity immersion/full support, support larger than the image, and nonreduced strata:
   empty support forces empty source; a nonempty chosen open forces the complement's image
   strictly below D even if range(i) is properly smaller than D; a surjective closed
   immersion over the chosen open is handled by localization, not asserted to be an
   isomorphism of schemes. Its complete docstring records how each case is handled.
   Searched Mathlib with new leanfinder, loogle, and grep queries and searched `lean/Sheaf`
   and `lean/WeilConjectures` using coefficient, closed-support, stratum-model and induction
   terminology. The existing parent finite-presentation descent theorem imports this item
   and therefore cannot be used to prove it; no independent duplicate step was found.
   The remaining step includes substantial geometry and extension-class descent and cannot
   be closed by a short existing lemma found in those searches.

4. **Top-down proof and pruning — pass after correction.** The Mathlib well-foundedness
   instance supplies the induction directly; the existing profinite-point identity
   comparison supplies the final isomorphism. The remaining hole is one inductive step,
   with recursive subproblems as assumptions. Restored the lower geometric dependency
   imports and corrected `No longer needed` above; none is falsely counted as pruned.
   The unit `sk-thm-properbasechange` has the same `realized` statement and steps: this
   coefficient-model tool is below that unit route, and no unit realization is bypassed.

5. **DAG — pass after repair.** The assembly node now records well-founded induction and
   identity specialization and cites exactly the step and profinite-point nodes. The new
   step node carries the original geometric proof plan, the explicit smaller-support
   premise, its complete dependency union and source, and its verbatim Lean signature.
   Existing node edits are limited to `proof`, `proof_deps`, and `proof_origin`. There
   is no circular proof dependency and no unrecorded statement change.

Changed during second reading: replaced the unsupported whole-problem generalization
with an explicit induction step; wrote the actual well-founded induction in the target;
expanded the step's source proof; restored its dependency imports; replaced its new node;
and corrected the report's proof, axiom, and pruning claims. The preliminary audit added
before the whole-problem split was recognized has been replaced by this final reading.
