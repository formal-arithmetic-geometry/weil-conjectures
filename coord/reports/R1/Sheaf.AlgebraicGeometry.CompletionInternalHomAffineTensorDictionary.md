## What changed

Completed `AlgebraicGeometry.completion_internal_hom_affine_tensor_dictionary` without changing
its signature or public imports. Constructed the tensor evaluation map with
`TensorProduct.AlgebraTensorModule.lift`, proved its generator equation, conjugated it by the
three Mathlib completion-tensor equivalences, and proved compatibility on ordinary maps using
`AdicCompletion.tensor_map_id_left_eq_map`. The final iff is transported by `LinearEquiv.arrowCongr`.

Added `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation` for the
remaining affine sheaf/quotient/inverse-limit comparison. This completion-only statement takes
a specified completed-ring-linear evaluation map and proves the section identification and
componentwise detection. It neither constructs tensor evaluation nor proves tensor naturality;
those parts are proved in the assigned module. Removed the duplicate private `Scheme.Modules.finiteType_over` helper after the landing
return. A proof-only `import all Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` now exposes
the existing private `Scheme.Modules.isFiniteType_over`, which the finite affine section
helper applies directly. Updated both DAG records to describe these arguments.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.completion_internal_hom_affine_tensor_dictionary`
(node `lem-weil-pbc-completion-internal-hom-affine-tensor-dictionary`). No sorry remains in the
assigned module. Its private finite affine section helper is proved using the existing restriction theorem.

Added one hole:
`AlgebraicGeometry.completion_internal_hom_affine_completion_evaluation`
(node `lem-weil-pbc-completion-internal-hom-affine-completion-evaluation`), the sole theorem of
`Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation`. Its proof is exactly
`:= by sorry`. This is a decomposition: one hole closed, one added, net zero. The algebraic tensor
construction, naturality calculation and equivalence transport are fully proved; the sheaf/limit
comparison remains for the next worker. Dependencies already containing sorry are not new holes.
Both delivered modules compile with no errors or non-sorry warnings.

Edge cases of the remaining statement were checked mathematically: J = the unit ideal gives
zero completions and zero quotient systems; J = zero gives constant systems and ordinary Hom
evaluation; zero F or G gives zero evaluation; a disconnected or empty affine open changes none
of the affine comparisons. The quantification over epsilon is valid because completed H is
generated over completed A by the images of H, so its prescribed generator values determine it.
There is no arbitrary choice of data from a holed mere existence theorem: q is an equivalence
and the transported data are the existential conclusion of the theorem, not a definition.

## No longer needed

Removed from the assigned module these direct proof imports:
`Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient`,
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`,
`Sheaf.AlgebraicGeometry.CoherentSheafHom`, and
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
Their corresponding nodes are no longer direct proof dependencies of the tensor dictionary;
they remain needed by the new completion-only evaluation node. The direct dependencies
`def-weil-affine-spectrum` and `lem-weil-pbc-affine-tilde-gamma-adjunction` likewise move to the
completion comparison. No module is claimed to leave the full target import closure.
Removed the duplicate local finite-type restriction proof.
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` is needed as a proof-only import for its
existing `Scheme.Modules.isFiniteType_over`; it is not pruned.
Kept every original public import and the unit's route unchanged.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing return: the local `Scheme.Modules.finiteType_over` repeated the existing
`Scheme.Modules.isFiniteType_over` word for word. Deleted it and imported and used the existing
theorem, as requested. The dependency node now records that use. No existing library module
was adapted, and no existing signature or visibility changed. The second reading below predates
this repair; its statements about a local restriction proof are superseded by this repair.

The earlier sandbox report named rho/rest theorems that did not exist and included a second
reading that had not occurred. Replaced that report; the independent second reader must supply
their own section. The existing attempted transport had an underdetermined `arrowCongr` scalar
homomorphism, a simplification that did not unfold local equivalences, and a deprecated equivalence
lemma. Added the linear-equivalence type, explicit `change`/`rw` steps, and the current
`Equiv.eq_symm_apply` identity. The original node statements and target signatures were sound
and were not changed. LeanSearch was unavailable; LeanFinder, Loogle, repository and Mathlib
source searches supplied the usable algebraic results and found no existing completion-only
sheaf evaluation theorem.

## New nodes

`lem-weil-pbc-completion-internal-hom-affine-completion-evaluation` records the remaining
completion-only affine section/evaluation comparison, from Stacks Tags 0882 and 087W, with a
complete proof plan and its original affine/quotient dependencies. Its module is
`lean/Sheaf/AlgebraicGeometry/CompletionInternalHomAffineCompletionEvaluation.lean`.
No existing interface changed, no forced adaptation was needed, and no change record is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the repository by diff and checked the complete
   theorem signature: byte-for-byte unchanged, including every hypothesis and conclusion.
   No existing public declaration or definition changed; all new helpers are private proofs.
   Verdict: pass; no change record is needed.
2. Compiled both modules locally in import order through lcompile.py: clean. The assigned
   module has no sorry; the new completion-evaluation theorem is the only added sorry.
   Checked for forbidden declarations and hollow definitions: none. The axiom scratch
   check and delivery probe verify standard axioms plus permitted inherited sorryAx.
   The restriction helper itself uses only propext, Classical.choice and Quot.sound.
   Verdict: pass as a decomposition, not a completed target proof.
3. Read the new statement, docstring and node against Stacks Tags 0882 and 087W.
   Checked J = zero, J = unit, zero F/G, and empty/disconnected affine opens. The given
   epsilon is uniquely determined on completed H by its values on ordinary H, since
   finite H-completion is generated over completed A by those images. Quotient projection
   surjectivity and faithful affine sections justify both directions of detection.
   Independent LeanFinder, Loogle, msearch grep and repository rg searches found completion
   projection lemmas but no existing sheaf evaluation dictionary. The split leaves only
   the sheaf/quotient/limit comparison: tensor evaluation, generator equality, completion
   naturality and conjugation are actual proofs in the original module. Verdict: pass;
   this is a strictly smaller part of the argument, with one new hole and net zero.
4. Read downward from the original target proof and inspected the imported comparison
   declarations. No short existing lemma closes the remaining sheaf comparison. Checked
   public imports against the signature and proof imports against the implemented proof
   or the remaining theorem's documented plan. Removed old direct proof dependencies are
   def-weil-affine-spectrum, lem-weil-pbc-affine-tilde-gamma-adjunction,
   lem-weil-pbc-coherent-formal-modules-affine, lem-weil-pbc-coherent-sheaf-hom-coherent,
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, and
   lem-weil-pbc-completion-internal-hom-quotient. They remain needed by the new comparison
   (affine-spectrum remains a statement dependency). Checked sk-thm-p1.json realized:
   no realization is bypassed or changed. No full-closure module pruning is claimed.
   Verdict: pass.
5. Compared the old and delivered DAG records: existing statement and Lean signature
   unchanged; proof steps and their dependency union agree with the actual reduction.
   The new node has its source, complete plan, searches, creation/blueprint fields and
   verbatim Lean statement. Verdict: pass.

Changed only the remaining theorem's proof explanation and its node to name
AdicCompletion.eval_surjective and remove the unnecessary finite/Noetherian qualification
from projection surjectivity; added independent search records and this review.
No Lean proof or statement needed repair. The remaining sheaf comparison is not a
few-minute closure from the currently available declarations.

## Second reading by R1

Independent review of the repaired delivery on 2026-10-13:

1. Compared the delivered tensor dictionary with the read-only repository using diff,
   and compared the complete theorem signature byte for byte: identical. All existing
   public imports and the existing docstring are unchanged. The only added helper is
   private and proved. No existing definition or statement changed. Verdict: pass.
2. Compiled both delivered modules in import order using lcompile.py: no errors or
   non-sorry warnings. Searched both files for forbidden declarations and hollow data:
   none. A scratch copy with #print axioms shows only propext, Classical.choice and
   Quot.sound for finite_affine_coherent_sections; the original theorem and the new
   completion-evaluation theorem additionally use sorryAx. The only new hole is the
   named completion-evaluation theorem reported above. Verdict: pass as a decomposition
   with net zero holes, not an axiom-free completed target.
3. Read the split theorem, its complete docstring argument, node, and Stacks
   [0882](https://stacks.math.columbia.edu/tag/0882) and
   [087W](https://stacks.math.columbia.edu/tag/087W). Checked zero and unit ideals,
   zero modules, and empty/disconnected affine opens. The completed Hom module is
   generated over the completed ring by ordinary Hom images via the finite-module
   tensor comparison; hence the prescribed epsilon is unique. Quotient projections
   are surjective, so completed-map equality detects all finite-level maps. No
   arbitrary witness from an unproved existence theorem becomes defined data.
   Independent LeanFinder, Loogle and msearch grep searches (recorded in searches.jsonl),
   plus repository searches and reading the original dependency declarations, found
   no independent affine evaluation dictionary. The split removes the tensor-map
   construction, generator calculation and conjugation from the remaining obligation;
   these are real proved steps, not a renamed application of the original theorem.
   Verdict: pass; the remaining comparison is not a few-minute closure.
4. Read the original proof from its conclusion through beta, epsilon and the transport
   equivalences. The construction uses the direct Mathlib tensor lift and completion
   naturality; no shorter available route closes the sheaf comparison. The repaired
   proof correctly reuses the existing private isFiniteType_over via proof-only import
   all, rather than duplicating it. Proof imports and split-module imports match their
   actual uses or documented remaining proof. Checked the six old proof dependencies
   removed against No longer needed and checked sk-thm-p1.json realized: the unit route
   is preserved, and no full-closure module pruning is claimed. Verdict: pass.
5. Compared both node records with their Lean signatures and proof steps. Both stored
   signatures occur verbatim in the Lean files; proof_deps is exactly the union of the
   step uses. The existing node changes only proof, proof_deps and proof_origin. The
   new node has source, complete argument, searches, creation, blueprint, chapter, unit
   and Lean fields. Verdict: pass.

Changed only this report by adding the independent second reading of the repaired
version. No Lean or node repair was needed. Removed the temporary axiom-probe copy.
