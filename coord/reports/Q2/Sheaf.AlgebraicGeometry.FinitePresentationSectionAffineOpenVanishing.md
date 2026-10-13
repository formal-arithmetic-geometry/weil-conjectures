## What changed
The target `AlgebraicGeometry.finitePresentation_section_affine_open_eventually_zero`
now has a complete proof combining one-stage detection with persistence at later stages.
Added two proof imports and two modules:
`Sheaf.AlgebraicGeometry.AffineSectionZeroAtStage` and
`Sheaf.AlgebraicGeometry.SectionBaseChangeZeroPersists`.
The latter is proved, including its private `unit_zero_comp` helper.
The former isolates the affine-limit detection step, without finite presentation
and without the conclusion about all later stages. Existing signatures and the original module's public
imports are unchanged. The second reader removed the unused public import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` from the new persistence module. No module data is chosen from an unproved existence statement.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.finitePresentation_section_affine_open_eventually_zero`.
Proved `AlgebraicGeometry.section_baseChange_zero_persists` and its private
`AlgebraicGeometry.unit_zero_comp` helper.
Added one hole:
`AlgebraicGeometry.section_affine_open_zero_at_stage`
(node `lem-pc-affine-section-zero-at-stage`). This is a decomposition, not an
axiom-free proof of the target: one original hole closed and one smaller hole added.
The new hole asserts only detection at one stage, while the proved persistence
lemma has no limit, quasi-coherence, affine-open or finite-presentation hypothesis.

## No longer needed
No original imports removed and no modules pruned. Removed the unused
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` import from the new
`SectionBaseChangeZeroPersists` module. The six original proof dependencies
remain beneath the detection lemma. The new propagation proof uses existing
pullback-adjunction and base-change interfaces and Mathlib adjunction uniqueness.
No finite-matrix construction or finite-presentation descent lemma is imported.

## Where the brief, the DAG or earlier work was wrong
The original module had none of its DAG proof-dependency imports. Three dependency
nodes have no direct `lean` record (affine permanence, Spec/colimit comparison and
conjugate unit equation); their mathematical content is provided by existing
Mathlib and library interfaces. Their missing attachment did not prevent stating
and compiling the reduction. The literature paths in the node are not present
in this read-only checkout; the detection proof follows the existing node's
source and argument. No statement defect was identified. The unit record's
`realized` lists are empty, and the existing affine-limit route is retained.

## New nodes
`lem-pc-affine-section-zero-at-stage`: one-stage detection for a quasi-coherent
module section. It isolates the affine ring-colimit and pure-tensor comparison
argument and has the sole new sorry. Empty affines and zero modules cause no
exception; singleton and nonskeletal directed preorders are included.

`lem-pc-section-base-change-zero-persists`: persistence for arbitrary modules
and opens under further base changes. It is proved using composition of
adjunctions and uniqueness of left adjoints, and is independent of inverse limits.
Its edge cases are the identity transition and zero sections, both covered by
linearity and the same unit equation. No change record is required.


## Second reading by Q2

1. Compared the original module with the repository using diff and checked its
   existing theorem signature byte for byte: identical. Its only changes are two
   plain proof imports and the proof body. No definitions or existing visibility
   changed. The existing node differs only in proof, proof_deps and proof_origin.
   Verdict: pass; no change record or forced adaptation is required.
2. Compiled all three modules with lcompile.py. Scratch-copy #print axioms checks
   show only propext, Classical.choice and Quot.sound for unit_zero_comp and
   section_baseChange_zero_persists. The detection theorem and original target
   additionally use sorryAx. There is exactly one delivered sorry, the named
   section_affine_open_zero_at_stage, and no forbidden declaration or hollow
   definition. The chosen intermediate adjunction comes from a proved theorem
   and is for fixed functors; no module or arbitrary existence witness is chosen.
   Verdict: pass as a decomposition, not a completed axiom-free target proof.
3. Read the new statements and the full natural-language proof of the remaining
   hole. Affine charts reduce detection to scalar extension and the directed
   colimit zero criterion, without any finite-presentation requirement. Empty
   opens and zero modules give zero section groups; a singleton index has an
   isomorphic limit projection and its unit reflects zero. Preorder proof
   witnesses are irrelevant, and the supplied i and j ensure nonemptiness.
   Arbitrary adjunctions compare by the left-adjoint uniqueness equation.
   Persistence is a distinct, fully proved step with no limit or coherence
   assumption; detection omits the later-stage universal conclusion. Thus this
   is a strict separation of detection and propagation, not a renamed restatement.
   Independent leanfinder, loogle and grep searches (logged in searches.jsonl)
   and local library searches found structure-sheaf vanishing and the more
   elaborate valuation_limit_qcoh_section_descent interface, but no directly
   applicable arbitrary-module theorem. Checked the cited Stacks 01ZR and 05LI
   online; 05LI(1) applied to a map from the rank-one free module gives the
   one-element algebraic argument. Verdict: pass; closing the remaining hole
   requires the nontrivial affine chart and colimit comparisons.
4. Read the proof top down and the existing dependency declarations and unit
   sk-thm-picard-semicon. The target combines detection with independently proved
   propagation, using Mathlib's unit_leftAdjointUniq_hom_app directly for the
   latter. The unit's realized lists are empty; no realized node or unit route
   is bypassed. The six old dependencies remain under detection:
   lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-conjugate-iso-unit-equation,
   lem-weil-pbc-directed-colimit-base-change-elementwise,
   lem-weil-pbc-module-pullback-affine-sections,
   lem-weil-pbc-scheme-over-limit, and lem-weil-pbc-spec-colimit-limit.
   None is globally no longer needed and no module is claimed pruned.
   Removed the unused Quasicoherent import from the new persistence module;
   its remaining public imports provide its signature and its plain adjunction
   import provides its proof. Verdict: pass after this import repair.
5. Checked all three nodes against their Lean declarations and proof routes;
   each proof_deps equals the union of its proof steps' uses. New nodes have
   source, proof, searches, creation, blueprint, chapter/unit and verbatim Lean
   signature records. Added the missing module-pullback definition dependency
   to the persistence node's statement dependencies. Verdict: pass after this
   metadata repair.

Second-reading changes: removed one unused public import from the new persistence
module, completed its statement-dependency metadata, and documented the independent
review. No Lean theorem statement or proof was changed. One original hole is
closed and one strictly smaller hole added; the net is zero, with no modules pruned.
