## What changed

Replaced the sole sorry in `AlgebraicGeometry.gradedModule_relativeSpec_realization`
by a complete Lean proof assembling two strictly smaller statements. Its signature,
visibility and existing docstring are unchanged. The private proved helper
`AlgebraicGeometry.finitePresentation_of_quasicoherent_finiteType` proves the last
step: obtain coherence from quasi-coherence and finite type, obtain finite sections
on every affine open, apply finite-module finite presentation over its Noetherian
coordinate ring, use the affine finite-presentation criterion, and glue on the
cover of all affine opens. Local Noetherianness of the pullback follows in Lean from
`Algebra.FiniteType.isNoetherianRing` and
`LocallyOfFiniteType.isLocallyNoetherian` for the second projection.

The realization is unpacked once as F, its quasi-coherence, iota, coproduct and
multiplication compatibility. The second lemma proves finite type of that SAME F;
no arbitrary witness is selected in a definition and no replacement F is chosen.
The main proof then retains the original iota and compatibility witnesses.

Added the modules `Sheaf.Paper.GradedModuleQuasicoherentRealization` and
`Sheaf.Paper.GradedModuleRealizationFiniteType`, one statement per module, with
complete source/proof docstrings and matching new DAG nodes. Updated the original
node's proof, proof_deps and proof_origin to match the actual Lean reduction.
All added proof imports in the original module are private imports.

Validation: all three delivery modules compile cleanly through `lcompile.py --all`.
The delivery dry run printed OK, passing preflight except for the intentionally
pending second reading, with nothing pushed.
The main theorem also compiles on its own against the compiled sandbox overlay.
No existing statement or definition, including any target, was changed. No forced
adaptations and no change records are needed. Every Lean line is at most 100 characters.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.gradedModule_relativeSpec_realization`
(node `lem-weil-pbc-graded-module-relative-spec-realization`). There is no sorry
left in the assigned module. Its private finite-presentation helper is proved.

Added exactly two named public theorem holes, each exactly `:= by sorry`:

- `AlgebraicGeometry.gradedModule_quasicoherent_realization`, node
  `lem-weil-pbc-graded-module-quasicoherent-realization`, module
  `Sheaf.Paper.GradedModuleQuasicoherentRealization`.
- `AlgebraicGeometry.gradedModule_realization_isFiniteType`, node
  `lem-weil-pbc-graded-module-realization-finite-type`, module
  `Sheaf.Paper.GradedModuleRealizationFiniteType`.

This is a decomposition: one upper hole closed and two lower holes added, not an
axiom-free proof of the target's closure. The final finite-presentation and
Noetherian steps are proved from existing library declarations. Neither new
statement is the old statement under a new name: the first omits every finite-type,
properness and Noetherian assumption and has no finiteness conclusion; the second
is a property of ANY already given compatible realization and has no existence
conclusion or grading/action laws. The actual original conclusion follows by
combining them with the separately proved Noetherian finite-presentation argument.

## No longer needed

Removed four explicit proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`, node
  `lem-weil-pbc-affine-module-correspondence`.
- `Sheaf.AlgebraicGeometry.AffineModuleFiniteType`, node
  `lem-weil-pbc-affine-module-finite-type`.
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`, node
  `lem-weil-pbc-affine-morphism-relative-spec`.
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`, node
  `lem-weil-pbc-relative-spec-base-change`.

These are no longer direct dependencies of the ASSEMBLY proof; their mathematical
roles remain in the proof plans of the two new nodes. This is not a claim that their
modules have become globally unreachable or that their mathematical work is pruned.
No original proof-plan node is declared unnecessary globally. The unit's statement
and all its realized steps remain untouched. New modules import only what their
signatures require; construction lemmas are recorded in their DAG proof plans.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically consistent, but its cited generic affine module
correspondence does not itself construct the algebra action from the dependent
homogeneous maps. That requires the finite-sum extension and localization/gluing
step stated separately here. Likewise affine finite-type correspondence takes an
algebra-module finite-type hypothesis; it does not supply the argument turning
hfinite and the coproduct into that hypothesis. The second new theorem isolates
precisely that omitted finite-generation glue.

The existing `AlgebraicGeometry.exists_finiteType_graded_module_affine_baseChange`
(module `Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange`, node
`lem-weil-pbc-graded-module-affine-base-change`) was inspected. Its conclusion
only supplies an O_X-linear isomorphism with the coproduct, and does not pin the
B-action or its multiplication square. Its proof text mentions a stronger
algebra-linear construction, but that is not part of its statement and cannot be
used as a theorem. Therefore it does not replace the compatible realization needed
here. No false-statement dispute was found.

Edge cases checked before stating the new lemmas: all G_m zero; empty X (hence
empty pullback); empty local generating family (its span is zero, so every G_m is
locally zero and the coproduct, and therefore F under affine correspondence, is
zero); degree zero and a = 1 (the scalar law supplies the unit law); zero B
(the scalar/unit law forces the summands to be zero). In the second lemma there
is intentionally no internalness or action-law hypothesis: local finite sums and
the supplied multiplication square suffice for finite generation of the already
given module. The same argument does not assert finite presentation without the
Noetherian hypotheses, which are used only in the main theorem.

Mathlib searches ran through msearch.py: LeanFinder returned general
quasi-coherent data/tilde infrastructure for the realization and generator
infrastructure for finite type; Loogle returned finite-presentation implies
finite-type infrastructure; source grep found no graded relative-spectrum
realization. Both LeanSearch queries returned HTTP Internal Server Error, recorded
as unavailable, not as no match. Repository searches included the existing graded
base-change statement. Blueprint searches for `graded module`, `0897` and
`homogeneous module` found no matching statement.

WANTED: the pinned local `literature/stacks-project/coherent.tex`, Tag 0897,
lemma-graded-finiteness, relative-spectrum and finite-type paragraphs. The path
is absent on this machine. The source was read online at
https://stacks.math.columbia.edu/tag/0897 and the finite-presentation equivalences at
https://stacks.math.columbia.edu/tag/01XZ. The detailed split proofs are marked
agent-written explications of those passages, not a claim to have read the pinned
local .tex file.

## New nodes

`lem-weil-pbc-graded-module-quasicoherent-realization`: geometric realization of
the homogeneous algebra action, without finite generators, Noetherianity,
properness or finite type of the algebra. Retains the exact multiplication
compatibility needed downstream, but makes no finite-type or finite-presentation
assertion. Its proof constructs the action on affine direct sums, localizes and
glues, and uses relative Spec base change and affine module correspondence.
Source: Tag 0897, relative-spectrum paragraph, with 01LX and 01SB. Three actual
search kinds are recorded (LeanSearch unavailable). Zero modules, empty schemes
and the unit/scalar edge cases are included.

`lem-weil-pbc-graded-module-realization-finite-type`: homogeneous local generators
imply finite type of any already specified quasi-coherent realization with a
coproduct cocone and the multiplication square. Its proof uses local finite-sum
representatives in the sheaf coproduct, rewrites their homogeneous generation
through the square, and applies the affine finite-type correspondence. No grading
or action-law construction and no existence of F is asserted. Source: Tag 0897's
finite-type paragraph, with 01SB and 01PB. Three actual search kinds are recorded
(LeanSearch unavailable). Empty generators and zero modules are included.

## Second reading by W2

1. **Statements and interfaces.** Compared the delivered relative-realization module with the repository version. The existing target signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, the proof body, and the recorded DAG route differ. The two added public statements are strictly smaller reductions: one supplies quasi-coherent realization without finiteness, and the other supplies finite type for an already specified compatible realization.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; they compile cleanly. The target proof contains no `sorry`, and the only remaining `sorry`s are the two named public split statements, each with its own docstring and DAG node. No forbidden declarations or hollow definitions occur. The finite-presentation helper is a genuine construction-free proof from coherence, affine finite sections, Noetherian finite presentation, and the affine-cover criterion.

3. **New statements and nodes.** Checked both added statements against their Lean signatures, edge cases, source explanations, and node records. Their hypotheses and conclusions are true and exactly the reductions used by the target; neither merely restates the target. Each node records the module, declaration, source, proof plan, dependencies, and searches required by the stage-3 contract. No existing library declaration duplicates either result.

4. **Pruning and imports.** Verified that the four removed proof-only imports are absent from the actual assembly proof and that the replacement imports are used. The new modules expose only imports required by their signatures. The main node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof, while the unit record and its realized route remain unchanged.

5. **Route and delivery checks.** Reviewed the route from the target downward: the realization split is applied first, finite type is proved for the same `F`, and local Noetherian finite presentation closes the target. Ran the stage-3 delivery dry run; after adding this section it is ready to rerun and should classify as CODEX solely because it adds split nodes and public modules.

**Changes made during second reading:** added this review section only. No Lean statement, definition, proof, node statement, or dependency was changed.
