## What changed

Replaced the sorry in `AlgebraicGeometry.derivedPullbackComposition_mate_unit` by a
complete transposition argument. A private generic lemma proves the necessary mate
identity from `conjugateEquiv_counit`, naturality and injectivity of the Hom equivalence.
Two proof imports give the two strictly smaller counit calculations. The upper theorem's
signature and its public import are unchanged.

Added `Sheaf.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization`, with a proved
`AlgebraicGeometry.derivedDirectImage_pasted_counit_normalization`. Its private helpers
extract the individual counit equations from the pinned Hom normalization and paste
those equations by naturality. Added
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization` for the remaining
chosen-comparison calculation. It uses the existing `canonicalDerivedPullbackComposition`
API from `SchemeDerivedMateEvaluation` rather than constructing a new comparison.

Added `DerivedCompositionCounitApex`, a concrete morphism definition with a proved
construction equation and an irreducible interface. It introduces no new choice or
proof hole and avoids repeatedly elaborating the large common counit expression.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.derivedPullbackComposition_mate_unit`
(node `lem-sc-derived-pullback-composition-mate-unit`).

Proved the new intermediate declaration:
`AlgebraicGeometry.derivedDirectImage_pasted_counit_normalization`
(node `lem-sc-derived-direct-image-pasted-counit-normalization`).

One new hole remains:
`AlgebraicGeometry.derivedPullbackComposition_counit_normalization`
(node `lem-sc-derived-pullback-composition-counit-normalization`). Its proof is exactly
`:= by sorry`; its docstring gives the full counit, lift-factorization and degreewise
underived-mate calculation. There are no other holes in this delivery.

This is a decomposition: one original hole closed, one smaller hole added, net zero.
The remaining theorem computes only the chosen-comparison side; it does not mention the
pasted derived units or their equality with the mate. The other side is independently
proved, and the upper theorem combines both computations with a proved transposition
argument. No existing definition, signature, or target is changed.

To avoid repeated unfolding of scalar restrictions, the original theorem and the
proved normalization use local irreducibility for the derived units, `Qh` and relevant
adjunction data, and disable lazy projection/weak-head unfolding. Linting is disabled
only on these two large declarations, following the existing composition-unit module;
all declarations are still elaborated and kernel checked. Line lengths and imports
were checked directly.

## No longer needed

Removed redundant public imports of `GlobalHomAdjunctionIso` from the two new
normalization modules and of `HomotopyCategory.Adjunction` from the new apex module.
They remain available through the retained public imports. No module is claimed to have
left the targets' import closure. The direct proof no longer needs the parent plan's K-flat roof/Yoneda
extension, `lem-pc-kflat-resolution` or `lem-pc-kflat-pullback-preservation` as direct
proof dependencies. Their modules remain transitive dependencies of the existing
pullback-composition construction; this is not a claim that they are globally pruned.
The parent node now records the two counit calculations as its direct proof dependencies.
All six former direct dependencies are therefore removed from the parent's direct list:
`lem-pc-ringed-spaces-derived-pullback-composition`, `def-pc-derived-base-change-map`,
`lem-pc-global-hom-adjunction`, `lem-pc-module-pullback-adjunction`,
`lem-pc-kflat-resolution`, and `lem-pc-kflat-pullback-preservation`. The first four
remain used in the lower counit calculations; the final two remain transitive
construction dependencies. No existing import was removed from the item module.

## Where the brief, the DAG or earlier work was wrong

The parent plan extends the Hom formula to arbitrary derived test maps through K-flat
roofs. Evaluating the formula on the underived counit instead computes the inverse
transpose of the recorded right-derived unit directly. Pasting these counit equations
avoids that extension in the present proof. The chosen-comparison side still needs its
underived homotopy compatibility calculation; it has not been silently assumed proved.

The fixed unit `sk-thm-picard-duality` has no realized statement or proof-step nodes for
this item. Its route is unchanged. New statements were checked mathematically on
identity morphisms, zero complexes and empty schemes: only triangle identities,
functoriality and naturality are used, with no invertibility or geometric hypotheses.
The official Stacks pages for Tags 079W, 0D5S and 0D5T were read online. The parent is a
normalization consequence of their constructions, not a verbatim Stacks statement.

`tools/import_direction.py may` crashed with `FileNotFoundError` on the unrelated
repository file `lean/Sheaf/Paper/ModuleCupPullbackResolutionMaps.lean`. No repository
file or tool was changed. The prescribed delivery dry run performs its own import-source
and cycle checks.

## New nodes

`lem-sc-derived-direct-image-pasted-counit-normalization`: the transpose of the pasted
right-derived units is the explicit pasted localized underived counits. Fully proved
from the pinned individual Hom normalization.

`lem-sc-derived-pullback-composition-counit-normalization`: the fixed comparison followed
by the transpose of the composite right-derived unit yields that same explicit
expression. This is the one remaining hole. Neither new statement restates the parent:
one computes each side of its adjunction transpose. The change record
`coord/changes/derived-pullback-composition-mate-proof-scope.md` documents the local
proof-scope commands flagged by the static interface check; no existing mathematical
interface changes and no downstream adaptation is required.

`def-sc-derived-composition-counit-apex`: names the concrete common counit expression;
its construction equation `AlgebraicGeometry.derivedCompositionCounitApex_eq` is proved
by reflexivity.

## Second reading by F4

1. Compared all four delivered modules with the repository. Only the item existed;
   its theorem signature is byte-for-byte identical, including its instance binder
   and chosen comparison. Its sole public import is unchanged. The other three
   modules are new. No existing definition or target statement changes. Verdict: pass.
2. Compiled all four modules in import order with lcompile.py, without errors or
   warnings (19.0, 34.3, 16.7 and 20.8 seconds). Searched the delivered sources for
   prohibited declarations and proof holes: the only hole is the listed public
   counit-normalization theorem, with proof exactly `by sorry`. A scratch module's
   `#print axioms` checks show only propext, Classical.choice and Quot.sound for
   the pasted-unit theorem, apex definition and its construction equation. The
   remaining normalization and original theorem additionally use sorryAx, as
   reported. The apex is an explicit composite; it chooses no arbitrary witness.
   The delivery tool also probes private declarations. Verdict: pass as decomposition,
   not a completed proof independent of sorryAx.
3. Read the remaining theorem against the pinned adjunction Hom formula, the
   selected left-derived-lift equation and the inverse-conjugate underived
   comparison in exists_derivedPullbackComposition. Evaluating the Hom formula
   at the underived counit gives the first equation by the right triangle identity.
   The lift equation and inverse mate counit identity then give the pasted
   expression, with naturality moving the g-counit across epsilon(f). There is no
   counit cancellation or flatness assumption. This reasoning covers identity
   morphisms, zero complexes and empty schemes; arbitrary choices of compatible
   adjunctions do not require strict identity counits. The docstring supplies the
   full mathematical argument. The remaining statement isolates the comparison
   calculation, while the independently kernel-checked pasted-unit calculation
   closes the other side; it is a genuine reduction rather than an application of
   a renamed parent hole. Repeated searches with leanfinder (transpose of composite
   adjunction counit compatible with left-derived composition), loogle
   (`conjugateEquiv_counit_symm`) and grep (`leftDerived_fac_app`,
   `homEquiv_symm_apply`, homotopy counits), plus source searches in lean/Sheaf,
   found generic tools but no existing pinned normalization. The termwise Picard
   counit theorem is specialized to an open-chart model and universe and does not
   directly close this arbitrary homotopy-complex statement. Verdict: pass; closing
   the remaining homotopy comparison requires more than a short local rewrite.
4. Read the upper proof and all private helpers from top downward. The mate
   transposition uses Hom-equivalence injectivity, conjugateEquiv_counit and
   naturality. The pasted-unit proof uses the individual pinned Hom equations,
   composite counit formula and naturality, with no extra geometric hypothesis.
   All imports supply names in signatures or actual proofs, and proof-only imports
   in the item are non-public. Checked the old six proof_deps and completed the
   report's explicit list of removed direct dependencies. The unit's realized
   statement is empty and its only realized step is empty, so no realized node or
   unit route is bypassed. Verdict: pass.
5. Compared node proof steps, proof_deps, proof_origin and Lean records with the
   delivered code. The existing node changes only the three stage-3 proof fields.
   Each new node has its source, searches, creation record, chapter, unit, blueprint
   provenance and Lean declaration. Repaired the pasted-unit node to record its
   use of the selected composition counits, the underived adjunctions and the apex
   construction equation. Checked the apex declaration record against the signature normalized by the
   preflight parser (which omits the `noncomputable` modifier). Verdict: pass after these metadata repairs.

Second reading changed no Lean proof or signature. It completed the pruning report,
corrected the pasted-unit proof dependencies, and added
this independent review. Holes closed: derivedPullbackComposition_mate_unit (one).
Holes added: derivedPullbackComposition_counit_normalization (one). Net zero;
one proved intermediate theorem and one remaining comparison subcalculation.
