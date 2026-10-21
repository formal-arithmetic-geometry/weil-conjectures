# Varying-ring operations: proof scopes and cached normalization

## Reason

Complete the four existing proof obligations. Static preflight conservatively flags
new `open`, `variable`, `section` and `attribute` commands, and the elaboration syntax
of `towerPushforwardEvaluation` and `moduleEvalP_existsUnique`. This record documents
those changes. There is no mathematical change to a public definition or statement.

## Old

The module has four holes: `moduleEvalG_exists`, `extension_exact`,
`evalPMate_isIso`, and `evalJInv_isIso`. Its existing private
`towerPushforwardEvaluation` states the unique sectionwise identity comparison using
`SemilinearSections.evaluation` in the two composite functors.

## New

All four proofs are complete. Every public import and all 47 original public
non-theorem declaration bodies are unchanged, checked by source comparison. Every
public signature is unchanged. All public theorem headers remain verbatim
(`moduleEvalP_existsUnique` restored by the reviewer, see below). All new helper
declarations are private and fully proved.

The private `towerPushforwardEvaluation` now specializes the checked conclusion of
`sequencePushforwardEvaluation` using `type_of%`. The two scalar maps are
`eqToHom (evaluation_ring ...).symm`. Thus unfolding
`SemilinearSections.evaluation` gives exactly the former statement, including its
unique isomorphism, all binders and its identity-on-section-carriers predicate.
Its proof is the same pushforward-composition argument. This avoids re-elaborating
the transported carrier normalization. `openEval_exists` uses the same technique.
No new public declaration refers to a private helper in its signature or data body.

The section-carrier predicate of `moduleEvalP_existsUnique` is proved once as the
private, fully proved `moduleEvalP_specialized`. The public theorem keeps its
original header verbatim (with its original `set_option` lines) and is proved by the
term `moduleEvalP_specialized R φ f n`.

Reviewer correction (cc review, 2026-10-21, re-applied on 42de14caa021 after the
first correction was lost at a failed landing): the delivery exported the theorem as
`public alias moduleEvalP_existsUnique := moduleEvalP_specialized`. The alias type is
the `type_of%` of the generic `towerPushforwardEvaluation`, and it contained the
instance `SheafOfModules.systemSequenceEssentiallySmall`. That instance comes from
`Sheaf.CategoryTheory.SystemRingedSequenceSite`, which this module imports only
with a plain `import`, so it is not available to importers. The direct importer
`Sheaf.Paper.FiniteSystemPullbackCoherence` then failed:
`(kernel) unknown constant 'SheafOfModules.systemSequenceEssentiallySmall'`
(line 341, `varyingDirectEvaluation_apply`). The private-constant check did not
catch this because the constant is public in its own module. With the original
header restored, an importer-side environment check finds no public declaration of
this module that uses a constant unavailable to importers.



Proof-only sections introduce the variables and opens needed for coextensions,
open-site pullbacks, finite left extensions, and exact localization. Every added
instance is `private local instance`; the open proof section explicitly reinstalls
its local continuity and invertibility instances after the model section ends.
No helper instance is exported. All added irreducibility attributes are local.
They freeze constructed adjunctions only after their computational identities have
been proved. The general evaluation-continuity instance is temporarily disabled to
avoid its phantom universes and is restored before the namespace closes; the local
fixed-universe instance proves exactly the same continuity property.

## Users

Only `Sheaf.AlgebraicGeometry.VaryingRingOperations` is edited (holder U1).
The private theorem has no external user. Its existing public caller
`moduleEvalP_existsUnique` retains its original signature as validated above, and
compiles against the cached statement. The five direct importers in the current source snapshot are:

- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
- `Sheaf.Paper.FiniteSystemPullbackCoherence`
- `Sheaf.AlgebraicGeometry.VaryingRingTensorComparison`
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`
- `Sheaf.AlgebraicGeometry.VaryingRingTensorSupport`

The additional indirect declaration-name user is
`Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation`. The direct importers
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting` and
`Sheaf.Paper.FiniteSystemPullbackCoherence` also mention
`moduleEvalP_existsUnique` explicitly. A source search finds no other external user
of that name, and no external user of the private `towerPushforwardEvaluation`.

The static source scanner reported removal of `moduleEvalP_existsUnique` because the
delivery wrote it as an alias. The reviewer's correction restores the original
theorem header, so no declaration is withdrawn.

They receive the same original public declarations and imports. No consumer
adaptation is needed or included. No adopted `WeilConjectures` module is changed.
The repair preserves the current repository's narrower public import
`StrictTowerOpenExtension` and its filtered-colimits and concrete-coefficients proof
imports. The proof imports `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
directly for `mateEquiv_whiskerTop_whiskerBottom`, previously supplied through the
larger public import. The former `StrictTowerProperOpenCalculus` import is not needed by these
proofs; its DAG proof references are replaced by the actual single-ring operations
and open-extension nodes. Both `lean_audit` fields, and all other metadata outside
stage-3 ownership, match the current repository.

The two attached node copies update only the proof route, proof dependencies and
proof origin; their statements and Lean attachments are retained.

## Status

landed 20261021T140925-L-2775784 2026-10-21 (merge of deliver/U1/Sheaf.AlgebraicGeometry.VaryingRingOperations)
`lem-pur-system-single-derived-extension` added to the node's proof_deps).

Zero holes remain and zero holes were added. The independent reader should verify
the unchanged public interface, local-only helper instances, and the definitional
equality of the cached private normalization statement. The delivery tool runs the
complete file and its axiom probe before submission.
