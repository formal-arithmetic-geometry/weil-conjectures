## What changed

Restored `lean/Sheaf/Paper/DiagonalOrientationChoiceIndependent.lean` from the
quarantine archive identified by `coord/rework.tsv`, preserving all three public
definitions and the existing theorem signature. Replaced the theorem's hole by a
complete combining proof.

DNC uniqueness identifies the two deltas. A fully proved private category lemma
turns uniqueness of a normalized identification-and-map pair into uniqueness of
the underlying map. Applied to `existsUnique_vectorIntegrationGluing`, it gives
uniqueness of the frame-normalized traces. Congruence of the exceptional adjunction
then identifies the gammas and the two composites.

For the canonical-value assertion, the same trace uniqueness reduces to the
specified vector integration. The new normal-model section normalization identifies
beta with its canonical chart factor; DNC uniqueness fixes delta. The new global
assembly statement then identifies the resulting fixed composite with the specified
orientation. These are separate parts of the source argument and carry no data
chosen from a mere existence theorem.

Added two private proof imports for the new results and an explicit proof import
of the existing vector-integration module. File-local transparency controls match
the dependencies; no limits are raised. The change record is
`coord/changes/S2-diagonal-choice-elaboration-context.md`. The existing node's proof,
proof dependencies and proof origin follow the actual reduction. Its Lean
attachment and statement remain unchanged.

Verification: the full sandbox compilation succeeded for all three modules, with
exit code zero and no warnings. The delivery preflight performs the final checks.

## Proved and sorry left

Closed the existing hole in
`WeilConjectures.PurityFiniteSetting.diagonalOrientationChoiceIndependent`
(node `lem-pur-diagonal-orientation-choice-independent`) by a complete proof from
named statements. The two private helpers
`unique_map_of_unique_normalized_pair` and `normalizedIntegration_unique` are fully
proved. The assigned module has zero remaining holes.

Added two holes, each in its own public theorem and module:

- `WeilConjectures.PurityFiniteSetting.normalModelSectionOrientation`, node
  `lem-pur-normal-model-section-orientation`, in
  `Sheaf.Paper.NormalModelSectionOrientation`.
- `WeilConjectures.PurityFiniteSetting.diagonalDncAssemblyGlobal`, node
  `lem-pur-diagonal-dnc-assembly-global`, in `Sheaf.Paper.DiagonalDncAssemblyGlobal`.

This is a decomposition: one upper hole closed and two separate lower holes added,
not a claim of a net reduction or an axiom-free proof of the target closure. Both
residual theorems have exact statements, source citations and complete proofs in
words. No definition contains `sorry`.

## No longer needed

Removed the private imports `Sheaf.Paper.VectorIntegrationSiteComparison`,
`Sheaf.Paper.PurityDiagonalSectionPasting`, and
`Sheaf.Paper.DegreeZeroDerivedMapGluing` from the assigned module. Their roles in
the global compatibility argument are localized in the residual statement.

The old node's direct proof dependencies on
`lem-pur-diagonal-regular-immersion`, `lem-pur-diagonal-base-change`,
`lem-weil-pbc-finite-type-over-noetherian`, `thm-amb-vector-bundle-purity`,
`lem-pur-vector-integration-site-comparison`, `cor-pur-vector-bundle-purity`,
`lem-pur-diagonal-dnc-chart-normalization`, `lem-pur-diagonal-section-pasting`, and
`lem-pur-degree-zero-derived-map-gluing` are replaced by the actual dependencies.
The ambient vector-purity theorem is not needed for uniqueness of an ordinary
trace: its existing defining gluing theorem suffices. The other comparisons remain
needed by the statements or lower normalization arguments; no whole module or DAG
node is claimed globally obsolete. Removed the unused direct tool approval for
`lem-weil-pbc-finite-type-over-noetherian`; the proof uses the finite-setting API.

No files or declarations are withdrawn. The original quarantine archive and all
attachments remain preserved. The parent's need for this node is retained.

## Where the brief, the DAG or earlier work was wrong

The item was absent because it was quarantined, not because it was withdrawn.
The original timeout did not recur in a comparison compile, so settings alone
would have been an inadequate repair.

The existing integration-gluing theorem uniquely characterizes a pair consisting
of a normalized degree-zero identification and a sheaf map. It does not directly
state uniqueness of arbitrary normalized derived traces. The new private abstract
argument supplies that missing glue using fullness of the single-degree embedding.

The available chart assembly and normal-vector formula have affine hypotheses.
The assigned conclusion has a global domain. Applying the affine formula directly
would add hypotheses, so the canonical-value argument is factored into two genuine
source results: normal-section orientation compatibility with a vector model, and
globalization of the fixed affine assembly. These preserve the unit's diagonal,
DNC and vector-purity route and include rank zero and empty schemes.

## New nodes

`lem-pur-normal-model-section-orientation` isolates the zero-section restriction of
integration-transposed purity under a projection- and zero-preserving vector-bundle
presentation. It concerns a general section pair and has no delta, diagonal alpha,
or two-choice conclusion. Its Noetherian base witness follows from finite type.
The source is the chart proof Step 4 and the vector-model agreement proof Step 3.

`lem-pur-diagonal-dnc-assembly-global` globalizes the fixed canonical three-factor
assembly. It has no alternative traces, gammas or DNC choices. Its source is the
diagonal-dualizing proof Steps 1--2 and the affine restriction-and-gluing argument.
The main proof performs the actual normalization and uniqueness work needed to
reduce arbitrary choices to these specified factors.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
