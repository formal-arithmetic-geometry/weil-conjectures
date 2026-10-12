## What changed

Replaced the proof hole in `lean/Sheaf/AlgebraicGeometry/AffineSectionLocalization.lean`
with `exact exists_sectionFraction_nonvanishing_equiv Y L s F`.
The existing general theorem specializes to the affine scheme without any conversion:
Mathlib infers `CompactSpace Y` and `QuasiSeparatedSpace Y` from `IsAffine Y`.
The declaration signature, visibility, docstring, and imports are unchanged.
The existing node's two-step route is realized exactly, so no node update is needed.
The general localization theorem is the already-approved tool use from the Picard-duality unit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.affine_section_localization`
(node `lem-sc-affine-section-localization`).
No sorry remains in the item, and no holes were added or split off.
The proof uses the existing general localization theorem and its dependencies;
this delivery does not claim to close their entire transitive axiom closure.

Local compilation with the prescribed launcher succeeded without warnings.
The theorem preserves the nonvanishing-open equality, additive equivalence,
restricted-scalar compatibility, and fraction tensor formula verbatim.
Both affine qcqs instance declarations were read in Mathlib and inferred by the compiler.
LeanFinder returned basic-open structure-ring localization and tilde-module results,
which do not replace the general invertible-module statement. Repository search found
`exists_sectionFraction_nonvanishing_equiv` as the exact general result.

## No longer needed

None. All imports remain: the three public imports provide statement vocabulary,
and `Sheaf.AlgebraicGeometry.InvertibleSectionLocalization` supplies the proof.
Both existing proof dependencies are used:
`lem-weil-pbc-affine-scheme-qcqs` via Mathlib instances, and
`lem-sc-p1-invertible-section-localization` via the general theorem.
No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The DAG's specialization proof works as written. No definitions, statements,
unit routes, or other modules were changed.

## Second reading by E4

1. Compared the delivered module with the repository version. The theorem signature,
visibility, docstring, and imports are unchanged; only the proof body replaces `sorry`.
Verdict: pass.

2. Compiled the module with the prescribed launcher. The proof has no local `sorry`,
axiom declaration, unsafe feature, or hollow definition. The remaining `sorryAx` in an
axiom print comes only from the imported general localization theorem still open below
this item. Verdict: pass.

3. Checked the proof against existing declarations and searched for alternatives. The
specialization `exists_sectionFraction_nonvanishing_equiv Y L s F` has exactly the target
type, while no Mathlib or upstream declaration duplicates this affine statement. Verdict:
pass; no statements were split off.

4. The route specializes the existing quasi-compact, quasi-separated localization theorem,
with affine instances inferred by `IsAffine Y`; it keeps both DAG proof dependencies and
all imports remain necessary. Verdict: pass; nothing was pruned.

5. The existing node's `proof`, `proof_deps`, and `proof_origin` agree with the proof,
and the unit route is unchanged. Verdict: pass.

Changed only the proof body and added this second-reading record; no definitions,
statements, nodes, or imports were changed.
