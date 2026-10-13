## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFlatOver_opcycles_zero_of_quasiIso` in
`Sheaf.AlgebraicGeometry.FlatModelOpcyclesFlat`, with its original signature and visibility.
Added four proved private helpers: `module_opcycles_flat`, `free_stalk_flat`,
`stalk_preserves_homology`, and `affine_sections_flat_of_flat_stalks`.
The proof follows the stalkwise Tag 0653 argument. It uses the already proved generic
source FlatModel declarations to compare ordinary tensor with derived tensor and to
apply the categorical flat-opcycles criterion. This avoids transport to the one-point
site. The affine return is proved using tensor localization presentations, the existing
stalk tensor equivalence, and Mathlib's maximal-ideal criterion. All new imports are
proof imports. Updated the item's node proof and proof dependencies to this route.
No definitions, public interfaces, target statements, or other modules changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.isFlatOver_opcycles_zero_of_quasiIso`
(node `lem-pc-flat-model-opcycles-flat-zero`).
All four private helpers are fully proved. There are no `sorry` declarations left in
the item, and no holes or new modules were added. This is one hole closed, zero added,
not a decomposition. The proof uses existing library dependencies rather than proving
their statements again.

Validation: the full module compiles through lcompile.py without errors or warnings.
Edge cases remain included: empty scheme, empty affine open, zero ring, rank zero,
zero complex, and d = 0; no nontriviality or nonemptiness hypothesis was introduced.
The maximal-ideal criterion handles a coordinate ring with no maximal ideals, and the
stalk arguments quantify over points without choosing a point of the scheme.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`

The wrapper nodes `lem-pc-module-flat-opcycles-tor-criterion`,
`lem-pc-module-bounded-flat-kflat`, and `lem-pc-kflat-tensor-quasi-iso` are not
proof dependencies of this item anymore: their mathematical roles are supplied by
proved generic source declarations. In particular no K-flat resolution or
one-point-site equivalence is required by this proof. The filtered-colimit node
`lem-weil-pbc-filtered-colimit-flat-modules` is no longer a direct dependency;
it remains needed inside `lem-pc-affine-flat-module-stalk-flat`, so this delivery
does not claim to remove it from the target closure. Every remaining direct proof
import supplies a used declaration or a required category/flat-resolution instance.
No unit-level step was bypassed; the unit record has no realized node for this item.

## Where the brief, the DAG or earlier work was wrong

The original plan asks for a one-point-site transport between the module formulation
and `kFlat_tensor_quasiIso`. This transport is unnecessary: the source library already
proves `DerivedCategory.torAmplitudeIn_Q_obj_of_flat`,
`DerivedCategory.QObjTensorSingleFunctorObjIso`, and
`ObjectProperty.flat_opcycles_of_exactAt`, and `ModuleCat.flat_iff_flat` bridges
categorical flatness and `Module.Flat`. The statement itself is unchanged and no
mathematical error is asserted. The existing docstring's module Tor criterion is
implemented through this proved categorical criterion.

## Second reading by H3

1. Compared the delivered module with the repository version. The public theorem signature and visibility are byte-for-byte unchanged; only proof imports, private helpers, and the proof body changed. Verdict: pass.
2. Compiled the module with `lcompile.py` and searched the delivered files for forbidden declarations and `sorry`. Compilation succeeds without errors or warnings, with no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only existing proved declarations and permitted foundational axioms. Verdict: pass.
3. Checked the private helper route and the DAG node against the theorem statement. The helper arguments are strictly simpler than the target, the affine localization argument handles empty and zero cases, and no duplicate library statement was introduced. Verdict: pass.
4. Checked pruning and imports against the proof. The removed one-point-site and filtered-colimit proof imports are not used by the delivered proof; the remaining imports provide declarations used by it. The unit route is retained at the node level, with no unit step bypassed. Verdict: pass.
5. Checked the node's `proof`, `proof_deps`, and `proof_origin` against the Lean proof and the recorded source. They describe the stalkwise derived-category argument and affine maximal-ideal localization argument used in the file. Verdict: pass.

Changed after this reading: added this review record only; no Lean declarations, statements, definitions, or DAG proof data required correction.
