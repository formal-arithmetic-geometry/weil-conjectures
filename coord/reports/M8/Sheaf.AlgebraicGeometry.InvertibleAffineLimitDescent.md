## What changed

Proved `AlgebraicGeometry.invertible_affine_limit_descent` without changing its signature.
The proof applies the existing `invertible_fp_tensor_models` and
`finitePresentation_iso_descent_affineLimit` declarations, identifies pullbacks of the
structure module using `tensorPullbackObjUnitToUnit_isIso`, and assembles the stage tensor
trivialization. The existing `affineLimitTensorPullbackComparison` identifies its limit
pullback with the given line bundle.

Added a proved private helper `AlgebraicGeometry.isInvertible_of_tensorIsoUnit` for
quasi-coherent scheme modules. On each affine open, the tensor-sections isomorphism gives
invertible coordinate-ring modules; these are finite projective and their prime-local
ranks multiply to one. The affine local-freeness criterion then gives local rank one.
This supplies the final implication using the library's actual local-triviality definition.
No definition, public signature, public import, attribute, or other existing module changes.

Updated the item's DAG proof and proof dependencies to record the actual assembly and helper.

Repair of returned delivery `a702297072b`: removed the inherited warning-suppression
option from the module header. The landing hole scanner treated the option's dotted
name as an unattributed hole at line 33, offset 1421. This option is unnecessary now
that both theorem proofs are complete. No proof, signature or dependency was changed
by the repair. The retained proof was compared with the current shared source; its
public imports and existing theorem signature remain identical to that source.
The project's `sorry_ledger.scan_text` now reports both named theorems with empty
marker lists, no unattributed rows, and no scanner warnings.

The repaired version compiled cleanly through `lcompile.py` in 4.7 seconds, with no
errors or warnings. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.invertible_affine_limit_descent`
(node `lem-trf-invertible-affine-limit-descent`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
The private helper is fully proved. The existing imported descent statements remain the
next proof obligations; no claim is made that their transitive axiom closure is sorry-free.

## No longer needed

Removed redundant direct proof imports:

- `WeilConjectures.AlgebraicGeometry.Modules.Dual`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`

Their required declarations remain available through the two descent interfaces. No
mathematical branch or module is withdrawn: the two existing extracted dependencies are
both used, and the original finite-presentation descent remains needed by them. No unit
statement or unit proof step is bypassed. The former direct `def-pc-module-pullback`
proof dependency is represented more precisely by the structure-sheaf pullback theorem
and `def-trf-affine-limit-tensor-pullback-comparison`, retaining it transitively.

## Where the brief, the DAG or earlier work was wrong

The first delivery retained an inherited warning-suppression option whose dotted
name was miscounted as a standalone hole by the source ledger. Removing that unused
option repairs the exact landing refusal without modifying the tools or moving a hole.

The DAG's reference to the tensor-inverse characterization was mathematically correct,
but the recorded Lean `IsInvertible` definition only gives local rank-one triviality.
`IsInvertible.of_tensorObj_iso_unit` in the source library requires one factor to be
invertible already and cannot be used here. The private affine-rank proof fills this API
gap without strengthening any hypothesis or adding a split-off theorem. Source checked:
Stacks Limits Tag 0B8W, `lemma-descend-invertible-modules` (2), and Modules Tags 0B8K,
0B8M, `lemma-invertible` and `lemma-invertible-is-locally-free-rank-1`.

The helper remains valid on the empty scheme (the affine rank criterion is vacuous there);
at any prime of an affine coordinate ring, nontriviality follows from that prime. No
nonempty-scheme, Noetherian, affine-stage, or flat-transition hypothesis was introduced.
The singleton-index case uses the same argument and all morphisms are tensor pullbacks.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
