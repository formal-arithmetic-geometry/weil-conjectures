## What changed

Proved `ModuleCat.localized_range_quotient_extendScalars_aux` in
`Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernelTransport`, preserving both current
public declarations, their signatures, and docstrings; the proof-only BaseChange import is now private.
The current delivery base had moved the original quotient theorem's hole into this auxiliary
range-transport theorem after the starting copy was taken. Adapted the completed proof to
close that current hole; the quotient theorem's existing proof is unchanged.
Constructed the localization-to-scalar-extension equivalence using Mathlib, with an explicit
identity equivalence between the canonical and restricted R-actions on the localization ring.
Transported the localized range using its span description and tensor-product induction.
Updated both existing DAG nodes to agree with the proof and its auxiliary dependency.
No project theorem with `sorry` is used. The module compiles without warnings through lcompile.py.

## Proved and sorry left

Closed the one hole of the current delivery base:
`ModuleCat.localized_range_quotient_extendScalars_aux`
(node `new-residue-kernel-localized-cokernel-transport-aux`).
`ModuleCat.localized_range_quotient_extendScalars` now rests on this proved auxiliary theorem
and `Submodule.Quotient.equiv`.
No `sorry` remains and no holes were added; this is a proof, not a decomposition.

## No longer needed

`Mathlib.RingTheory.Localization.BaseChange` was changed from a public import to a plain
proof import because it is used only by the auxiliary proof. No DAG nodes or Sheaf/WeilConjectures
modules were pruned.
The auxiliary proof does not need `LinearMap.localized'_range_eq_range_localizedMap` or
`localizedQuotientEquiv`; it instead transports the span of the range directly.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The planned identification with `extendScalars` requires
handling its restricted scalar action explicitly; it is not a direct definitional application
of `LocalizedModule.equivTensorProduct` in the module system. The proof supplies that identity
linear equivalence and proves the range comparison. The unit route is preserved: this is an
algebraic transport tool, and the unit record realizes no statement or step with these nodes.
The original DAG node did not record the existing auxiliary dependency of the quotient theorem;
its proof_deps now names that auxiliary node.

## Second reading by X3

1. **Visibility and unchanged statements.** Compared the delivered module and both DAG nodes with the repository versions. The two theorem signatures and all existing declarations are byte-for-byte unchanged; the only interface change is pruning the proof-only `Mathlib.RingTheory.Localization.BaseChange` import, recorded separately.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; a scratch copy with `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both declarations. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.
3. **Split statements.** The auxiliary statement is a genuine range-transport lemma, strictly below the quotient target, and its construction and tensor induction prove it. It has a matching DAG node and docstring; no additional holes were introduced.
4. **Shortest route and pruning.** Checked the Mathlib declarations used by the construction and verified the span/tensor induction route. `BaseChange` is needed only by this proof, so it is now a plain import; all statement imports remain public. The unit route is unchanged.
5. **DAG agreement.** Updated proof text, origin, and dependency metadata to match the actual auxiliary proof and quotient reduction. No statement or unit metadata was altered.

Changed the proof-only import classification and added `coord/changes/ResidueKernelLocalizedCokernelTransport-imports.md`; no theorem statements or definitions were changed.
