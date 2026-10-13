## What changed

Proved `AlgebraicGeometry.Scheme.trace_discriminant_evaluation_ne_zero_iff_etale_fibre`
with its original signature unchanged. Its proof imports two new, fully proved modules:
`Sheaf.AlgebraicGeometry.Morphisms.AffineFibreTensorEtale` and
`Sheaf.RingTheory.TraceFormEtaleField`. All new imports in the original module are proof-only.
The former identifies fibre etaleness with tensor-algebra etaleness using affine pullback
squares; the latter proves the general finite-algebra trace criterion. The original module
proves the discriminant base-change calculation directly from Mathlib.

All three modules compile without warnings using lcompile.py. The source is
[Stacks Tag 0BJF](https://stacks.math.columbia.edu/tag/0BJF), whose finite-dimensional
trace-pairing argument is followed. No signatures, definitions, or existing visibility changed.
The unit route is unchanged: the target node's original fibre-algebra step is now fully realized.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.trace_discriminant_evaluation_ne_zero_iff_etale_fibre`.
No sorries remain, and no holes were added or split off.

Also proved the two new helper declarations without sorry:
`AlgebraicGeometry.Scheme.etale_fibre_iff_etale_tensor_section_algebra`
(node `lem-sbc-affine-fibre-tensor-etale`) and
`Algebra.traceForm_nondegenerate_iff_etale`
(node `lem-sbc-trace-form-nondegenerate-iff-etale-field`).

The rank-zero case is covered uniformly by the empty determinant, finite algebra
product characterization, and affine pullback argument. The field criterion admits the
zero algebra; neither proof assumes Nontrivial of the section or fibre algebra.

## No longer needed

No original imports or DAG dependencies were pruned (the original proof_deps was empty).
Second reading removed the redundant explicit `Mathlib.RingTheory.TensorProduct.Basic`
helper import and made `Mathlib.RingTheory.Etale.Field` proof-only, using
`Mathlib.RingTheory.Etale.Basic` for the public statement.
The exploratory imports `Mathlib.LinearAlgebra.TensorProduct.Basis` and
`Mathlib.RingTheory.TensorProduct.Free` were removed because the original discriminant
imports already provide their declarations and instances. No project module became
unreached through this delivery. No exploratory directional lemma modules are delivered.
The converse trace argument reuses the already proved
`WeilConjectures.Mathlib.RingTheory.Trace.Basic` tools instead of restating their theory.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The node's single non-elementary proof step had no named
proof dependencies; this delivery records its two proved components and the direct
trace/discriminant base-change calculation. LeanSearch was unavailable (Internal Server
Error); LeanFinder, Loogle, source-library rg and Mathlib rg supplied the search evidence.
No forced adaptations or interface changes were needed.

## New nodes

`lem-sbc-affine-fibre-tensor-etale` states fibre etaleness iff residue-field tensor-algebra
etaleness, with no finite-dimensional assumption. It is proved using Mathlib's affine
chart, stalk, tensor pullback and ring-hom-property lemmas. Its source is the affine
fibre reduction in Tag 0BJF. LeanFinder/Loogle found related fibre and evaluation tools;
rg identified the precise affine chart and pullback API.

`lem-sbc-trace-form-nondegenerate-iff-etale-field` states the trace-form criterion for
any finite-dimensional commutative field algebra, including the zero algebra. Its proof
follows Tag 0BJF: nilpotents vanish, an Artinian reduced algebra splits into quotient fields,
nonzero trace forces each factor separable, and the existing source finite-etale trace
lemma proves the converse. LeanFinder found the field TFAE and etale product criterion;
rg found the source trace_pi_single and exists_trace_mul_ne_zero tools. No new axioms or
unproved helper statements are used. No change records are required.

## Second reading by N1

1. **Statements and accidental changes.** Compared the delivered target module with the repository version and checked all existing declarations byte for byte. The target signature is unchanged; the two helper declarations are new nodes with statements matching their JSON records. No definition or visibility was changed. Verdict: pass.

2. **Compilation and trust.** Compiled all three modules with `lcompile.py --all`; each completed without errors or warnings. Axiom probes for all three declarations report only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations, and no definition contains `sorry`. Verdict: pass.

3. **New statements.** Checked the affine fibre statement against the affine pullback and tensor-product construction, including the empty algebra case. Checked the trace criterion against Stacks Tag 0BJF and the Mathlib/source trace lemmas; finite-dimensional reduced algebras split into residue fields, and the converse uses the finite-etale trace witness. Neither statement adds hypotheses or weakens its conclusion, and no duplicate declaration was found by LeanFinder, Loogle, or repository search. Verdict: pass.

4. **Route and pruning.** The target proof keeps the unit's affine fibre and trace-pairing route. The target uses both helper nodes exactly as recorded in `proof_deps`; the helpers use only their stated source tools. The exploratory tensor imports are absent from the final files, and no original proof dependency is unused. Verdict: pass.

5. **DAG and report consistency.** The target and helper node `lean` records, proof steps, and `proof_deps` agree with the imports and theorem bodies. The report records one target hole closed, two helper declarations proved, and no holes added. Verdict: pass.

Changed during second reading: replaced the helper’s public `Mathlib.RingTheory.Etale.Field` import with public `Mathlib.RingTheory.Etale.Basic` plus proof-only `Mathlib.RingTheory.Etale.Field`; removed redundant `Mathlib.RingTheory.TensorProduct.Basic` from the affine helper (already provided by its other public imports); removed an extra blank line. No proof or statement changes. Recompiled the complete delivery after the import cleanup.
