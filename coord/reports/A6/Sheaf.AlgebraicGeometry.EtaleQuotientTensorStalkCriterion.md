## What changed

Proved `AlgebraicGeometry.Scheme.etale_quotient_tensor_stalk_criterion` with its full
original signature and both definitions unchanged. Added four proved private helpers
for the normalized strong-monoidal tensor identity, its invertibility consequence,
geometric-stalk equality, and tensor stalks with a zero factor.

The proof works directly in the existing abelian category of module-valued sheaves.
It proves the generator epic by stalkwise cancellation, annihilates its kernel with
`r`, and uses `ShortComplex.kernelSequence_exact` and `Exact.desc`. Geometric-stalk
conservativity makes the descended morphism invertible. Lax tensor naturality gives
the section formula, and the normalized stalk equation gives multiplication and the
specified inverse. Flatness and all three original Epi assumptions remain in the
statement. No public interface or definition changed, no consumer adaptation is needed,
and no source-library file was edited.

Updated the item's DAG proof, proof dependencies and proof origin to this argument,
and removed obsolete entries from its existing tool-use approvals. Removed the three
private proof imports listed below. All existing public imports remain.

Searches: LeanFinder for tensor products of quotient module sheaves returned ordinary
module tensor/quotient lemmas, not this geometric-stalk criterion. Loogle found no
specialized categorical tensor-generator theorem. The project/Mathlib grep located the
already proved geometric-stalk equality and conservativity APIs, the strong monoidal
stalk instances in `Mathlib.CategoryTheory.Sites.Point.Monoidal`, and Mathlib's exact
kernel-sequence descent. Those APIs give the shorter proof used here.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.etale_quotient_tensor_stalk_criterion`
(node `lem-pur-etale-quotient-tensor-stalk-criterion`).

Holes added: 0. Sorries left in the delivered module: 0. No split-off statement,
new module, axiom or unproved helper was added.

Validation: the complete file is checked through `lcompile.py`; delivery additionally
runs the project's compilation, declaration-axiom probe and preflight checks.

## No longer needed

Removed private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

Removed the corresponding proof-dependency nodes
`lem-weil-pbc-etale-constant-ring-module-equivalence`,
`lem-pc-sites-module-sheafification-tensor`, and
`lem-weil-pbc-module-sheaves-colimits-forgetful`: the existing statement already fixes
module-valued sheaves, their sheafified tensor and the canonical monoidal stalk maps,
so conversion to modules over a ring sheaf and back is unnecessary.

Also removed proof dependencies `lem-pur-ringed-site-module-category-abelian`,
`prop-weil-pbc-geometric-stalks-exact`, and
`lem-weil-pbc-preadditive-epi-iff-cokernel-zero`. The module-valued sheaf category has
its abelian instance directly; the proof maps the kernel equation and cancels an
invertible stalk map rather than identifying stalks of kernels; and it proves Epi by
cancellation rather than testing a cokernel for zero. The exact-epi cokernel lemma,
tensor convention/stalk comparison and geometric-stalk conservativity remain needed.

The removed tool-use approvals are exactly the constant-ring equivalence,
sheafification-tensor and module-sheaf forgetful nodes. No library declaration or
module is withdrawn; no assertion is made that these modules are globally unreachable
through other public imports or other consumers. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The proposed seven-step proof is valid but needs more interfaces than the actual Lean
statement: its tensor and unit are already the published module-valued sheaf tensor
and unit. Mathlib's strong monoidal stalk structure supplies the normalized tensor
identity directly. The existing conservative geometric-point family gives joint
faithfulness for module coefficients, so no explicit passage to abelian sheaves or
zero-cokernel criterion is required. No statement defect was found or corrected.

The zero ring, empty scheme, empty intersection, and either asymmetric off-support
case require no additional hypothesis: the zero-factor argument treats them uniformly.
All stalk formulas are proved for every normalized identification as required, rather
than only the identifications selected from the hypotheses.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
