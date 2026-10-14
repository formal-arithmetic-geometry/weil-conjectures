## What changed

Proved `HopfAlgebra.height_ker_counit_eq_ringKrullDim` in
`Sheaf.RingTheory.HopfAlgebra.AugmentationHeight` with the existing statement unchanged.
Added proof-only imports for convolution, tensor Hopf structures, algebraic closure,
finite-type base change and the source library's proved Nullstellensatz. Faithfully flat
spectra and integral tensor base change are available through retained imports; the
second reading removed their redundant direct imports. Both original Sheaf proof
imports are used.

Over an algebraically closed field, explicit mutually inverse convolution translations
identify each maximal-ideal height with the counit-kernel height. Mathlib's maximal-height
criterion identifies that height with the global dimension. For arbitrary fields, tensor
with the algebraic closure. Integral contraction is strictly monotone, and going down
lifts every smaller prime; `Order.height_eq_of_strictMono` proves height preservation.
This replaces the planned local flat-height formula and fibre-quotient calculation.
Tensor commutation is used explicitly to keep the standard scalar actions on both tensor
orders. The DAG proof and its dependencies now describe this argument.

The private translation helpers reproduce the proved formulas in
`WeilConjectures.RingTheory.HopfAlgebra.Cartier`; importing that module would create a
cycle, because it imports this item. All helpers are fully proved. The unit's translation
and maximum argument is retained, as is descent through algebraic closure.

## Proved and sorry left

Closed the only original hole:
`HopfAlgebra.height_ker_counit_eq_ringKrullDim`
(node `lem-wf-hopf-augmentation-height`). No holes added and no `sorry` remains anywhere
in the delivered Lean file. This is a full proof, not a decomposition.

Local compilation completes without warnings in approximately 2 seconds. The explicit
`#print axioms` check reports only `propext`, `Classical.choice` and `Quot.sound`.
The delivery dry run also checks every declaration's axioms.

## No longer needed

No original Lean import was removed: `Sheaf.RingTheory.IntegralExtensionDimension` and
`Sheaf.RingTheory.KrullDimension.GoingDown` both supply used dimension inequalities.

The second reading removed the first worker's redundant proof-only imports
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` and
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. Their results remain used through
retained imports, so their dependency nodes remain in `proof_deps`; this removes no
additional mathematical dependency or original import-closure module.

The proof no longer needs these planned nodes:

- `lem-weil-pbc-flat-height-formula`: replaced by integral incomparability plus going down.
  No localization, quotient fibre, or Noetherian dimension formula is used.
- `lem-sc-translation-automorphism`: the scheme-level module
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic` is unnecessary for this proof;
  translations are constructed directly from Mathlib's Hopf convolution API.

`WeilConjectures.RingTheory.HopfAlgebra.Cartier` and the modules for group-scheme/local-ring
translation are not imported. No claim is made that these modules become globally
unreachable: that depends on their other importers. The tensor universal property,
Nullstellensatz, field-extension faithful flatness, both dimension bounds, and the
Krull-dimension definition remain used.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned flat-height/fibre step is stronger machinery than
needed: integral plus going down already preserves each prime's height. The planned
scheme translation declaration has a scheme interface; direct convolution formulas fit
the Hopf-algebra interface and avoid importing a downstream module.

The Nullstellensatz dependency node lacks a Lean attachment, although the source library
already proves the exact needed statement as `exists_algHom_ker_eq_of_isMaximal` in
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`. This delivery uses that declaration
and leaves the dependency node's bookkeeping to the maintainer.

No statement, definition, universe, signature or public import was changed. No adaptations
or new nodes were needed. The checker classifies the added namespace opens and section
variables conservatively as an interface change;
`coord/changes/augmentation-height-proof-context.md` records their scope and the
unchanged public API. The cited blueprint source is absent from this machine's
literature checkout; the existing node/docstring supplies the translation/dimension
argument, and the formal proof uses the available library and Mathlib declarations.

## Second reading by T4

1. Compared the entire delivered module against the repository version. The signature,
   visibility and docstring of `HopfAlgebra.height_ker_counit_eq_ringKrullDim` are byte
   for byte unchanged. The original three public imports are identical. All helpers
   are private; added imports are proof-only. There is no changed public definition,
   target statement or forced adaptation. The proof-context change record accurately
   explains the checker's conservative interface classification. Verdict: pass.

2. Read every helper and the final proof, then compiled locally without warnings.
   Translation and its inverse are constructed as convolution algebra maps and their
   inverse laws are proved; no object is chosen from an unproved existence theorem.
   `#print axioms` on a scratch copy checks all nine declarations, including the
   translation definition and final theorem. Only the permitted axioms occur; there
   is no `sorry`, custom axiom, unsafe declaration or hollow definition. Integral
   contraction is strictly monotone by incomparability; going down lifts all smaller
   primes, precisely the hypotheses of `Order.height_eq_of_strictMono`. The tensor
   commutation calculation contracts the correct counit kernel. Verdict: pass.

3. There are no split-off statements and no new holes or nodes. Independently searched
   the repository for height under contraction and Hopf translation, and ran logged
   Mathlib grep with integral/going-down height terminology and Loogle with counit/height.
   The existing Mathlib height-addition formula requires a quotient-fibre calculation
   and is longer here. The existing public translation theorem is in downstream
   `Cartier`, which imports this module, so using it would create a cycle; the private
   reproduced calculation is justified. Checked the small cases `A = k`, disconnected
   zero-dimensional groups and infinitesimal groups: the counit kernel remains proper,
   and the argument requires neither reducedness nor characteristic zero. Algebraic
   closure can be inseparable: integrality and flatness still apply. Verdict: pass.

4. Read `dag/units/sk-i-cartier.json`, including its translation/maximum step and
   `realized` fields, and the existing node's source and proof plan. The unit's route
   remains unchanged: local dimensions are identified by translations and their
   maximum gives global dimension. Only the below-unit height-descent machinery is
   shortened. `realized` is unchanged (its lists are empty in the repository).
   Both obsolete original `proof_deps` are listed under `## No longer needed`.
   Import-removal compilation trials confirm the retained proof imports are needed;
   two first-worker additions were redundant and removed. Verdict: pass after pruning.

5. Read each dependency node's statement and Lean/Mathlib attachment. The integral
   dimension theorem, going-down dimension theorem, faithful flatness/spectrum/going-down
   instances, incomparability and tensor constructions match the proof's uses.
   The delivered node changes only `proof`, `proof_deps` and `proof_origin`, with
   `proof_deps` exactly the union of step citations. The source Nullstellensatz's
   maximal-ideal clause supplies exactly the required algebra homomorphism; its missing
   node attachment is reported above rather than silently repaired outside this item.
   The node's statement and Lean record are unchanged. Verdict: pass.

Second-reading changes: removed the two redundant direct Mathlib imports and updated
this report. No mathematical proof, signature, definition, node or change record was
rewritten. One original hole closed, zero holes added, zero split off.
