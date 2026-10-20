## What changed

Proved `Ideal.quasiRegular_flatQuotient_baseChange` in
`Sheaf.RingTheory.QuasiRegularFlatQuotientBaseChange`, with its signature unchanged.
Private, fully proved helpers establish flatness of the graded pieces and all
ideal-power quotients, injectivity of the tensor inclusions, coefficient maps
from the given graded isomorphism, and the homogeneous relation criterion.
The criterion then gives injectivity and surjectivity of the canonical map.
The monomial and homogeneous-component helpers reproduce the corresponding
private helpers of `RegularSequenceGradedPolynomial`; those declarations cannot
be called from another module. They use only the construction of the canonical
map, not its regular-sequence theorem or any unproved higher-relation theorem.

Proof imports added: `Mathlib.RingTheory.Flat.Stability`,
`Mathlib.RingTheory.TensorProduct.Quotient`, and
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`.
The last supplies the already proved flat-extension lemma.
The node's proof, proof dependencies and proof origin now describe this argument.
No definition, existing declaration signature, or unit realization changed.

## Proved and sorry left

Closed 1 of 1 holes: `Ideal.quasiRegular_flatQuotient_baseChange`
(node `lem-pur-quasi-regular-flat-quotient-base-change`).
There are zero holes left in the item and zero holes added elsewhere.
No theorem is split off. Every private helper is proved.
The complete module compiles without warnings through `lcompile.py`.

## No longer needed

Retained the existing public imports to preserve the module's public interface.
Removed the direct proof imports `Mathlib.RingTheory.Flat.Equalizer` and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`; the new proof imports
provide their used declarations transitively.

The declared dependency `lem-weil-pbc-finite-product-flat-modules` is unused:
flatness of the entire polynomial ring and the direct-summand criterion replace
the finite enumeration of homogeneous monomials. The replacement uses the
existing Mathlib leaf `lem-weil-pbc-flat-ring-map-comp` (`Module.Flat.trans`).
The other original dependencies remain used, including tensor right exactness
through the flat-extension lemma and quotient tensor equivalence.
No existing Sheaf module is made unreachable or withdrawn by this delivery.

The planned explicit graded-piece tensor equivalence and tensor equivalence
for finite coordinate products are unnecessary: the coefficient maps detect
relations directly. Temporary unsubmitted split drafts were removed; they are
not new modules or nodes in this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original eight-step route is
valid, but its finite coordinate products and graded base-change equivalence
need more constructions than the coefficient argument. The unit's route is
preserved. The theorem still allows arbitrary scalar extension and assumes
flatness only of A/J, including zero rings and the empty sequence.

The resumed attempt's first dry run rejected the earlier packet's public-import
removals because no change record accompanied them. Those imports are restored;
no public-interface change or consumer adaptation remains.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
