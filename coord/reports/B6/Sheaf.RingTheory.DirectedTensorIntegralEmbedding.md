## What changed

Proved `Algebra.TensorProduct.directed_integral_embedding` in
`Sheaf.RingTheory.DirectedTensorIntegralEmbedding`, following all five existing
DAG proof steps. A proved private helper transports
`CommAlgCat.filteredColimit_tensorProduct_elementwise` to the specified colimit
cocone using its canonical cocone-compatible algebra isomorphism. The main proof
uses eventual vanishing and stagewise injectivity for the kernel, transports
integrality with `IsIntegral.map_of_comp_eq`, and constructs the restricted
algebra homomorphism by `AlgHom.codRestrict`. Tensor extensionality proves the
transition and coprojection identities. The public theorem statement and all
imports are unchanged. Remote single-file validation through `lcompile.py`
passed cleanly in 10.4 seconds.

## Proved and sorry left

Closed the sole hole, `Algebra.TensorProduct.directed_integral_embedding`
(node `lem-sfb-directed-tensor-integral-embedding`). Added zero holes and split
off zero statements. No `sorry` remains in the delivered module. The private
transport helper is proved in full.

## No longer needed

None. Every declared proof dependency is retained, and the original proof-only
import of `WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`
is used. No nodes, modules or imports are pruned; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The supplied five-step plan applies to
the exact theorem, including arbitrary specified colimit cocones and transition
maps that need not be injective. The transport helper only specializes and
transports the existing elementwise theorem; it adds no mathematical assumption.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
