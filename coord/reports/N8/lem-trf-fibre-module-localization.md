## Worker report

The module states `RingTheory.fibreModuleLocalization`. It introduces a commutative-ring
map `φ : A →+* B`, a prime ideal `p`, and a B-module `N`, with the induced A-module
structure. It states existence of an A-linear equivalence between the tensor product
with `p.ResidueField` and the localized quotient module. The first conjunct gives the
canonical fraction formula on pure tensors; the second gives the inverse on localized
quotient generators; the third records B-linearity on pure tensors, which determines
B-linearity because pure tensors generate the tensor product. The quotient is by the
B-submodule spanned by all `φ a • n` with `a ∈ p`, and the localization submonoid is
`Submonoid.map φ p.primeCompl`.

The statement uses `TensorProduct` from `Mathlib.LinearAlgebra.TensorProduct.Basic`,
`LocalizedModule` from `Mathlib.Algebra.Module.LocalizedModule.Basic`, the residue field
`Ideal.ResidueField`, and `RingTheory.annihilatorAssociatedPrimes` is imported for the
recorded proof dependency. The induced A-module structures are supplied canonically by
`Module.compHom`; no extra mathematical hypothesis is imposed. The dependency declarations
are Mathlib `TensorProduct` and `LocalizedModule`, and upstream
`RingTheory.annihilatorAssociatedPrimes` in `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`.

Edge cases checked: `p` is an arbitrary prime ideal (including zero and maximal primes),
`N` may be zero, and no Noetherian or finite-generation hypothesis is added. The prime
complement is used as a multiplicative submonoid, and all universes are explicit.

Searches: `msearch.py grep` for fibre/module localization declarations in the source
returned no match; LeanFinder query “canonical isomorphism tensor product with residue
field localization of quotient module” returned only generic tensor/localization results;
Loogle query `TensorProduct, LocalizedModule, Ideal.ResidueField` returned no complete
match; grep of Mathlib found `LocalizedModule.equivTensorProduct` and related generic
lemmas but no statement with the quotient and annihilator clauses. Thus no existing
single declaration matches this node.

STATEMENT-DISPUTED: the node's prose calls the isomorphism B-linear, while the canonical
B-action on the tensor product is not a Mathlib typeclass instance. The Lean statement
uses an A-linear equivalence together with the explicit B-linearity equation on pure
tensors, which is the exact generated condition and preserves the stated meaning.

## Second reading by N8

The node and file were read together. The binders match `A`, `B`, `φ`, prime `p`, and
B-module `N`; the induced A-module is canonical. The first conjunct renders the displayed
map on `n ⊗ (a/s)` as the class of `φ(a) • n` over `φ(s)`. The second conjunct renders
its inverse on `n/φ(s)` as `n ⊗ (1/s)`. The final conjunct renders B-linearity on pure
tensors. No hypotheses or edge cases are omitted.
