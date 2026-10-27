## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.adicFiniteTop_roos_epi` with a
complete Lean proof from one structural tensor-sequence statement and the existing
Milnor/product theorems. The assigned theorem's signature and public import are
unchanged. All new imports in the assigned module are private proof imports.

The proved private helpers do the following:

- `map_roos` proves naturality of the Roos map under an additive functor by checking
  every product projection.
- `model_exact_products` transports exact countable products to the coefficient-sized
  site through the module-sheaf equivalence.
- `model_tower_epi` transports an arbitrary epimorphic successor tower to the actual
  pro-etale site, applies `milnor_epimorphic`, conjugates by the product comparison,
  and reflects epimorphy back through the equivalence.
- `top_transition_epi` applies the residue Tor predicate at b+1 to the tensor-sequence
  kernel, uses the actual short-exact-complex homology sequence, and transports its
  epimorphism through the localization factorization and the normalized transition
  square.

The final proof applies these helpers and preservation of countable derived products
by cohomology. The only isolated unfinished step constructs the normalized ordinary
short exact tensor sequence for one transition; it has no Tor interval, completeness,
product, or Roos hypothesis or conclusion.

Both modules compiled through lcompile: the tensor-sequence module in 6.1 seconds and
the assigned module in 12.8 seconds. Subsequent delivery recompiles the final files.
The structural statement was checked on J=0 (zero kernel, identity quotient), J=A
(zero quotients and kernel), n=0, the zero complex, and the empty scheme. It imposes
no principal-ideal, regularity, or Noetherian restriction.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.adicFiniteTop_roos_epi`
(`lem-sfb-adic-finite-top-roos-epi`). There are zero sorries in the assigned module.
All four new private helper proofs are complete.

Added one named theorem hole:
`AlgebraicGeometry.Scheme.adicFiniteTransition_tensor_sequence`
(`lem-sfb-adic-finite-transition-tensor-sequence`), in the new module
`Sheaf.Paper.AdicFiniteTransitionTensorSequence`.
Its body is exactly `by sorry`; its docstring and node give the full construction
and natural-language proof.

This is a decomposition: one original hole closed, one structural hole added, net
hole reduction zero. It does not claim an unconditional proof of the original item.
The added statement is strictly the coefficient-kernel tensor construction, without
any Tor bound or inverse-product conclusion. The Tor-test, long-exact-sequence,
localization, site-transport, and Roos arguments combining it into the assigned
conclusion are proved in Lean.

## No longer needed

No existing import was removed, and no module or node is globally pruned.
The original direct K-flat-resolution, change-of-rings, K-flat-base-change, and
flat-sheaf dependencies move into the tensor-sequence node, where they are still
needed. The parent node now lists the dependencies of its actual Lean proof.
The original public import `Sheaf.Paper.AdicFiniteReductionData` is retained.

No principal-power quotient sequence is imported: the existing
`SuccessiveQuotientFlatTensorSequence` and `SuccessiveQuotientLinearTriangle` APIs
require a principal regular section and cannot specialize to arbitrary J.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The DAG's coefficient-kernel tensor step was
not yet a Lean interface: the existing principal regular quotient sequence is a
different result. The new theorem states exactly that structural step, retaining
the normalization equation with `adicFiniteTransition`. The rest of the DAG plan
is now written in Lean. The unit and chapter route are unchanged.

## New nodes

`lem-sfb-adic-finite-transition-tensor-sequence` records the short exact cochain
presentation of a single normalized transition. Its last two terms represent
U_(n+1) and U_n with a commuting transition square; its first homology is a
restricted residue tensor test in every degree. The construction is independent
of the Tor hypothesis used above it. Its source is the coefficient-tensor step
in Stacks 09C2 (1), expanded using K-flat change of rings, flat tensor exactness,
balancing, and exact scalar restriction. No existing shared interface changed,
so no change record or consumer adaptation is required.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
