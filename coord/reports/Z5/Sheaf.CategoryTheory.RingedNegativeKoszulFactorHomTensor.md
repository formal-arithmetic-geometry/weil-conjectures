## What changed

Proved `CategoryTheory.ringedNegativeKoszulFactorHomTensor` with its existing statement.
The item module constructs a canonical isomorphism from the negative factor to
`Hom(P_m,O[0])`, verifies both its transition and its degree-zero basis normalization,
and tensors this isomorphism with `Hom(K,O[0])`. The rank-one identifications are
normalized against the prescribed Hom unit by an explicit unit automorphism;
endomorphisms of the monoidal unit commute, so scalar compatibility is preserved.
A proved private closed-category calculation supplies the natural, normalized
product of internal Homs; existing Koszul dualizability makes it invertible for
arbitrary K. The construction and its laws are packaged together so that Lean
checks the functor conversions in the generic category. Local instance bindings
avoid repeated tensor-existence searches; they are confined to the proof, and
no private declaration occurs in the public theorem's type. The existing named
sheaf-composition proof is given local instance priority to avoid repeating
its instance search; no dependency module is modified.

Added proof-only imports of `RingedHomTensorUnitNormalization`,
`RingedKoszulDualizable`, `Monoidal.Dual`, and Mathlib rigid braiding.
Updated the item's DAG proof and proof dependencies to match this route.
No public signature or definition changed.

## Proved and sorry left

Closed: `CategoryTheory.ringedNegativeKoszulFactorHomTensor` (one original hole).
Added holes: zero. Remaining holes in the delivered module: zero.

Validation: the remote axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. The theorem's signature is byte-for-byte unchanged. The final
remote single-file compile passed in 49.1 seconds with no warnings. A separate
public-type audit found no private constants in the theorem signature.

## No longer needed

No original import was removed. The proof does not need these planned dependencies:

- `lem-sc-finite-free-internal-hom-exact`
  (`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`):
  rank-one evaluation is calculated directly; no short exact sequence is involved.
- `lem-sc-hom-tensor-degreewise`
  (`WeilConjectures.Algebra.Homology.HomTensorDegreewise`).
- `lem-sc-hom-tensor-differential`
  (`WeilConjectures.Algebra.Homology.HomTensorDifferential`).
- `lem-sc-hom-tensor-naturality`
  (`WeilConjectures.Algebra.Homology.HomTensorNaturality`).

The three general Hom-tensor dependencies are replaced by the ordinary closed-category
product of Homs; its invertibility, naturality, and normalization are proved in private helpers.
These are dependency removals from this node; other consumers may still need them.

## Where the brief, the DAG or earlier work was wrong

The previous route was mathematically sound but requested an arbitrary-coefficient
two-summand comparison. Existing ordinary-complex dualizability and the ordinary
closed structure avoid that calculation: only the dual into O[0] in degrees -1 and 0 needs
explicit coordinates. No general signed-dual complex is constructed or used. The proof
includes b=0, units b, K=0, zero ring sheaves, and empty sites; it never divides by a section or
assumes boundedness of K.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
