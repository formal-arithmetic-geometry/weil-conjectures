## What changed

Proved `AlgebraicGeometry.Scheme.regular_divisor_root_model_normal` by splitting each
factor's prime ideals according to membership of the root coordinate. Added the proved
module `Sheaf.RingTheory.RootAlgebraRegularAtRoot` for the containing-root case.
All original signatures and public imports are unchanged. Updated the item's DAG proof.

Along the root divisor, the new module constructs the equivalence B/(t) ≃ R/(f)
explicitly from ring homomorphisms. Freeness and flatness give injective multiplication
by t, retained after localization. Quotient/localization compatibility identifies the
local quotient with a regular prime localization. A private proof of regularity lifting
uses generators of the quotient maximal ideal and Mathlib's nonzerodivisor dimension
formula; no regularity-lifting axiom or unfinished theorem is added.

Away from the root, the private derivative argument extends the polynomial derivative
to the corresponding local ring of R[X]. Its unit value on the equation keeps the
equation outside the square of the maximal ideal. The existing regular-hypersurface
criterion proves the local quotient regular. Existing regular-ring normality and
finite-product normality, followed by Mathlib's Spec.stalkIso, finish the proof.

The new containing-root lemma assumes only a Noetherian base, a nonzerodivisor f,
regular R/(f), and positive exponent. It needs neither regularity of R nor an invertible
exponent. The proof is complete, and every object is constructed explicitly.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.regular_divisor_root_model_normal` (1 of 1 original holes).
Also proved: `AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem`
(node `lem-sbc-root-algebra-regular-at-root`), private `lift_regular`, private `root_pow`,
private `root_quotient_equiv` (a constructed ring equivalence), and private
`regular_root_localization_of_derivative_not_mem`.
No sorry remains in either delivered module. No holes were added; none was split off.
Existing imported declarations retain their existing status. Both modules compile cleanly
with lcompile.py --all; the dry-run axiom/preflight checks are the final validation.

## No longer needed

No original imports or dependency nodes were removed. The second reading removed
redundant newly added imports `Mathlib.RingTheory.Localization.Ideal` from the item
and `Mathlib.RingTheory.Flat.Basic` from the new module; both remain available
through imports needed for other parts of the proofs. No module is pruned from
the targets import closure. The original node had no
proof dependencies. The away-from-root argument needs no new etale-presentation,
etale-regularity-ascent, or finite-product-regularity statement or module. Normality is
applied to the factors before taking their product. The new divisor lemma is proved
rather than leaving regularity lifting or root-quotient identification as further items.

## Where the brief, the DAG or earlier work was wrong

The original node supplied non-elementary proof steps but no proof dependencies.
The library has normality and finite-product normality statements, and these are now
explicit dependencies. Polynomial regularity and the regular-hypersurface criterion
allow the off-root branch to be proved directly instead of constructing an etale map.
The underlying mathematical statement remains unchanged, including m=0, zero rings,
unit f, and exponent 1. In the new lemma the zero ring has no primes; unit f makes
root membership impossible; exponent 1 is covered by the explicit quotient construction
and positive-exponent calculations. The finite-product lemma covers the empty product.
The unit record has no realized nodes, and its trait/root-model route is preserved.

Read Stacks Tags 0EYH, 0EYG, 00NU and 07PF online (the local literature contains only
citation lists). A blueprint search for “root regular” found no duplicate. Mathlib searches
were run through msearch.py and logged; LeanSearch returned an internal server error,
Loogle found no root/regular-local-ring theorem, and the regular-local-ring grep found no
such theorem. RegularRingNormal, FiniteProductNormal, Derivation.CompletionAndLocalization
and the regular-hypersurface criterion are general algebra tools from the
proper-base-change unit; their use bypasses no step of the spreading unit.

## New nodes

`lem-sbc-root-algebra-regular-at-root`: proved local regularity at primes containing
the root coordinate, following the finite-free and nonzerodivisor-quotient verification
in Tags 0EYH/0EYG and the lifting argument of Tag 00NU. This is strictly one local case,
not the product's normal-stalk assertion under a new name. No change records or forced
adaptations are needed.

## Second reading by G3

1. Compared the delivered item with the repository using diff and an exact text
   comparison of the original theorem signature through `:=`. PASS: the signature,
   hypotheses, conclusion, public imports, and existing definitions are unchanged.
   Restored the original theorem docstring and one extra signature space.
2. Read both proofs in full and compiled both modules through lcompile.py. PASS:
   neither module contains sorry or forbidden declarations. Scratch-copy
   `#print axioms` for the item and the new public theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The quotient equivalence is constructed from explicit mutually inverse maps;
   the chosen lifts in `lift_regular` come from proved quotient surjectivity.
3. No unfinished statement was split off. PASS: the proved new theorem treats only
   primes containing the root and is strictly one part of the item's argument.
   Checked zero rings (no primes), unit f (root cannot lie in a prime), n=1,
   and arbitrary positive n without invertibility. Its docstring and node give
   the full argument. Independent LeanFinder, Loogle, Mathlib grep and repository
   searches found ingredients but no duplicate. Verified the lifting argument
   against https://stacks.math.columbia.edu/tag/00NU and the derivative argument
   against https://stacks.math.columbia.edu/tag/07PF.
4. Checked the route from the item downward. PASS: polynomial regularity and the
   hypersurface criterion supply the off-root case; the existing global
   `quotient_span_singleton_of_isUnit_derivation` requires a globally unit
   derivative, unavailable at primes containing the root, and gives no shorter
   direct reduction here. Removed two redundant proof imports as listed above.
   The original proof_deps list was empty, so no old dependency is omitted from
   No longer needed. The unit's realized arrays are empty; its trait/root-model
   route and all unit steps are preserved.
5. Compared both nodes with the declarations, source arguments, and actual uses.
   PASS: the existing node changes only its proof route, dependencies and origin;
   the new node contains source, statement dependencies, proof, proof origin,
   three kinds of search, creation metadata, blueprint ancestry and exact Lean
   signature. The dependencies match the proofs. Added independent search results
   to the new node.

Second reading changed only signature whitespace restoration, restoration of the
existing docstring, removal of two redundant new proof imports, search records,
and this report. No mathematical proof repair or additional hole was required.
