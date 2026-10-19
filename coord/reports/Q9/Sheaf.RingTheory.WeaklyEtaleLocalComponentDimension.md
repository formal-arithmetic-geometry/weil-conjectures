## What changed

Proved `RingHom.WeaklyEtale.ringKrullDim_quotient_minimalPrime_eq` with its exact original
signature. The proof uses the declared normalization tensor decomposition. Its projection
to the normalization E of D/P is surjective and D-linear, making E finite over D/P.
Integral injective dimension invariance identifies dim E with dim(D/P).

The upper inequality uses dim E <= dim(C' tensor D) <= dim C' = dim C. The lower
inequality chooses any maximal ideal of E, computes its contraction to C', applies the
finite-normalization dimension theorem, and uses faithful flatness of the canonical local
map. In particular no maximal-length chain or finite-dimension theorem is needed.

Added the fully proved module `Sheaf.RingTheory.WeaklyEtaleDimension`, with theorem
`Algebra.WeaklyEtale.ringKrullDim_le`. This separate general result is the upper bound
in Greco's local AF comparison: weakly etale residue-field fibres are absolutely flat,
hence have only maximal primes. The fibre prime order isomorphism makes contraction
strictly monotone, and the Krull-dimension comparison follows. The proof uses the proved
upstream absolute-flatness API, not an additional assumption or sorry. Updated the item
node's proof, proof dependencies and proof origin to match the written argument.

No existing statement, definition, public import, or consumer module was changed.
The normalization theorem application supplies the algebra instance explicitly. The local
normalization names are explicitly typed as Type u and Type v, rather than inferred as
subalgebras; this avoids repeated conversion of their subtype algebra structures. The main
module compiles in 40.8 seconds. No elaboration options remain in the delivered files.

## Proved and sorry left

Closed 1 of 1 original holes:
`RingHom.WeaklyEtale.ringKrullDim_quotient_minimalPrime_eq`
(node `lem-exc-weakly-etale-local-component-dimension`).

Also proved `Algebra.WeaklyEtale.ringKrullDim_le`
(node `lem-exc-weakly-etale-dimension-upper-bound`). Added 0 holes. There is no sorry
in either delivered module. This is a proof, not a decomposition into new holes.
The imported existing `weaklyEtale_normalization_tensor` is unchanged and remains a
proof dependency as intended by stage 3.

## No longer needed

Removed proof imports `Sheaf.RingTheory.WeaklyEtaleField`,
`Sheaf.RingTheory.IndEtaleUniverseTransport`, and
`WeilConjectures.Mathlib.RingTheory.Etale.Weakly`.

The node no longer directly needs `lem-weil-pbc-weak-etale-field`: fibre incomparability
uses the already proved absolute-flatness criterion directly, without finite subalgebras,
ind-etale presentations, separability or ind-etale universe transport. Removed its old
tool-use approval. The new dimension-bound node records the fibre correspondence and
base-change dependencies it actually uses.

The node also no longer needs `lem-weil-pbc-noetherian-local-finite-krull-dimension`:
choosing any maximal ideal of E suffices after proving the upper bound globally.
It no longer directly needs `lem-weil-pbc-localization-ring-weakly-etale`: only flatness
of the product projection and its canonical localized map is used; their existing
Mathlib APIs suffice. It no longer directly needs `def-weil-pbc-ind-etale-algebra`
or `lem-weil-pbc-fibre-ring-primes-bijection`, which are instead direct dependencies
of the new proved general dimension bound. All other original dependencies remain.
No whole library module is withdrawn; these nodes may remain reachable elsewhere.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The normalization route is preserved and shortened:
the old Step 2 maximal-height chain choice is unnecessary; the upper bound can be proved
before choosing a maximal ideal. The old Step 3 base-change identification proving weak
etaleness of the localized map is also unnecessary, because only its flatness is used.
The old Step 6 finite-subalgebra argument is replaced by the proved absolute-flatness API.
The unit record has no realized statement or step binding this node, and no unit route
is bypassed. Edge cases include dimension zero, arbitrary base and target universes,
and the zero complementary factor when the target has only one minimal prime.
The new dimension bound also applies to zero rings and infinite-dimensional rings.

## New nodes

`lem-exc-weakly-etale-dimension-upper-bound`, in
`dag/nodes/sec-smooth-purity/lem-exc-weakly-etale-dimension-upper-bound.json`, records
`Algebra.WeaklyEtale.ringKrullDim_le` in `Sheaf.RingTheory.WeaklyEtaleDimension`.
Its statement is a strictly simpler general part of the source argument: an upper
bound only, with no normalization, catenarity, localness or component quotient.
Its complete Lean proof is delivered. Source text read: Stacks More on Algebra,
`lemma-absolutely-flat-over-absolutely-flat` (092I), `lemma-absolutely-flat` (092F),
and the first paragraph of `lemma-absolutely-flat-over-field` (092Q).
Searched the blueprint using `blueprint_refs.py search`, the DAG and both Lean roots,
and ran Lean Finder, Loogle, grep and LeanSearch via the required search wrapper.
No existing declaration or blueprint node states the general dimension bound.
No change record is needed: existing signatures and definitions are unchanged.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
