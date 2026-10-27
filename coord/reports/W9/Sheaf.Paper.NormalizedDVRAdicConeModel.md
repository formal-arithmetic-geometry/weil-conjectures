## What changed

The original statement of `WeilConjectures.normalizedDVR_adic_cone_model` is preserved.
Its proof constructs flat-term K-flat finite-coefficient representatives by successor
induction using right fractions and K-flat resolutions. It constructs compatible chain
maps, restricts them to completed coefficients, and inserts the zero complex at exponent
zero. The level isomorphisms and their successor compatibility are proved explicitly.

The scalar ring is the ring of compatible sections of the actual completed coefficient
sheaf. Its action and uniformizer are explicit constructions. Flat tensor exactness,
completed-projection divisibility and scalar regularity prove annihilation and exactness
of the scalar short complexes. Exact countable products give CountableAB4Star and hence
countable products in the derived category.

Two new modules isolate the remaining genuine steps: scalar-cokernel normalization of
an already constructed strict flat model, and the bounded-free tensor comparison for an
already supplied strict normalized model. The main proof combines these with the
explicit constructions. No definition contains a sorry, and no arbitrary data is chosen
from either new unproved theorem. Finite representatives are chosen using proved
resolution and right-fraction existence theorems.

## Proved and sorry left

Original holes closed syntactically: one,
`WeilConjectures.normalizedDVR_adic_cone_model`.
Original holes remaining: zero. New holes: two:

- `WeilConjectures.normalizedDVR_flat_cokernel`
  (`lem-coef-normalized-dvr-flat-cokernel`).
- `WeilConjectures.normalizedDVR_bounded_free_cone`
  (`lem-coef-normalized-dvr-bounded-free-cone`).

This is a decomposition, not a sorry-free proof of DVR effectivity: one original
hole is reduced to two strictly smaller obligations. All private helper proofs in the
item module are complete. The scalar cokernel lemma constructs no tower or limit;
the bounded-free lemma assumes the tower, normalization, level identifications and
products, and supplies only the cone comparison and its actual-map equation.

## No longer needed

No original public import is removed and no library module is withdrawn. The route
uses the adopted strict adic tower interface and preserves the unit route. The already
proved nilpotent-fibre calculation is not repeated.

The unimported retained draft `Sheaf.Algebra.Homology.SheafPrincipalReductionDatum`
is preserved only in scratchpad and is not a delivery dependency. Unused exploratory
proof imports of `WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum`
and `Sheaf.Algebra.Homology.CochainDerivedAdjunction` were removed from the item.
The unused `Sheaf.Algebra.Homology.RegularQuotientFlatSequence` and
`Sheaf.Algebra.Homology.RegularQuotientConeChain` proof imports were replaced by
the smaller `RegularQuotientConeBasic` interface actually used.
No global pruning is claimed for them: other existing declarations still use them,
and the latter remains a dependency in the normalization node's proof plan.

The item's updated node does not directly use the original completion-flatness,
DVR-domain, long-exact-sequence, generic derived-change-of-rings or generic derived
adjunction nodes: it uses the already specialized projection-divisibility, scalar
regularity, restriction-composition and K-flat declarations. Tensor and adjunction
steps still needed by the bounded-free calculation are recorded on that new node.
These are dependency-route changes, not assertions that those source modules can be
deleted from the library. The exact original direct dependency removals are:

- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-weil-pbc-constant-completion-equivalence`.
- `def-pc-kflat-complex`.
- `def-pc-tensor-complex-sheaves`.
- `lem-sf-derived-homology-long-exact`.
- `lem-pur-derived-change-of-rings`.
- `lem-coef-strict-normalized-adic-cone-limit`.
- `def-pc-sheaf-restrict-scalars`.
- `lem-pc-derived-adjoint-functors`.


## Where the brief, the DAG or earlier work was wrong

The earlier server disk-space failure no longer prevents compilation. The retained
attempt's general quotient-transition proof and principal-reduction datum draft were
unfinished; they have not been presented as proved dependencies. The actual source
strictification is for constant-ring sheaves, so it cannot directly instantiate the
completed ring-sheaf interface; its successor-induction argument is reproduced using
the independent-coefficient resolution API.

The concrete recursive representative and coefficient constructions initially caused
expensive unfolding. Local irreducibility of the recursive models and tensor comparison
keeps the proofs within the ordinary per-file compile limit; no limit was raised and
no file was split to evade that limit. The new modules separate mathematical obligations.

## New nodes

`lem-coef-normalized-dvr-flat-cokernel` states only that normalization of the finite
semilinear tower makes its scalar cokernel descent a quasi-isomorphism. Its assumptions
include the chosen K-flat complexes, flatness, representation equations and annihilation.
The docstring explains the coefficient quotient, flat tensor and universal-arrow argument,
including equal-index and zero-exponent cases.

`lem-coef-normalized-dvr-bounded-free-cone` states the bounded two-term free tensor
comparison for a supplied strict normalized model. It fixes the actual completed scalar
action, requires the level identifications and successor equations, and proves no
strictification, normalization or product existence. Its docstring describes the Roos
cone and canonical augmented projection, including arbitrary-adjunction compatibility.

Both nodes use the current blueprint effectivity proof as source. No definition or
existing theorem signature changes, so no change record or forced adaptation is needed.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
