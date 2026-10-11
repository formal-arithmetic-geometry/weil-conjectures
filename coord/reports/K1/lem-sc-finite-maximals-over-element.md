## Worker report

The module states `Ring.finite_maximalIdeals_containing_nonzero` for a commutative,
Noetherian domain `R` of Krull dimension exactly one. Its conclusion is that the set of
ideals `m` satisfying `m.IsMaximal ∧ x ∈ m` is finite for every nonzero `x : R`.

The Lean rendering of each hypothesis is:

- “`R` is a Noetherian domain” is `(R : Type u) [CommRing R] [IsDomain R]
  [IsNoetherianRing R]`.
- “Krull dimension 1” is `(h_dim : ringKrullDim R = 1)`.
- “for every nonzero `x`” is `(x : R) (hx : x ≠ 0)`.

The conclusion is exactly `Set.Finite {m : Ideal R | m.IsMaximal ∧ x ∈ m}`: the set
ranges over ideals of `R`, requires maximality, and requires membership of `x`.
The proof is `sorry` as required at stage 2; its docstring records the source proof and
its two proof dependencies.

The dependency notions used are Mathlib's `IsNoetherianRing` and `ringKrullDim`, as
recorded by `def-weil-pbc-noetherian-ring` and `def-weil-pbc-krull-dimension-ring`.
The module uses the Mathlib declarations directly; no dependency module is needed.

Edge cases checked: `x = 0` is excluded by `hx`; the theorem permits all universes via
`Type u`; the set may be empty, and `Set.Finite` allows that. The exact dimension
hypothesis allows the stated one-dimensional case, including all Noetherian domains
satisfying the equality.

Searches for an existing declaration:

- `msearch.py leanfinder "finite set maximal ideals containing nonzero element one dimensional Noetherian domain"` returned only related results (`IsDedekindRing.toDimensionLEOne`, field maximal-spectrum finiteness, and PID facts), with no matching theorem.
- `msearch.py loogle "ringKrullDim IsNoetherianRing maximal ideal finite"` returned no result (the query had an application-type mismatch).
- `rg` over Mathlib `RingTheory` for finite maximal-spectrum declarations found only unrelated
  semilocal/fraction-ring results; no theorem for maximal ideals containing a fixed nonzero
  element in a one-dimensional Noetherian domain.
- `rg` over `lean/Sheaf` and `WeilConjectures` found no existing declaration of this result.

No `STATEMENT-DISPUTED` issue or node fault was found.

Server compilation: clean, with no warnings or errors.

Additional searches: `msearch.py leansearch` with query "finite maximal ideals containing nonzero element Noetherian domain Krull dimension one" was unavailable (Internal Server Error). `msearch.py grep` for `finite.*maximal|finite.*Maximal|IsMaximal.*[Ff]inite` in RingTheory returned 25 hits, including the Artinian-ring maximal-ideal finiteness lemma; none has this theorem's hypotheses and conclusion. The Noetherian and Krull-dimension dependency signatures and docstrings were read in `Mathlib/RingTheory/Noetherian/Defs.lean` and `Mathlib/RingTheory/KrullDimension/Basic.lean`. The theorem name was also checked against `dag/lean_names_upstream.json`, Mathlib, the source project, and `lean/Sheaf`, with no collision.

Source checked at [Stacks Tag 00PF](https://stacks.math.columbia.edu/tag/00PF),
Lemma 10.119.11, first sentence of its proof (the local literature file is absent on
this machine). The lemma assumes a Noetherian domain of dimension one; its proof uses
finiteness of the maximal ideals containing a nonzero element. The present node captures
precisely that support assertion. A unit element gives an empty set of maximal ideals,
which the conclusion includes. The zero ring and fields cannot satisfy the domain and
exact dimension-one assumptions together; no additional exclusion was added.

## Second reading by K1

I read the node statement, dependency records, Lean module, and Stacks Tag 00PF
independently. The objects and hypotheses match item by item:

- The node's Noetherian domain `R` is rendered by `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R]`. These are the recorded dependency and Mathlib
  notions, with no stronger finiteness or field assumption.
- Dimension one is exactly `(h_dim : ringKrullDim R = 1)`. The dependency declaration
  identifies `ringKrullDim` with the supremum of strict prime-chain lengths.
- The universal nonzero element clause is `(x : R) (hx : x ≠ 0)`.
- The conclusion is exactly `Set.Finite {m : Ideal R | m.IsMaximal ∧ x ∈ m}`:
  ideals are quantified, and both maximality and containment of `x` are retained.
  The binder order is `R`, assumptions, dimension, `x`, then `hx`, as in the node.

The source page (Stacks Tag 00PF, Lemma 10.119.11, proof) states that in a
Noetherian one-dimensional domain a nonzero `x` lies in finitely many maximal primes.
Its surrounding lemma introduces a fraction field and module, but those objects are
not part of this extracted support assertion, so Lean correctly omits them. No
mismatch was found and no code or node repair was required.

Edge cases checked: `hx` excludes `x = 0`; a unit yields the empty finite set; the
set may be empty; `Type u` leaves the universe unrestricted; domain and exact
dimension-one assumptions exclude the zero ring and fields.

Searches were repeated with LeanFinder/Loogle-style queries and `rg` over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and upstream name records. Results were only related
field, Dedekind, and Artinian lemmas; no declaration states this result. The dependency
declarations `IsNoetherianRing` and `ringKrullDim` were opened and used directly.
