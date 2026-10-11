## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SemilocalDimOneConductor.lean` states
`semilocal_dim_one_conductor` with `B` and `K` commutative rings, an algebra
structure, `IsDomain B`, `IsNoetherianRing B`, finite maximal spectrum (the
semilocal hypothesis), `IsFractionRing B K`, and `ringKrullDim B = 1`.
The integral closure is Mathlib's `integralClosure B K`.

The first conclusion `Finite (MaximalSpectrum (integralClosure B K))` renders
semilocality of `B'`. The second, `IsDedekindDomain (integralClosure B K)`,
renders the Noetherian one-dimensional integrally closed domain clause. The
third conclusion is `IsFractionRing (integralClosure B K) K`, rendering the
fraction-field equality. The final universal clause binds `x,y` in `B'`,
requires `x ≠ 0` and `x ∈ Ring.jacobson (integralClosure B K)`, and gives
`n : ℕ` with `0 < n` and `b : B` satisfying
`algebraMap B K b = (x : K)^n * (y : K)`, which renders `x^n y ∈ B`.

Dependencies are used through Mathlib declarations recorded by the nodes:
`IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs), `ringKrullDim`
(Mathlib.RingTheory.KrullDimension.Basic), `integralClosure`
(Mathlib.RingTheory.IntegralClosure.Algebra.Basic), and
`IsIntegrallyClosed`/`IsDomain` underlying `IsDedekindDomain`
(Mathlib.RingTheory.DedekindDomain.Basic). The Jacobson radical is
`Ring.jacobson` from Mathlib.RingTheory.Jacobson.Ideal.

Edge cases checked: `ringKrullDim` permits the zero-ring value but the
`IsDomain B` hypothesis excludes the zero ring; `n` is explicitly positive;
`x` is required nonzero; arbitrary universes are covered by `(B K : Type*)`;
`y` is universally quantified, including zero; and finite maximal spectrum
allows the one-maximal (local) case.

Searches made: `msearch.py leanfinder` for “integral closure of a semilocal
Noetherian one dimensional domain is semilocal Dedekind and conductor powers”
returned no exact declaration; `msearch.py loogle` for
`IsSemilocalRing, IsDedekindDomain, integralClosure, Ring.jacobson` returned
only the generic declarations used above; grep of Mathlib RingTheory for
`conductor.*integral closure|semilocal.*Dedekind|dimension one.*integral closure`
found no matching theorem; `rg` over `WeilConjectures` found no declaration of
this statement; and `rg` over `lean/Sheaf` found no existing module.
The recorded dependency declarations were checked at their source signatures.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The hypotheses correspond one by
one: commutative rings and algebra map, domain, Noetherian, finite maximal
spectrum, fraction field, and dimension one. `integralClosure B K` is exactly
the closure notion in the node. The three structural conclusions match
semilocal Dedekind with fraction field `K`; the last clause binds exactly the
nonzero Jacobson-radical element and arbitrary `y`, and expresses membership
in `B` by equality to the image of an element `b : B`. No mismatch was found.

## Second reading by K1

I read the node statement and the Lean file side by side. The objects and hypotheses match as follows: `B K : Type*` with `[CommRing B] [CommRing K]` gives the two commutative rings; `[Algebra B K]` gives the inclusion into the fraction ring; `[IsDomain B]` gives the domain hypothesis; `[IsNoetherianRing B]` gives Noetherianity; `[Finite (MaximalSpectrum B)]` gives finitely many maximal ideals (semilocality); `[IsFractionRing B K]` makes `K` the fraction field; and `h_dim : ringKrullDim B = 1` gives dimension one. The integral closure object is exactly `integralClosure B K`.

The conclusion clauses render the node in order: `Finite (MaximalSpectrum (integralClosure B K))` is semilocality of `B'`; `IsDedekindDomain (integralClosure B K)` is the Dedekind condition; `IsFractionRing (integralClosure B K) K` is the fraction-field assertion; and the universal clause quantifies `x,y : integralClosure B K`, assumes `x ≠ 0` and `x ∈ Ring.jacobson (integralClosure B K)`, then supplies `n : ℕ` with `0 < n` and `b : B` whose image satisfies `algebraMap B K b = (x : K)^n * (y : K)`, exactly expressing `x^n y ∈ B`. Quantifier order and all conjunctions agree. No mismatch was found or changed.

I checked edge cases: the finite-maximal-spectrum hypothesis includes the local and one-maximal cases; `y` is unrestricted (including zero); `x` is explicitly nonzero and `n` explicitly positive; the domain hypothesis excludes the zero ring; and `Type*` leaves universes unrestricted. The `IsFractionRing` assumptions and compilation permit the fraction-field case represented by the node.

For independent searches, LeanFinder (`integral closure semilocal Dedekind conductor`) returned only generic integral-closure/Dedekind declarations; Loogle/msearch for the full conductor statement returned no exact theorem; grep over Mathlib `RingTheory`, `WeilConjectures`, and the repository `lean/Sheaf` found no declaration of this statement. I opened the recorded dependency signatures and used Mathlib's `integralClosure`, `Ring.jacobson`, `IsDedekindDomain`, `IsNoetherianRing`, and `ringKrullDim` directly. The module compiles cleanly with `scompile.py`; no repair was necessary.

## Reviewer fix (R-sdc1303)

The statement was restated: the conclusion now includes `ringKrullDim (integralClosure B K) = 1` (the node says B' has Krull dimension 1; Mathlib's `IsDedekindDomain` allows a field); `K` is a `Field` and the binders follow the landed sibling `semilocal_normalization_dim_one` (K1 6c72e167a, `Type u`/`Type v`); the Jacobson radical is `Ideal.jacobson (⊥ : Ideal _)` as in the landed siblings, replacing `Ring.jacobson`.
