## Worker report

The module `Sheaf.RingTheory.NormalizationPrincipalHeightOneRefinement` states
`RingTheory.normalization_principal_height_one_refinement`.  It uses Mathlib's
`integralClosure R (FractionRing R)` as the normalization of the commutative
Noetherian domain `R` in its fraction field.  No definition is introduced and
no existing declaration has the exact statement.

The Lean statement renders the node sentence clause by clause as follows.

* `R : Type u` with `[CommRing R]` is the commutative ring, `[IsDomain R]`
  expresses that it is a nonzero ring without zero divisors, and
  `[IsNoetherianRing R]` is the node's Noetherian hypothesis.
* `[IsLocalRing R]` expresses that `R` has a unique maximal ideal.
* `integralClosure R (FractionRing R)` is the node's `N`, with `FractionRing R`
  the field `K = Frac(R)`.
* `(b : integralClosure R (FractionRing R))` and `hb : b ≠ 0` render
  `0 ≠ b ∈ N`.
* `P : Ideal (integralClosure R (FractionRing R))` with `[P.IsPrime]` renders a
  prime ideal `P ⊂ N`; `hbP : b ∈ P` renders that `P` contains `b`.
* The conclusion gives an ideal `Q` with `Q.IsPrime`, `Q ≠ ⊥`, and
  `∀ Q', Q'.IsPrime → Q' < Q → Q' = ⊥`; these are exactly that `Q` is a
  nonzero prime with no prime strictly between it and `(0)`.  `Q ≤ P` is
  `Q ⊆ P`, and `b ∈ Q` says that it contains `b`.
* There is no hypothesis asserting Noetherianity of `N`; only `R` carries
  `[IsNoetherianRing R]`.

The statement dependencies are used directly from their recorded Mathlib
interfaces:

* `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
* `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure` and
  `IsIntegral` (with `FractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`).

I checked edge cases before writing the statement: `b = 0` is excluded by
`hb`; `Q ≠ ⊥` excludes the zero prime; the universal strict-subprime clause
allows no intermediate prime; `Q ≤ P` permits equality; a field (where no
nonzero prime can contain a nonzero `b`) is covered vacuously; and no
Noetherian assumption is imposed on the normalization.

Searches made:

* `msearch.py ... leanfinder "commutative noetherian local integral domain
  normalization height one prime containing nonzero element"`: only unrelated
  Dedekind/height-spectrum declarations; no exact match.
* `msearch.py ... grep "height.*one|height.*prime|normalization" RingTheory`:
  Mathlib height and Dedekind results, all with stronger hypotheses; no exact
  normalization refinement.
* `rg -n "principal-height|height-one|integralClosure|normalization"` in
  `lean/Sheaf` and the slopmaster2 `WeilConjectures` source: found the
  surrounding `NormalizationIntegralClosureKrull` module, but no declaration
  of this theorem.
* `grep -rl
  "lem-trf-normalization-principal-height-one-refinement"` in the project
  Lean/source trees: only a proof-plan docstring, not a matching declaration.

The module compiled cleanly with
`scompile.py NM lem-trf-normalization-principal-height-one-refinement`.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
