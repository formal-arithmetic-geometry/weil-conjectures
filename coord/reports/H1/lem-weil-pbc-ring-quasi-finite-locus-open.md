## Worker report

The module `lean/Sheaf/RingTheory/QuasiFiniteLocusOpen.lean` states that for commutative
rings `A` and `B`, an `A`-algebra `B` of finite type has an open locus
`{q : PrimeSpectrum B | IsQuasiFiniteAtPrime A B q}`. It also states the equivalent local
form: every point of this locus admits `g : B` outside its prime such that every prime of
`Localization.Away g` is quasi-finite for the induced `A`-algebra.

The binders `[CommRing A]`, `[CommRing B]`, `[Algebra A B]`, and
`[Algebra.FiniteType A B]` render the finite-type ring-map hypotheses. The set-builder
renders the quasi-finite locus in `Spec B`; `IsOpen` renders openness. The implication and
existential binders render the pointwise localization form, with `g ∉ q.asIdeal` and all
primes `p : PrimeSpectrum (Localization.Away g)` exactly as in the node. The proof is
`sorry`, as required for stage 2.

The dependency declaration used is `Algebra.IsQuasiFiniteAtPrime` from
`Sheaf.RingTheory.QuasiFiniteAtPrime`; `Algebra.FiniteType` is Mathlib's declaration in
`Mathlib.RingTheory.FiniteType`, `AlgebraicGeometry.Spec` is Mathlib's affine spectrum,
and `Localization.Away` is Mathlib's principal localization. The localization finite-type
instance is supplied by Mathlib's `IsLocalization` instance from
`Mathlib.RingTheory.Localization.InvSubmonoid`.

Edge cases checked: the finite-type bound permits zero generators; `g` is only required to
avoid the chosen prime (so units and the empty basic open are represented); no nonemptiness,
domain, field, or characteristic assumptions are added; universes `u` and `v` allow distinct
ring sizes.

Searches made: `msearch.py leanfinder` for “quasi finite locus of finite type ring map is
open” returned no exact ring-level declaration; `msearch.py loogle` for
`AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt` found only the scheme-level theorem;
`msearch.py grep` and `rg` over pinned Mathlib found no ring-level openness theorem. Searches
of `WeilConjectures/` and `lean/Sheaf` found no existing statement of this lemma. The recorded
Mathlib candidate `Scheme.Hom.isOpen_quasiFiniteAt` requires an additional comparison with
the ring-level definition, so it is not an exact match.

## Earlier second reading (a previous round; superseded)

I reread the node and the module line by line. The module binds exactly the two rings, their
commutative-ring structures, the algebra structure, and finite-type hypothesis. Its first
conjunct is the open subset assertion. Its second conjunct is the stated equivalence, with
one chosen element outside each quasi-finite prime and the universal quantifier over primes
of the principal localization. No assumptions on nonemptiness, reducedness, characteristic,
or fields were introduced, and the source's zero-generator case remains included.

## Second reading by H1

The node introduces commutative rings `A` and `B` (possibly in distinct universes), an
`A`-algebra structure on `B`, and finite type. It defines the locus in `PrimeSpectrum B`
using `Algebra.IsQuasiFiniteAtPrime`; the conclusion has two clauses: that this set is
`IsOpen`, and that openness is equivalent to the pointwise existence of `g ∉ q.asIdeal`
for which every `p : PrimeSpectrum (Localization.Away g)` is quasi-finite for the induced
`A`-algebra. The Lean binders and conjunction in `Algebra.isOpen_isQuasiFiniteAtPrime`
render these clauses exactly, with no added hypotheses or altered quantifier order.

The source is Stacks Algebra Lemma 00QA (lines 30880–30904). Its proof proceeds through a
finite subalgebra, finite-map quasi-finiteness, localization, prime correspondence, and
basic-open coverage. I expanded the statement docstring to record these proof steps and
all cited blueprint nodes. Edge cases remain covered: zero-generator finite type, zero or
empty spectra, units or empty basic opens, arbitrary characteristic, and distinct ring
universes. No existing exact ring-level declaration was found in Mathlib, WeilConjectures,
or Sheaf; the scheme-level `Scheme.Hom.isOpen_quasiFiniteAt` is a different notion.

The only mismatch was documentary: the worker docstring named the proof dependencies but
did not give the node's step-by-step proof. I repaired that docstring; the Lean signature
itself required no change. The module compiles cleanly with only the intended `sorry`.
