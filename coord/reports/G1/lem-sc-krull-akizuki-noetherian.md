## Worker report

The module `Sheaf.RingTheory.KrullAkizukiNoetherian` states
`krullAkizukiNoetherian`. It models a Noetherian domain `R`, its fraction field
`K`, a finite field extension `L/K`, and a commutative ring `D` with injective
algebra maps `R → D → L`. The `IsScalarTower` assumptions identify the two
maps from `R` into `L`; `ringKrullDim R = 1` is the dimension hypothesis and
`IsNoetherianRing D` is the conclusion. Every hypothesis appears as a typeclass
or explicit binder in the theorem signature. The proof is `sorry`, as required
for stage 2.

Dependencies used: `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`,
`ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic`, and
`IsFractionRing` from `Mathlib.RingTheory.Localization.FractionRing`.
The field-extension convention is Mathlib's `[Field K] [Field L]
[Algebra K L] [FiniteDimensional K L]`.

Edge cases checked: the theorem permits arbitrary universe levels for all four
rings/fields, allows `D = 0` only when the stated injectivity assumptions make
that possible, and does not exclude the zero ideal or any finite extension
degree. The dimension equality uses Mathlib's `WithBot ℕ∞`-valued
`ringKrullDim`, so the zero ring is excluded by the equality to `1`.

Searches made: `msearch.py leanfinder` for Krull–Akizuki intermediate-ring
Noetherianity (only integral-closure results); `msearch.py loogle` for
Noetherian finite extensions (no result); grep of Mathlib and
`WeilConjectures` for `Krull|integralClosure.*isNoetherian|isNoetherian.*integral`
(no matching theorem). The project search found no existing declaration of
this node.

## Earlier second reading (a previous round; superseded)

The node statement and module were read together. The Noetherian, domain,
one-dimensional, fraction-field, finite-extension, and intermediate-ring
hypotheses each have a corresponding Lean binder; injectivity expresses both
inclusions and the two scalar-tower assumptions enforce compatibility of the
embeddings. The conclusion is exactly `IsNoetherianRing D`. No mismatch was
found.

## Second reading by G1

I independently opened the item JSON, its Lean module, all three statement
 dependency nodes and the actual Mathlib declarations they record. I read
Stacks `algebra.tex`, `lemma-krull-akizuki`, including its proof and the
introduction to `section-krull-akizuki`, from the local source copy
`/home/ubuntu/c1-stacks-review/algebra.tex:29292` (the repository literature
checkout is absent). The source assumes no localness, normality, separability
or characteristic restriction for this lemma. Its intermediate ring is named
`A`; the node and Lean consistently rename it `D`.

Object/hypothesis/conclusion checklist, in the node's order:

- A commutative domain R: `{R : Type uR} [CommRing R] [IsDomain R]`.
  Exact; nontriviality is part of being a domain.
- R Noetherian: `[IsNoetherianRing R]`. Exact dependency
  `def-weil-pbc-noetherian-ring`: Mathlib's abbreviation is `IsNoetherian R R`,
  equivalent to finite generation of every ideal by
  `isNoetherianRing_iff_ideal_fg` in `Noetherian/Defs.lean`.
- Krull dimension exactly one: `(hdim : ringKrullDim R = 1)`. Exact dependency
  `def-weil-pbc-krull-dimension-ring`: `ringKrullDim R` is the Krull dimension
  of `PrimeSpectrum R` ordered by inclusion, with values in `WithBot ℕ∞`.
- K the fraction field of R: `{K : Type uK} [Field K] [Algebra R K]
  [IsFractionRing R K]`. Exact: `IsFractionRing` is localization at the
  nonzero divisors, which are precisely nonzero elements of the domain R.
- Finite field extension L/K: `{L : Type uL} [Field L] [Algebra K L]
  [FiniteDimensional K L]`. Exact dependency `def-pc-field-extension` uses
  this Algebra convention, not a special field extension. FiniteDimensional
  is the finite-module condition on a vector space. No separability assumed.
- Ring D with R contained in D contained in L: `{D : Type uD} [CommRing D]`,
  `[Algebra R D] [Algebra D L]`, and injectivity binders `hRD` and `hDL`.
  Exact: these give embeddings identifying D with its image subring in L.
  Commutativity follows from containment in the field and adds no restriction.
- Compatibility with the given embedding through K: `[Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R D L]`. Exact structural encoding of
  the inclusions, not an extra mathematical finiteness condition.
  `IsScalarTower.algebraMap_eq` identifies both composites with `algebraMap R L`.
  Although hRD also follows from these facts and hDL, its explicit inclusion
  merely restates the node's inclusion and does not strengthen the statement.
- Conclusion D Noetherian: `IsNoetherianRing D`. Exact and the only conclusion.
  All four types and every hypothesis are universally quantified before it;
  there is no hidden existential choice or restriction on D.

Edge cases: the zero ring is excluded for R by IsDomain and dimension one,
and for D by its injective map into the nontrivial field L. This matches
actual inclusions into a field. Degree-one extensions, D = R, D = L, and
purely inseparable finite extensions are all allowed. R cannot be a field
because its dimension must be one. There are no index-set, scheme or n binders;
the zero ideal is explicitly handled in the proof docstring. Independent
universes uR, uD, uK, uL cover all sizes. No variable or universe is unbound.

Independent searches used alternative wording. `msearch.py leansearch` for
"Every subring containing a one dimensional Noetherian domain in a finite
extension of its fraction field is Noetherian" returned service unavailable
(Internal Server Error); no negative mathematical verdict is drawn from that.
`msearch.py leanfinder` for "A subalgebra of an algebraic extension of the
fraction field of a dimension one Noetherian integral domain is a Noetherian
ring" returned integral-closure Noetherianity and Dedekind-domain results.
I opened `IsIntegralClosure.isNoetherianRing` in
`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`: it assumes integral
closure, an integrally closed base and separability, so it is not this theorem.
`msearch.py grep` for `akizuki|isNoetherian.*(subalgebra|intermediate)|00PG`
returned no Krull-Akizuki theorem: its subalgebra hits assume finite generation
or Noetherianity as a module, unlike this node. Direct rg searches in Mathlib,
WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no existing
statement: the upstream Dominating module only mentions a related length
estimate in its introduction. No notion is missing: all notions used have
Mathlib definitions, and all recorded dependencies are usable. This delivery
has no new definition nodes, dependency modules or statement correction.

No semantic mismatch was found; the signature and JSON lean.statement are
unchanged and verbatim equal. The proof docstring previously compressed away
the clearing-denominators argument and the finite K-basis identification
needed to apply the finite-length node. I expanded those two steps, including
passage from D/xD to its submodule I/xD and lifting generators. No theorem
was proved; the sole proof remains `by sorry`. Header, namespaces, imports,
source/blueprint docstrings and the 100-character line limit were checked.
The original module compiled cleanly on the server; the final docstring edit
is checked again by the delivery dry run.
