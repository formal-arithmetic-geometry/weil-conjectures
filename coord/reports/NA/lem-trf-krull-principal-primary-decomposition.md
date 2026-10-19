## Worker report

The module `Sheaf.RingTheory.KrullPrincipalPrimaryDecomposition` states
`RingTheory.krull_principal_primary_decomposition`. Its only declaration is this theorem,
with whole proof `sorry`. No definition, extra node, dependency repair, or statement correction
is needed. Only the item's `lean` field changes.

Source read: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Definition
4.10.1 and Proposition 4.10.3 with proof, printed p. 89 (PDF page index 102),
https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf . The source gives exactly the three
Krull conditions and the contractions of the localized principal ideals. The node asks for
the intersection and radical clauses rather than the additional minimality/primary-property
conclusions of the proposition; no extra conclusions were inserted.

Hypothesis and clause correspondence:

- A commutative integral domain is `(D : Type u) [CommRing D] [IsDomain D]`.
  The universe `u` is explicit and unrestricted. `IsDomain` excludes the zero ring.
- Height-one primes are `P : PrimeSpectrum D` with `P.asIdeal ≠ ⊥` and
  `∀ Q : Ideal D, Q.IsPrime → Q < P.asIdeal → Q = ⊥`. This is literally the node's
  description. `PrimeSpectrum.isPrime` supplies the prime instance for localizations.
- Krull condition (i) is `hlocal`: each such prime's `Localization.AtPrime P.asIdeal`
  is `IsNoetherianRing`, `IsDomain`, and `IsIntegrallyClosed`.
- Condition (ii) is `hintersection`: the image `Set.range (algebraMap D (FractionRing D))`
  equals the intersection, over precisely those height-one primes, of
  `Localization.subalgebra.ofField (FractionRing D) P.asIdeal.primeCompl
  P.asIdeal.primeCompl_le_nonZeroDivisors`, coerced to a set. The Mathlib definition's
  carrier is exactly fractions a/s with s outside P. Thus these are the canonical local
  rings inside the fraction field, with no arbitrary embedding or chosen isomorphism.
  The nested `Set.iInter` over the height conditions is the whole field if there are no
  height-one primes, exactly as specified.
- Condition (iii) is `hfinite`, for every nonzero `x : D`: `Set.Finite` of the set of
  height-one primes containing x. No global Noetherian or dimension-one hypothesis on D
  is imposed.
- The chosen nonzero element is `(b : D) (hb : b ≠ 0)`.
- The finite list `P₁,...,Pₜ` is `∃ (t : ℕ) (P : Fin t → PrimeSpectrum D)` with
  `Function.Injective P`; its exactness is the following biconditional for every prime Q:
  `(∃ i : Fin t, P i = Q) ↔ Q is height one and b ∈ Q.asIdeal`.
  Existence of this duplicate-free list is equivalent to finiteness of the specified set.
- Each Jᵢ is written directly as `Ideal.comap (algebraMap D (Localization.AtPrime
  (P i).asIdeal)) (Ideal.span {algebraMap D (Localization.AtPrime (P i).asIdeal) b})`.
  This is exactly the inverse image of bD_(Pᵢ). It uses Mathlib's canonical map and ideals,
  without introducing a redundant helper definition.
- The principal ideal equality is `Ideal.span ({b} : Set D) = ⨅ i : Fin t, Jᵢ`.
- The radical clause is `∀ i : Fin t, Jᵢ.radical = (P i).asIdeal`.
  Mathlib's radical allows exponent zero; this gives the same ideal as the node's positive
  exponent convention: exponent zero implies 1 ∈ J, hence J = ⊤, and exponent one then
  witnesses membership for every element. In this statement each Jᵢ is in fact proper.
- With `t = 0`, the ideal infimum is `⊤`, i.e. D, and the radical clause is vacuous.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, the Noetherian self-module abbreviation; read the
  underlying `IsNoetherian.noetherian` and `isNoetherianRing_iff_ideal_fg` too.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed` from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, together with `IsDomain`, exactly
  the recorded normal-domain inline interface. The node needs normal domains only.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` and `algebraMap` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, localization at `P.primeCompl`.
- Additional existing Mathlib constructions: `PrimeSpectrum`/`PrimeSpectrum.isPrime`,
  `Localization.subalgebra.ofField` in `Mathlib.RingTheory.Localization.AsSubring`,
  `Ideal.primeCompl_le_nonZeroDivisors`, `Ideal.span`, `Ideal.comap`, and `Ideal.radical`.
  Read `ofField`'s full definition/docstring and `Ideal.radical`'s definition before writing.
- All already stated proof dependencies' modules are imported without `public`:
  `WeilConjectures.AlgebraicGeometry.Regular` (recorded
  `AlgebraicGeometry.IsRegular.of_isIntegrallyClosed_stalk`; also read the underlying
  `IsRegularLocalRing.of_isIntegrallyClosed` in
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`),
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`
  (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`), and
  `Mathlib.RingTheory.Ideal.Height` (`IsLocalization.AtPrime.ringKrullDim_eq_height`).
  The fourth proof dependency, `Localization.AtPrime.under_maximalIdeal`, is in the
  already publicly imported localization module. The proof docstring explains all four
  dependencies, the uniformizer radical calculation, and both inclusions in the equality.

Edge cases checked: b a unit gives an empty prime list and the unit ideal; D a field has
no height-one primes and the fraction-field intersection convention holds; t = 0 has no
radical assertions; the zero ring and b = 0 are excluded exactly as in the node. No
characteristic, global dimension, finite generation, or global Noetherian assumption was
introduced. Nothing is disputed; the node's statement requires no correction.

Searches for an existing statement (raw service results are in `searches.jsonl`):

- msearch.py leanfinder, query "Every nonzero principal ideal in a Krull domain is the
  finite intersection of its contractions from height one localizations, with radicals
  equal to those primes": eight hits. The Dedekind factorization/intersection results
  have stronger domain assumptions; the prime-spectrum product result assumes Noetherian.
- msearch.py loogle, query `"primary", "principal"`: zero hits.
- msearch.py grep, query `KrullDomain|isKrull|principal.*primary`, RingTheory: zero hits.
- msearch.py leansearch, query "In a Krull domain the principal ideal generated by a
  nonzero element is the finite intersection of the contractions of its height one
  localizations": eight hits, again Dedekind factorization and localization height;
  none gives the present Krull-domain theorem.
- Direct rg of `KrullDomain|isKrull|principal.*primary|krull_principal_primary` in
  WeilConjectures and lean/Sheaf found the landed normalization theorem and its consumer's
  proof plan, but no existing decomposition theorem. The normalization theorem states
  that a particular ring is Krull, not the present decomposition result. Direct grep of
  the exact item id in WeilConjectures found no declaration.
- Direct rg of the chosen declaration/module names in `dag/lean_names_upstream.json`,
  Mathlib, WeilConjectures and lean/Sheaf found no collision.
- Read Mathlib `RingTheory/Lasker.lean`: `IsLasker` assumes finite primary decompositions
  for all submodules; `exists_isMinimalPrimaryDecomposition` requires that property.
  It does not supply this result from the three Krull conditions.

Validation: prescribed scompile.py compiled the single delivered module both as its sandbox
probe and at its library module path, cleanly (1.7 s / 1.9 s). All binders and the universe
are explicit; autoImplicit is false; every line is at most 100 characters.

## Second reading by NA

Author self-check, with the node and final file open; independent review is supplied by the
maintainer, as specified by the dispatcher. Re-read the three hlocal/hintersection/hfinite
hypotheses against Definition 4.10.1, the nonzero b binder, and the exact finite list
biconditional. Checked that P ranges over all prime ideals rather than just maximal ideals,
that the height condition excludes zero and allows only zero strictly below P, and that
the canonical localization subalgebra uses the complement of that same P. Re-read every
occurrence of `(P i).asIdeal` in both contractions: b is mapped into that localization,
then the span is contracted back to D. Confirmed the same Jᵢ occurs in the intersection
and radical clauses. No IsPrimary or minimality conclusion beyond the node is asserted;
no source assumption is missing. The canonical Mathlib constructors avoid new definitions.
The empty intersection and positive-exponent radical conventions were checked as above.
No mismatch was found and no node correction was made.
