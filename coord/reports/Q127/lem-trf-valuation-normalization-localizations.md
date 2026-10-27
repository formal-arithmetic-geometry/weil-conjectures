## Worker report

The module `Sheaf.RingTheory.ValuationNormalizationLocalizations` states
`ValuationSubring.integralClosure_maximal_localizations`, with one `sorry` and no new
definitions. The node's other fields are unchanged. There is no statement correction,
new node, dependency repair, or statement dispute.

The source read was Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
Section 2.1's paragraph beginning “If L/k is a finite extension of abstract fields” and
Proposition 2.2.1's converse proof, printed p. 11:
https://arxiv.org/html/0707.3953v3#S2.SS2 . The former explicitly treats finite extensions
of abstract fields, so the separability and height-one hypotheses of Proposition 2.2.1
are not hypotheses of this background normalization statement. Bourbaki VI Section 8.6
Proposition 6 is still listed as wanted; it was not consulted. The local Stacks
`algebra.tex` lemmas `lemma-dominate`, `lemma-valuation-ring-normal`, and
`lemma-x-or-x-inverse-valuation-ring` were also read. The declaration docstring records
all nine proof steps of the DAG node, including the polynomial-tail calculation.

Hypotheses and clauses, in order:

- Fields K and L and their inclusion: `(K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L]`. The inclusion is `algebraMap K L`, automatically injective for fields.
- Finite algebraic extension: `[FiniteDimensional K L]`. A finite-dimensional field
  extension is algebraic; there is no separability binder.
- V is a valuation subring of K, with fraction field K: `(V : ValuationSubring K)`.
  This existing bundled notion has exactly the element-or-inverse condition, including
  zero, and its Mathlib instances give `ValuationRing V` and `IsFractionRing V K`.
  The zero clause is automatic in a subring and does not strengthen the node.
- C is the specified monic-polynomial integral closure: `integralClosure V L`, the
  Mathlib subalgebra whose carrier is `{x | IsIntegral V x}`. Its V-algebra and embedding
  into L are the canonical ones induced by the inclusion V into K and K into L.
- Nonzero integral domain: `Nontrivial (integralClosure V L)` and
  `IsDomain (integralClosure V L)` are the first two conjuncts.
- Integral over V: `Algebra.IsIntegral V (integralClosure V L)` is the third conjunct.
- Fraction field L: `IsFractionRing (integralClosure V L) L` is the fourth conjunct.
- Nonempty set of maximal ideals: `Nonempty (MaximalSpectrum (integralClosure V L))`.
- Every maximal ideal n: the next conjunct quantifies over that maximal spectrum.
  Its `asIdeal.primeCompl` is exactly C minus n.
- The localization as a subring of L: `Localization.subalgebra.ofField` at that
  complement, followed by `.toSubring`. The explicit fraction-field proof argument is
  the existing `integralClosure.isFractionRing_of_finite_extension K L`; this does not
  assume the conclusion as a hypothesis or choose any noncanonical map. The carrier
  consists of the actual fractions `a * s⁻¹` in L, and the existing instance
  `Localization.subalgebra.isLocalization_ofField` identifies this as the localization
  of C at n, the same notion as `Localization.AtPrime n`.
- This localization is a valuation ring: there exists `W : ValuationSubring L` whose
  underlying subring is equal to that concrete localization. Its valuation property
  is part of the existing bundled type, not an additional assumed property of C.
- Its intersection with K is V: `W.comap (algebraMap K L) = V`. This is equality of
  valuation subrings of K, hence exactly the inverse image/intersection in the node.
- Conversely every valuation subring W of L: `∀ W : ValuationSubring L` in the final
  conjunct, subject exactly to `W.comap (algebraMap K L) = V`.
- W is a unique maximal localization: `∃! n : MaximalSpectrum (integralClosure V L),
  W.toSubring = ...`. Equality is inside L, not an abstract ring isomorphism, and
  uniqueness is uniqueness of the maximal ideal itself.
- The final exclusion of extra assumptions is respected: there are no henselian,
  Noetherian, rank, separability or module-finiteness hypotheses on C/V.

Recorded statement dependencies used:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`.
  Read its full signature/docstring in Defs.lean, lines 95 onward.
- `def-trf-valuation-ring`: `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing`
  and `ValuationRing.TFAE` (including `iff_isInteger_or_isInteger`). The concrete
  subring interface is the existing `ValuationSubring`, in
  `Mathlib.RingTheory.Valuation.ValuationSubring`, lines 35 onward; its fraction-field
  instance was read at lines 153 onward. This is the same valuation-ring notion with
  the embedding in K retained, not a private copy or a dependency repair.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`, lines 216 onward; and `IsIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, line 53.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `IsLocalization.AtPrime`, lines 46 onward. The concrete in-field realization is the
  already existing `Localization.subalgebra.ofField` from
  `Mathlib.RingTheory.Localization.AsSubring`; its full construction, carrier and
  localization instance were read. No new localization notion is introduced.

All statement-dependency modules are public imports, directly or through the public
Mathlib imports that supply their definitions. The additional public import
`Mathlib.RingTheory.Localization.Integral` supplies the named canonical fraction-field
proof used in the signature; `Mathlib.RingTheory.Spectrum.Maximal.Basic` supplies the
maximal-ideal type.

Stated proof dependencies are imported with plain imports, unless already supplied by
public imports: integral closure and localization normality from
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`; lying over from
`Mathlib.RingTheory.Spectrum.Prime.Topology`; integral primes above maximal ideals,
going up and incomparability from `Mathlib.RingTheory.Ideal.GoingUp`; valuation
domination and the integral-closure intersection criterion from
`Mathlib.RingTheory.Valuation.LocalSubring`; inverse/nonunit criterion from the public
valuation-subring module; `ValuationSubring.comap_eq_of_toLocalSubring_le` from
`WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`; and
`isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse` from
`Sheaf.RingTheory.ValuationRingNormal`. The two project declarations and their
docstrings were opened and read. No import needs to be omitted for an import cycle.

Edge cases checked mathematically before writing:

- V = K (the trivial valuation): C = L, its only maximal ideal is zero, localization
  there is L, and any prolongation containing K must be L because L/K is algebraic.
- L = K: C = V since valuation rings are integrally closed; the unique maximal
  localization is V itself. This includes a field V with zero maximal ideal.
- Purely inseparable extensions are included; no separability assumption appears.
- General higher-rank and non-Noetherian valuation rings are included. C is not assumed
  finite as a V-module. No discrete or real-valued valuation is chosen.
- Maximal ideals are proper and hence prime, so their complements exclude zero;
  `primeCompl_le_nonZeroDivisors` makes each canonical localization well typed.
- The polynomial-tail proof includes the boundary indices k = 0 and k = r and the
  relation of degree one. Zero lies in every valuation subring and does not cause an
  inverse exception in the statement.
- The universes u and v are independent; no field or index-universe case is excluded.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder`, query: “The integral closure of a valuation ring in a
  finite field extension has valuation rings as its maximal localizations, and all
  extending valuation rings arise uniquely this way”. Eight hits, including
  `Valuation.Integers.integralClosure`, integrally-closedness results and
  `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn`; no exact match.
- `msearch.py ... loogle`, query `ValuationSubring, integralClosure`: six hits,
  `iInf_valuationSubring_superset` and the discrete-valuation algebra instances;
  no maximal-localization classification.
- `msearch.py ... leansearch`, query: “Localizations at maximal ideals of the integral
  closure of a valuation ring classify its extensions to a finite field extension”.
  Eight hits on local normality, localization of integral closures and localizations
  at primes; no exact match.
- `msearch.py ... grep`, query `localization|integralClosure`, subdirectory
  `RingTheory/Valuation`: 25 hits. This located `Localization.subalgebra.ofField` as
  used in `ValuationSubring.ofPrime`, which provided the existing in-field realization.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for valuation,
  normalization, integralClosure and localization combinations found related
  normalization and valuation modules, but no classification statement. A direct
  search for the item id in `lean/WeilConjectures` returned none. A name-clash search
  for `integralClosure_maximal_localizations` in Mathlib, the upstream-name index,
  `lean/WeilConjectures`, and `lean/Sheaf` returned none.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers. The
initial module-mode API probe and the completed statement both compiled cleanly on the
server. Diagnostic `#check` commands were removed from the completed module.

## Second reading by Q127

This is a separate second pass by the same dispatcher worker; no second agent was
started, as the brief forbids it. The maintainer's independent review remains external
to this delivery. I reopened the node and final module and compared all seven
conjuncts and both quantified parts. The field, extension and valuation-ring binders
match the hypotheses. The first five conjuncts give exactly the domain, integrality,
fraction-field and nonemptiness clauses. The existential valuation subring in the
sixth conjunct is required to equal the canonical in-field localization, and its
comap equality is the required intersection with K. The last conjunct quantifies over
all extending valuation subrings and asserts uniqueness of the maximal ideal, without
adding a containment assumption or weakening equality to isomorphism. The canonical
fraction-field proof used to type the localization is an existing theorem, not an
extra binder. The identity extension, trivial valuation, inseparable and higher-rank
cases remain covered. No mathematical mismatch was found; only explicit private proof
dependency imports were added after this reading. There are no new nodes or dependency
modules to review.
