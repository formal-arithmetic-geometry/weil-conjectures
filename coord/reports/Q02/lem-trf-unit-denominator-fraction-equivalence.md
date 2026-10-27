## Worker report

The module `Sheaf.RingTheory.UnitDenominatorFractionEquivalence` states
`RingHom.exists_fractionRing_equiv_of_unit_denominators`, with `sorry` as the entire
proof. It adds no definitions or auxiliary theorems. The node is unchanged apart
from its `lean` field.

Hypothesis and clause correspondence:

- A commutative integral domain A: `{A : Type u} [CommRing A] [IsDomain A]`.
  The `IsDomain` mixin includes nontriviality and cancellation by nonzero factors,
  hence the node's nonzero commutative ring without zero divisors.
- A commutative ring B: `{B : Type v} [CommRing B]`. The independent explicit
  universes `u v` impose no size equality.
- An injective unital ring map: `(i : A →+* B) (hi : Function.Injective i)`.
- Every element has a unit denominator: `hden : ∀ x : B, ∃ a s : A,
  IsUnit (i s) ∧ i s * x = i a`. Mathlib's `IsUnit` is existence of a bundled
  two-sided multiplicative inverse, exactly the inline notion in the node.
- B is a domain: the first existential witness `(_ : IsDomain B)` is a conclusion,
  not an input assumption. Its binder supplies the instance needed by the following
  fraction-field expressions.
- The fraction fields and ring isomorphism: the second witness is
  `J : FractionRing A ≃+* FractionRing B`. `FractionRing D` is Mathlib's concrete
  localization at `nonZeroDivisors D`; for a domain these are precisely the nonzero
  elements and its standard instance `FractionRing.field` is a `Field`.
  This implements the node's pairs modulo cross multiplication, without a second
  fraction-field construction.
- J(a/s) = i(a)/i(s) for all a and nonzero s: the first conjunct quantifies over
  `a s : A` and assumes `s ≠ 0`; each numerator/denominator is mapped into its
  respective fraction ring by `algebraMap`.
- J extends i: the second conjunct is
  `∀ a : A, J (algebraMap A (FractionRing A) a) =
  algebraMap B (FractionRing B) (i a)`.
- The last clause quantifies over `x y : B` and `a s b t : A`, then assumes exactly
  `y ≠ 0`, `IsUnit (i s)`, `IsUnit (i t)`, `i s * x = i a`, and
  `i t * y = i b`. Its conclusion is `s * b ≠ 0` and the asserted equality
  `J((t*a)/(s*b)) = x/y`, using the canonical algebra maps on every element.
  Both formulas and the extension clause concern the same existential J.

Dependency declarations: `def-weil-field` is a Mathlib leaf with
`mathlib_match: ["Field"]`. Its declaration and full docstring were read in
`Mathlib.Algebra.Field.Defs` (class at line 180). The sole public import is
`Mathlib.RingTheory.Localization.FractionRing`, which transitively exposes that
class and supplies `FractionRing`, its algebra maps, and `FractionRing.field`.
Also inspected `IsFractionRing`, `IsFractionRing.toField`, `IsDomain`, and
`IsUnit` with `isUnit_iff_exists` to check the definitions against the node.
There are no recorded project dependency modules to import.

Sources read: ILO PDF page 110 (printed page 104), VIII Lemma 3.2.9 proof
(common dense group-algebra open) and Lemma 3.2.12 first proof paragraph
(integrality of the monoid algebra), and `literature/stacks-project/fields.tex`,
`example-quotient-field` (Tag 09FJ), lines 103–124. The module docstring gives
all six elementary steps of the node's explicit algebra argument: nontriviality,
absence of zero divisors, construction and well-definedness of J, injectivity,
the double-denominator preimage calculation and surjectivity, and assembly of
the ring isomorphism. It names the ILO source and Tags 09FJ and 00CO.

Edge cases checked: a zero ring B admits no injective unital map from a domain,
so it is excluded by the hypotheses rather than by an extra instance. The field
case A = B with i the identity satisfies the denominator condition using s = 1.
The identity case for any domain likewise gives the usual identity fraction map.
The numerators a or x may be zero. In the last clause b cannot be zero since
`i(t)` is a unit and y is nonzero; s cannot be zero since B is nonzero and i(s)
is a unit. Thus s*b is nonzero with no added assumption on b or s. Only the
node's nonzero denominators and nonzero y are restricted; no characteristic,
finiteness, or universe restriction is introduced.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: "An injective ring map from a domain such that every target element
  has a denominator mapping to a unit makes the target a domain and induces a
  fraction field ring equivalence". Eight hits, including `IsFractionRing.map`,
  `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`, and
  `IsFractionRing.ringEquivOfRingEquiv`. None states the combined conclusion with
  these hypotheses and the explicit last formula.
- Loogle: `IsFractionRing, RingEquiv`. Twelve hits, principally
  `IsFractionRing.ringEquivOfRingEquiv` and its compatibility lemmas. They start
  with a ring equivalence of the base rings, which is not the hypothesis here.
- Mathlib grep: `unit.*[Dd]enom|[Dd]enom.*unit|isDomain.*[Ll]ocalization|isFractionRing_of_isDomain`
  in `RingTheory/Localization`. Twelve hits, including domain-localization and
  the iterated-localization fraction theorem. Read the latter's full signature
  at `LocalizationLocalization.lean:278`: it assumes `IsLocalization`, so does
  not state the present elementary transfer from an arbitrary injective map.
- LeanSearch: "An injective ring homomorphism with unit denominators induces an
  equivalence of fraction fields and the target is a domain". Eight hits,
  including `IsFractionRing.map` (requires a domain target, returns only a map),
  `IsFractionRing.lift`, and `AlgEquiv.ofInjectiveField`; no exact match.
- Project `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `unitDenominator|unit_denominator|fraction.*[Ee]quiv|[Ee]quiv.*[Ff]raction`,
  followed by `unit.denominator|unitDenominator|unit_denominator` and an exact
  declaration-name search including Mathlib and `dag/lean_names_upstream.json`.
  Existing matches concern other localization/fraction equivalences; none
  states this transfer. The exact declaration name is unused.
- Required `grep -rn 'lem-trf-unit-denominator-fraction-equivalence'
  lean/WeilConjectures` returned no match.

No statement correction, new node, dependency repair, or statement dispute is
needed. The source clone and compiled library were only read. All writes are
in the assigned sandbox and all compilation uses the prescribed server wrapper.

Validation: `scompile.py Q02 lem-trf-unit-denominator-fraction-equivalence
<module>` compiled the sandbox and library-name copies successfully (2.1 s and
4.8 s), with no errors or warnings printed.

## Second reading by Q02

Reread the node and the finished file in this worker, clause by clause, after the
successful compile. The dispatcher prohibits starting another agent; independent
review is the maintainer's delivery review. This section records the worker's
second pass, not a claim of independent agent review.

Checked that the existential domain witness is a conclusion and is in scope for
all following divisions; no IsDomain B hypothesis was smuggled into the binders.
Checked the first fraction formula has numerator a and denominator s, and the
last has numerator t*a and denominator s*b, with the equations in exactly the
node's orientation. Checked all five last-clause hypotheses and both conclusions,
and that the extension equality lands in Frac(B). The one public import supplies
the recorded Field dependency and concrete fractions. Universes and variables
are explicitly bound; there are no local notations, private constructions, lets,
or hidden proof-bearing terms. No mismatch was found and no revision was needed.
