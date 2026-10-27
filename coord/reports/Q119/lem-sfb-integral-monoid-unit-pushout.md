## Worker report

The module `Sheaf.GroupTheory.IntegralMonoidUnitPushout` states
`Algebra.integralMonoidUnitPushout`. Its only theorem proof is `sorry`.
The node's statement, statement dependencies, proof, and proof dependencies are unchanged.
The helper definitions construct exactly the objects introduced in the node and are
listed in `lean.declarations`; none has postponed data or a postponed proof.

The source was read in the local ILO PDF, PDF page 104 / printed page 98,
Exposé VIII 3.1.1–3.1.2. It supplies the localization convention, as the node
accurately says; the full mixed pushout lemma is the node's agent-formulated
refinement, not a theorem claimed from that source. The module docstring preserves
that distinction. The theorem docstring carries all seven elementary proof steps.

Hypotheses and constructions, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Commutative monoid P | `(P : Type u) [CommMonoid P]` |
| Abelian group presentation of P's completion | `monoidCompletionRelations P : Module.Relations ℤ`, with generator type P, relation type `Option (P × P)`, relation at `none` equal to `Finsupp.single 1 1`, and relation at `some (p,q)` equal to `Finsupp.single (p*q) 1 - Finsupp.single p 1 - Finsupp.single q 1` |
| Completion written multiplicatively | `Multiplicative (monoidCompletionRelations P).Quotient` |
| Canonical map p ↦ [p] | `monoidCompletionGenerator P`, the multiplicative type tag of `Module.Relations.toQuotient` applied to `Finsupp.single p 1` |
| P integral | `hP : Function.Injective (monoidCompletionGenerator P)` |
| Submonoid E ⊆ P | `(E : Submonoid P)`; `e.1` is its actual inclusion |
| Any abelian group G | `(G : Type v) [CommGroup G]`, with v independent of u |
| Arbitrary monoid homomorphism E → G | `(f : E →* G)`; there is no injectivity hypothesis |
| Generated monoid congruence (pe,g) ∼ (p,f(e)g) | `unitAmalgamationCon E f := conGen (fun x y => ∃ p e g, x = (p * e.1,g) ∧ y = (p,f e * g))` |
| M = (P × G) modulo this congruence | `UnitAmalgamation E f := (unitAmalgamationCon E f).Quotient`, with Mathlib's commutative monoid structure |
| Representative [p,g] | `(unitAmalgamationCon E f).mk' (p,g)` |
| Canonical homomorphism G → M | `unitAmalgamationGroupMap E f : G →* UnitAmalgamation E f`, the quotient homomorphism composed with `g ↦ (1,g)` |

The completion map is used through its underlying function because injectivity is
a property of that function. It is precisely the generator map into the specified
presentation; no arbitrary comparison group replaces the node's group completion.

Conclusions, clause by clause:

| Node | Lean rendering |
| --- | --- |
| M → M^gp injective | `Function.Injective (monoidCompletionGenerator (UnitAmalgamation E f))` |
| M cancellative | `IsCancelMul (UnitAmalgamation E f)`, with the existing commutative monoid structure |
| G → M injective | `Function.Injective (unitAmalgamationGroupMap E f)` |
| Action h · [p,g] = [p,hg] | Multiplication by `unitAmalgamationGroupMap E f h`; on representatives it is the class of `(1,h) * (p,g) = (p,h*g)` |
| Action free, h · m = m implies h = 1 | `∀ (h : G) (m : UnitAmalgamation E f), unitAmalgamationGroupMap E f h * m = m → h = 1` |
| Equality criterion for all p,p',g,g' | `∀ (p p' : P) (g g' : G), ... ↔ ∃ e e' : E, p * e'.1 = p' * e.1 ∧ g * f e = g' * f e'` |

Dependency declarations used:

- `def-trf-abelian-group-presentation` is a Mathlib leaf, whose recorded match is
  `Module.Relations.Quotient` in `Mathlib.Algebra.Module.Presentation.Basic`.
  Read the full `Module.Relations` structure, `Quotient`, and `toQuotient`
  signatures and docstrings at lines 55–75. This exact API constructs both group
  completions here; its general generators-and-relations notion is not redefined.
- `conGen` and `Con.Quotient` provide generated monoid congruences and their
  quotients; `Con.mk'` in `Mathlib.GroupTheory.Congruence.Hom` provides the
  quotient homomorphism. `Mathlib.Algebra.Group.Prod` supplies product monoids.
- The one proof dependency is also `def-trf-abelian-group-presentation`, whose
  module is already publicly imported as a statement dependency.

Edge cases checked mathematically before writing:

- E = {1}: the quotient is P × G, so the criterion reduces to p = p' and g = g'.
- E = P and G trivial: the quotient is trivial; the criterion has witnesses
  e = p and e' = p'. This tests an entirely noninjective f.
- P = E = the free commutative monoid on one generator, G cyclic of order 2,
  and f sending the generator to the nontrivial element: the quotient is G;
  the kernel of f causes no failure of G-injectivity or freeness.
- P trivial: E is trivial, M = G, and freeness is left regular freeness.
- P a group: M is the corresponding abelian-group pushout and G embeds
  because E^gp → P is injective.
- Without the integrality hypothesis the claim can fail: a nontrivial
  idempotent monoid is its own pushout when E = {1} and G is trivial,
  and is not cancellative. Thus hP is a substantive hypothesis.
- P and G may have unrelated universes. Empty P or E cannot occur for monoids;
  trivial monoids and trivial groups remain included.

Searches made (all Mathlib service searches used the prescribed `msearch.py`):

- LeanFinder: `Pushout of an integral commutative monoid with an abelian group
  along a submonoid is integral with free group action and explicit equality
  criterion`. Eight hits: ring-integrality pushouts and `Monoid.PushoutI`
  normal-word/group constructions, with no exact statement.
- Loogle: `Monoid.PushoutI, Algebra.GrothendieckGroup`: zero hits.
- LeanSearch: `commutative monoid pushout along a submonoid to an abelian group
  is cancellative and the group action is free`: eight hits, including
  `CancelMonoid`, `CancelCommMonoid`, `Monoid.PushoutI.monoid` and
  `Monoid.PushoutI.instGroup`; no mixed commutative pushout result.
- Mathlib grep: `Pushout|GrothendieckGroup|conGen`, subdirectory `GroupTheory`:
  25 hits. Read the Grothendieck-group construction and lift/injectivity
  signatures; its injectivity lemma already assumes cancellation, so it does
  not prove this result. The existing completion is a localization, whereas
  this node explicitly requests the recorded integer-module presentation.
  This delivery specializes that presentation API rather than redefining its
  general quotient machinery.
- Project grep: `unitPushout|UnitPushout|unit_pushout|integral-monoid-unit-pushout`
  in `lean/WeilConjectures` and `lean/Sheaf` found only references in
  log-structure proof docstrings, no statement of this theorem.
- Read `divisorialChartCongruence` and `divisorialChartPushout` in
  `Sheaf.AlgebraicGeometry.LogRegularPair`. They require a ring A and a
  structural map β, and use the inverse image of A's units, so do not supply
  this node's arbitrary submonoid E and homomorphism to an arbitrary group G.
- Searched the DAG for group-completion and monoid-pushout titles: it has the
  dropped `lem-per-integral-monoid-unit-pushout` twin, without a Lean binding.
  It is not used or reintroduced as a dependency.
- Checked all six proposed declaration names in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py Q119 lem-sfb-integral-monoid-unit-pushout` compiled the
delivered file in sandbox mode (29.5 s) and its actual library module mode (39.1 s),
with no errors or warnings. `autoImplicit` is explicitly false, and every
universe and variable is bound. All lines are at most 100 characters.

No statement dispute, correction, dependency repair, or new independent node
was needed. The helpers are the objects already explicitly defined by this node,
as authorized in the brief's same-notion helper rule.

## Second reading by Q119

This is the dispatcher's single-worker assignment, with an explicit instruction
not to start other agents. The following is a self-review; the maintainer's
independent delivery review remains independent.

Re-read the node alongside the complete Lean file. The presentation uses exactly
the two requested families of additive relations, and `Multiplicative` changes
notation, not the quotient. The integrality hypotheses/conclusions concern its
actual canonical generator function. The congruence uses the generating relations,
not a relation whose transitivity or equality criterion is silently assumed.
The group inclusion is a constructed homomorphism with values [1,g]. Its
multiplication action sends [p,g] to [p,hg]; quantifying over arbitrary quotient
elements in the freeness clause includes every m. The equality criterion has
the exact cross multiplication `p * e' = p' * e` and exact group equation
`g * f(e) = g' * f(e')`, with both directions. No injectivity of f, finite
generation, saturation, or equality of u and v is imposed. The sole theorem has
`sorry`, and no helper introduces a postponed theorem. No mismatch was found.
