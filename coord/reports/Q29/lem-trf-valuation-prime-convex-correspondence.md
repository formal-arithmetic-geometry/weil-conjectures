## Worker report

The module `Sheaf.TraceFormula.ValuationPrimeConvexCorrespondence` states
`ValuationSubring.primeSpectrum_orderDualEquiv_convexSubgroup`, with its entire proof
`sorry`. It introduces no new definitions. The node changes only in `lean`.

Hypothesis and clause correspondence:

- The field `K` is `{K : Type u} [Field K]`, using `def-weil-field`'s recorded
  Mathlib declaration `Field` (`Mathlib.Algebra.Field.Defs`). No characteristic or
  size restriction is imposed.
- The valuation subring is `(A : ValuationSubring K)`. Mathlib's full structure is
  a `Subring K` with `mem_or_inv_mem' : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A`.
  Requiring this at zero is equivalent to the node's nonzero alternative because
  every subring contains zero. The fraction-field property is automatic; there
  is no additional hypothesis on it.
- The node's group `Γ = Kˣ/Aˣ` is exactly `Kˣ ⧸ A.unitGroup`. The recorded
  Mathlib definition `ValuationSubring.unitGroup` is the kernel of valuation on
  `Kˣ`, and `unitGroupMulEquiv : A.unitGroup ≃* Aˣ` verifies that these are
  precisely the embedded units of `A`.
- The given total order is expressed as an existential `ord : LinearOrder
  (Kˣ ⧸ A.unitGroup)`, together with its representative characterization
  `ord.le (QuotientGroup.mk' A.unitGroup x)
  (QuotientGroup.mk' A.unitGroup y) ↔ (y : K) / (x : K) ∈ A`.
  The next conjunct gives multiplication invariance, rendering the ordered
  abelian group described in proof Step 1. The quotient group already has its
  commutative group operations. This is a conclusion constructing the specified
  order, not an assumption of an arbitrary order. No local notation, local
  instance, helper order, or private version of the value group is introduced.
- Convex subgroups are the subtype of `Subgroup (Kˣ ⧸ A.unitGroup)` whose
  predicate is exactly `h₁ ∈ H → h₂ ∈ H → ord.le h₁ g → ord.le g h₂ → g ∈ H`.
  The order on this subtype is the inherited subgroup inclusion order.
- Prime ideals are `PrimeSpectrum A`, whose order is ideal inclusion.
  `e : (PrimeSpectrum A)ᵒᵈ ≃o {H // ...}` is the requested order
  anti-isomorphism. Its inverse and both inclusion implications are part of
  `OrderIso`, without replacing a correspondence by just two implications.
- Canonicity is specified by the nonnegative representative formula: for
  `x : Kˣ` with `hx : (x : K) ∈ A`, its quotient class belongs to
  `e (OrderDual.toDual P)` if and only if `(⟨(x : K), hx⟩ : A) ∉ P.asIdeal`.
  This is the composite of the node's prime value-set correspondence and its
  nonnegative-complement formula. It determines the subgroup on every class:
  either the class or its inverse is nonnegative, and a subgroup contains one
  exactly when it contains the other. Thus the existential equivalence is the
  specified canonical one, rather than an unspecified bijection.
- The final conjunct takes every `n : ℕ` and every strictly increasing chain
  `p : Fin (n + 1) → PrimeSpectrum A` to the strictly decreasing chain
  `fun i ↦ e (OrderDual.toDual (p i))`. `StrictAnti` states all the strict
  reversed inclusions; the index set has `n + 1` terms, hence `n` inclusions.
  Reversing its finite indexing gives the increasing convex-subgroup chain
  used by the downstream height/rank argument.

Dependency and source reading:

The sole statement dependency is the Mathlib node `def-weil-field`; its complete
`Field` declaration and docstring were read. The module publicly imports
`Mathlib.RingTheory.Valuation.ValuationSubring` and
`Mathlib.GroupTheory.QuotientGroup.Basic`, using the existing `ValuationSubring`,
`unitGroup`, `PrimeSpectrum`, `Subgroup`, `QuotientGroup.mk'`, and quotient group
instances. It also imports, for the future proof only,
`Sheaf.GroupTheory.OrderedGroupPrimeIdealConvex`, whose declaration
`AddSubgroup.orderedGroup_primePositiveConeIdeal_orderDualEquiv_convexAddSubgroup`
and full docstring were read. This is the already-stated proof dependency; it
uses additive notation and will be applied to `Additive (Kˣ ⧸ A.unitGroup)`.
The other proof dependency `lem-trf-valuation-ring-ideal-correspondence` has no
Lean record in the read-only DAG snapshot, so there is no recorded module to
import. It is used only in the natural-language proof plan, not to define any
object of this statement.

Read Stacks `algebra.tex`, `lemma-valuation-group`, `definition-value-group`
(Tag 00IE), and `lemma-ideals-valuation-ring` (Tag 00IH). Also opened the author's
v3 PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, §2.1,
p. 7, lines 375–416. Its prime/overring and overring/convex-subgroup
correspondences give the claimed canonical correspondence. Temkin's
multiplicative order is dual to the node's additive valuation convention;
convexity is unchanged by dualizing the group order. The Lean uses exactly the
node's `y/x ∈ A` convention. No statement correction or dispute is needed.

Edge cases checked before finalizing:

- For `A = K`, the quotient is trivial; `A` has just its zero prime and the
  quotient has just its trivial convex subgroup. The membership formula is
  valid because nonzero field elements are outside the zero ideal.
- The zero prime corresponds to the whole quotient group; the maximal ideal
  corresponds to its trivial subgroup. This confirms inclusion reversal and
  the orientation of the formula.
- For a discrete valuation ring with value group `ℤ`, the two prime ideals
  correspond in reverse order to the two convex subgroups `ℤ` and `{0}`.
- For a higher-rank lexicographic ordered value group, the intermediate prime
  corresponds to the intermediate convex subgroup, not its complement.
- For `n = 0`, both finite chains have one term and no strict inclusion; the
  `StrictMono` and `StrictAnti` conditions are vacuous comparisons, so this
  case is included. There is no nontrivial-valuation assumption.
- The formula quantifies only over nonzero representatives `x : Kˣ`, as
  required for the quotient. Zero still belongs to every prime ideal and is
  handled by the prime ideal type, not dropped from the ring.

Searches for an existing statement or definition:

- `msearch.py`, LeanFinder: `prime ideals of a valuation ring correspond to
  convex subgroups of its quotient value group`. Eight hits, including
  `ValuationSubring.primeSpectrumOrderEquiv_apply_coe_carrier`; these concern
  overrings or valuation ideals, not the convex-subgroup correspondence.
- `msearch.py`, Loogle: `ValuationSubring, Subgroup, OrderIso`. Zero hits.
- `msearch.py`, LeanSearch: `prime ideals of valuation ring correspond to
  convex subgroups of value group`. Eight hits, including
  `ValuationSubring.primeSpectrumEquiv` and `prime_idealOfLE`, but no exact
  statement.
- `msearch.py`, grep of `Mathlib/RingTheory/Valuation`:
  `primeSpectrumOrderEquiv|convex.*[Ss]ubgroup|[Ss]ubgroup.*convex`. Two hits,
  both the existing prime/overring equivalence. Its definition and docstring
  were read; its target is overrings, so it does not state this node.
- Direct `rg` of the upstream `WeilConjectures/` tree and `lean/Sheaf` for
  valuation, convex subgroup, quotient value group, and the proposed full
  declaration name. No duplicate theorem. The search found the ordered-group
  proof dependency and the downstream height/rank statements, whose full
  signatures and docstrings were read. The literal item-id search in the
  upstream source returned no hits. The upstream declaration-name inventory
  also contains no proposed-name match.
- `scompile.py --source Mathlib.RingTheory.Valuation.ValuationSubring` read
  the live source and confirmed the existing `unitGroup` and `ValueGroup` APIs.
  Mathlib's `ValuationSubring.ValueGroup` is a group with zero in multiplicative
  valuation convention; the theorem uses the exact quotient carrier requested
  by this node, with no second value-group definition.

Validation: `scompile.py Q29 lem-trf-valuation-prime-convex-correspondence`
compiled the sole delivered file separately, its ordered-group proof import
in the private overlay, and the library module path, with no warnings or errors.
Every universe and variable is explicitly bound; every Lean line has at most
100 characters. No new nodes or dependency modules were needed.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
