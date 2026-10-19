## Worker report

Item: `lem-per-valuation-topology-common-coarsening`, group Q51, stage 2.

The new module `Sheaf.FieldTheory.ValuationTopologyCommonCoarsening` states
`AddValuation.topology_eq_iff_exists_common_proper_coarsening`, with its sole proof `sorry`.
It defines no new notions. The item node changes only in `lean`.

Hypothesis and clause correspondence:

- A field K: `(K : Type u) [Field K]`. The two ordered abelian value groups use independent
  universes `v` and `w`, with `[AddCommGroup Γᵢ] [LinearOrder Γᵢ] [IsOrderedAddMonoid Γᵢ]`.
  These unbundled classes express a linearly ordered abelian group; no rank condition occurs.
- The additive valuations K → Γᵢ ∪ {∞}: `vᵢ : AddValuation K (WithTop Γᵢ)`.
  Mathlib's existing `AddValuation` includes the zero, unit, product and ultrametric axioms.
  Its infinity is `⊤`; `vᵢ 0 = ⊤`, `vᵢ (x*y) = vᵢ x + vᵢ y`, and
  `min (vᵢ x) (vᵢ y) ≤ vᵢ (x+y)` are its defining properties.
- Nontriviality: `[v₁.toValuation.IsNontrivial] [v₂.toValuation.IsNontrivial]`.
  The existing class says a value differs from multiplicative zero and one. Under the
  canonical additive/multiplicative equivalence, this is a finite additive value different
  from zero, exactly nontriviality of the given additive valuation.
- Surjective value groups Γᵢ = vᵢ(Kˣ): `hᵢ : ∀ γ : Γᵢ, ∃ x : Kˣ,
  vᵢ (x : K) = (γ : WithTop Γᵢ)`. The domain is explicitly Kˣ, so all finite values and only
  finite values arise from nonzero elements (finiteness on Kˣ follows from multiplicativity).
- Vᵢ = {x : vᵢ(x) ≥ 0}: `vᵢ.toValuation.valuationSubring`.
  `AddValuation.toValuation` is Mathlib's identity equivalence to the multiplicative valuation
  on the order dual. Thus `vᵢ.toValuation x ≤ 1` is precisely `0 ≤ vᵢ x`.
- The topology with translated strict balls of all finite thresholds:
  `vᵢ.toValuation.subgroups_basis.topology`. Its zero-neighbourhood basis is the strict
  subgroups `Valuation.ltAddSubgroup` at units of the actual value group. Under order duality,
  these are `{x | (γ : WithTop Γᵢ) < vᵢ x}`. The hᵢ hypotheses identify the actual finite
  value group with all Γᵢ, and translation gives the balls centred at any `a : K`.
  The topology is the existing Mathlib construction, not a newly introduced predicate or
  an arbitrary assumed topology.
- Equality of those two topologies: the left side of `↔` is literal equality of the two
  `TopologicalSpace K` terms. Both directions are retained.
- Existence of a valuation ring U ⊊ K containing V₁ ∪ V₂:
  `∃ U : ValuationSubring K, U ≠ ⊤ ∧ v₁.toValuation.valuationSubring ≤ U ∧
  v₂.toValuation.valuationSubring ≤ U`. The order is inclusion of the actual subrings of K;
  the two inclusions are exactly containment of the union. Since every subring is contained
  in K, `U ≠ ⊤` is proper containment. The bundled type supplies the valuation-ring property
  and fraction field K, so no extra property is hidden or assumed.
- “Common nontrivial coarsening” is the name for that very existential condition; it is not
  an additional conclusion. The statement does not equate V₁ and V₂. No henselianity,
  rank-one or completeness hypothesis occurs. Universes u, v, w are explicit and independent.

Dependency interface read and used:

`def-trf-valuation-ring` is a Mathlib leaf with match `ValuationRing; ValuationRing.TFAE`
in `Mathlib.RingTheory.Valuation.ValuationRing`. I read the class at lines 62–64 and the
full TFAE signature at lines 407–416. `ValuationRing.TFAE` equates the domain valuation-ring
class to the fraction-field condition that x or its inverse is integral. For a subring of
K the exact bundled specialization is Mathlib's `ValuationSubring K`, from
`Mathlib.RingTheory.Valuation.ValuationSubring`, publicly imported through
`Mathlib.Topology.Algebra.Valued.ValuationTopology`. I read its full structure and its
`ValuationRing` and `IsFractionRing` instances. It has precisely the node's fraction-field
characterization. Consequently no dependency repair or private valuation-ring definition
is needed. I also read `Valuation.valuationSubring`, `AddValuation.toValuation`,
`Valuation.IsNontrivial`, `Valuation.subgroups_basis`, and the associated neighbourhood-basis
and translated-neighbourhood statements.

Source reading: I opened ILO Exposé XX section 4.4 on printed page 374 (PDF page 380),
which discusses valuation topologies and dense embeddings of henselian valued fields and
refers to Bourbaki VI §8. It does not state this criterion; the node honestly records an
agent-selected elementary refinement. The module preserves that provenance. I also read
Stacks `algebra.tex`, `definition-valuation-ring` and
`lemma-valuation-ring-x-or-x-inverse`, including the converse immediately after it.
The docstring includes all six proof steps from the node, including the bounded mixed-sum
subring construction and the explicit cofinal ball inclusions in the converse.

Edge cases checked before writing:

- Equal nontrivial valuations: their own proper integer ring is a witness U; both topologies
  are literally equal.
- Comparable but unequal valuation rings: a nontrivial coarser one is a proper common
  overring, so the theorem gives equal topologies without equating rings. For example the
  t-adic coarsening of the lexicographic (t,u)-valuation on k((u))((t)) is allowed.
- Independent valuations, such as p-adic and q-adic valuations on Q for distinct primes:
  the generated subring is Q, so no proper common overring exists and the topologies differ.
- The trivial valuation is excluded by the stated nontriviality hypotheses, exactly as in
  the node. The zero field cannot satisfy `[Field K]`; finite fields have no nontrivial
  valuation, so give no unintended case.
- Zero lies in both integer rings and all finite-threshold balls. The top value is not
  a threshold: thresholds range over Γᵢ and the topology basis uses nonzero values.
- Arbitrary-rank, nondiscrete groups and value-group universes different from the field's
  are allowed. There is no Archimedean, discreteness, or cofinality hypothesis added.

Searches for existing declarations (2026-10-19):

- `msearch.py ... leanfinder "Two nontrivial valuations on a field induce the same topology
  if and only if their valuation rings have a proper common valuation overring"`: 8 hits,
  including `Valuation.isEquiv_iff_valuationSubring`, `Valuation.isEquiv_tfae`,
  `Valuation.isEquiv_valuation_valuationSubring`, and local-field results. I read the
  equivalence definitions/signatures: they compare integer rings/preorders, which is
  stronger than equality of arbitrary-rank valuation topologies. No exact match.
- `msearch.py ... loogle "ValuationSubring, TopologicalSpace"`: 3 hits, the clopen, closed,
  and open valuation-subring statements in the valuative topology. None compares two
  topologies or asserts the proper-common-overring criterion.
- `msearch.py ... leansearch "Two valuation topologies agree exactly when a proper
  valuation subring contains both valuation rings"`: 8 hits including
  `Valuation.isEquiv_iff_valuationSubring`, `Valuation.isEquiv_iff_val_eq_one`,
  `Valuation.isEquiv_of_val_le_one`, `AddValuation.IsEquiv`, and subring extensionality.
  None states the topology criterion.
- `msearch.py ... grep "coarsen|same.*topolog|topolog.*equiv"
  Topology/Algebra/Valued`: 0 hits.
- Direct `rg` over Mathlib, upstream WeilConjectures and project `lean/Sheaf` for
  `common.*coarsen|coarsen.*topolog|same.*valuation.*topolog|topolog.*common.*overring`
  and the proposed declaration name found only the downstream docstring references in
  `Sheaf.FieldTheory.HenselianFiniteExtensionTopology`, not a declaration of this item.
- `grep -rn "lem-per-valuation-topology-common-coarsening"` in upstream WeilConjectures:
  no matches. `rg` of the proposed declaration name in `dag/lean_names_upstream.json`:
  no matches. The additive valuation, associated subring and topology APIs themselves
  were located in and read from the Mathlib sources, and are reused.

No statement dispute, statement correction, new nodes, or dependency modules.

Validation: the prescribed `scompile.py Q51 lem-per-valuation-topology-common-coarsening`
compiled the delivered file cleanly in both sandbox and library checks (2.5 s and 2.9 s),
with no errors or warnings. `set_option autoImplicit false` enforces explicit binders.
The signature in `lean.statement` is extracted verbatim from the file. The remaining
required validation is the delivery wrapper's server preflight and repeated per-file check.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
