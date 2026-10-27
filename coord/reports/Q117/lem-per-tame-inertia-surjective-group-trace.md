## Worker report

The module `Sheaf.RingTheory.TameInertiaSurjectiveGroupTrace` states
`MulSemiringAction.groupTrace_surjective_of_isUnit_inertia`, with `sorry` as its entire
proof. It supplies no definitions and proves no theorem. Only the item's `lean` field changes.
The earlier `lean` record named this same module, but its note records withdrawal on
2026-10-20. The module is absent locally and `scompile.py --source` confirms that it is
unavailable on the live server. This delivery restores its statement with its current
seven-step proof docstring. No repair note or group return for the item was found.

Clause-by-clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`. The universe is explicit and there
  is no `Nontrivial R` assumption.
- A finite group G: `(G : Type v) [Group G] [Fintype G]`. This presents any finite group
  with a finite enumeration for the displayed sum; u and v are independent.
- Action by ring automorphisms: `[MulSemiringAction G R]`; the action preserves sums,
  products, zero and one, and the inverse group element gives the inverse automorphism.
  No faithful-action assumption is added.
- A = R^G: `FixedPoints.subring R G`, the existing Mathlib subring of elements fixed by
  every element of G.
- Every prime p and its residue field: `∀ (p : Ideal R) [p.IsPrime]` and `p.ResidueField`.
  These include nonmaximal primes; `Ideal.ResidueField` is literally the residue field
  of `Localization.AtPrime p` from the recorded statement dependency.
- Inertia: `p.inertia G`, the existing subgroup of g with `g • r - r ∈ p` for every r.
  Such g preserve p (use the same condition for g inverse), and induce the identity on
  R/p, hence on its fraction field κ(p). Conversely identity on κ(p) forces the
  difference into p since R/p embeds in κ(p). Thus this is the stated residue inertia,
  without an extra choice of action or any restriction to maximal primes.
- Tameness: `IsUnit (Nat.card (p.inertia G) : p.ResidueField)`, exactly invertibility
  of each inertia order in that residue field. The order of the entire group need
  not be invertible in R or in the residue fields.
- Trace formula: `∑ g : G, g • a`. Its invariance, additivity, and A-linearity follow
  directly from the action and reindexing by left multiplication, as in node step 1.
  No arbitrary replacement map is supplied. Expressing its surjectivity by preimages
  avoids duplicating a bundled linear-map definition.
- Surjectivity to A: `∀ b : FixedPoints.subring R G, ∃ a : R, ... = (b : R)`.
- Equivalent trace-one condition: the second conjunct is `∃ a : R, ... = 1`.
  Both conclusions are stated, as in the prior reviewed signature. Under trace
  linearity each follows from the other; the docstring records both directions.
- No Noetherian or finite-type hypothesis: neither occurs in the binders.

Dependency declarations inspected and used:

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. Read their full definitions and
  docstrings. The latter is publicly imported to expose the actual residue-field
  notation required by the statement. `Ideal.Fiber` and its quotient equivalence in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` were also inspected; the present
  statement uses only the localization/residue clauses of that dependency.
- `FixedPoints.subring`, `Mathlib.Algebra.Algebra.Subalgebra.Operations`, and
  `Ideal.inertia`, `Mathlib.RingTheory.Ideal.Defs` (via its public import chain).
  The underlying `AddSubgroup.inertia` definition was read too.
- Plain proof imports follow every stated proof dependency: `RingHom.IsIntegral.comap_surjective`
  from `Mathlib.RingTheory.Spectrum.Prime.Topology` (injective integral lying over);
  `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'` from
  `Mathlib.RingTheory.Ideal.GoingUp` (prime over maximal is maximal);
  `linearIndependent_monoidHom` from `Mathlib.LinearAlgebra.LinearIndependent.Basic`;
  `Ideal.quotientInfRingEquivPiQuotient` from
  `Mathlib.RingTheory.Ideal.Quotient.Operations`; and `Ideal.exists_le_maximal` from
  `Mathlib.RingTheory.Ideal.Maximal`. Their full recorded signatures and nearby
  docstrings were read. Mathlib leaves without `lean` records use their `mathlib_match`.

Sources read: Stacks `more-algebra.tex`, `lemma-base-change-invariants` (0BRH),
`lemma-one-orbit` (0BRI), and `lemma-one-orbit-geometric` (0BRJ), including the
orbit-polynomial integrality and finite-orbit CRT passages. As the node explicitly
says, the trace theorem is an agent-supplied consequence, not a quotation of any
one of these tags. The declaration docstring carries all seven accepted DAG proof
steps, including character independence and the actual trace calculation.

Edge cases checked mathematically before writing:

- Zero ring: there are no prime ideals; choose a = 0, whose trace is 0 = 1.
- Trivial group: the trace is the identity and every inertia order is 1.
- Nonfaithful trivial action: inertia is all of G; tameness forces its order to be
  invertible in every residue field, which is the right condition for multiplication
  by |G| to be surjective. The statement does not accidentally assume faithfulness.
- F₂ × F₂ with the transposition action: inertia at both primes is trivial although
  |G| = 0 in the residue fields; (1,0) has trace (1,1). This checks that no stronger
  whole-group-order condition has slipped in.
- F₄ with Frobenius: the sole inertia group is trivial, and the field trace is
  surjective despite characteristic 2 and group order 2.
- Nonmaximal primes are retained in the quantified hypothesis; no dimension,
  finite-generation, or Noetherian instance appears.

Searches actually run via `msearch.py` with group Q117 and this item:

- LeanFinder: `A finite group acts on a commutative ring with inertia orders invertible
  in each residue field then the group trace to the invariant ring is surjective`.
  Eight hits: stabilizer homomorphism surjectivity, finite-field/fixed-field results,
  `Algebra.trace_surjective`, and normalized trace. None states this arbitrary-ring
  trace theorem.
- Loogle: `"trace", "inertia"`: zero hits.
- Grep: `inertia|trace.*surject|surject.*trace`, subdirectory `RingTheory`: 25 hits,
  including `Ideal.inertia_le_stabilizer`, field-trace surjectivity, ramification
  indices and unrelated norms; no exact match.
- LeanSearch: `Finite group ring action invertible inertia orders at every prime imply
  group trace surjective onto invariants`: eight hits on invariant-ring integrality,
  the inertia membership criterion, representation invariants, and unrelated group
  actions; no exact theorem.
- Local `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id, full declaration name, groupTrace, and trace/surjectivity patterns:
  no extant declaration with this statement. Fixed-ring and inertia uses elsewhere
  confirm the existing notions, which are reused here.

Validation: `scompile.py Q117 lem-per-tame-inertia-surjective-group-trace` compiled
this module both as sandbox and at its library module path (20.9 s and 11.4 s), with
no errors or warnings reported. `autoImplicit` is explicitly false and both universes
and every variable are bound. No new node, dependency repair, statement correction,
or STATEMENT-DISPUTED issue is needed.

## Second reading by Q117

I reopened the final node and final module for a separate clause-by-clause pass.
The commutative-ring and finite-group binders, ring action, fixed subring, all-prime
quantification, residue-field unit condition, invariant-preimage conclusion, and
trace-one conclusion agree as listed above. Inertia uses the difference criterion
for the same residue action, not merely the prime stabilizer. The independent u/v
universes and absence of `Nontrivial`, `FaithfulSMul`, `IsNoetherianRing`, and
finite-type assumptions preserve the edge cases. Both outputs are explicit.
The seven proof steps in the docstring now follow the accepted node rather than
an older localization/field-trace shortcut. No mismatch remained after this pass.
This is the assigned worker's second pass; the dispatcher forbids spawning another
agent, and the maintainer's independent delivery review remains the independent reading.
