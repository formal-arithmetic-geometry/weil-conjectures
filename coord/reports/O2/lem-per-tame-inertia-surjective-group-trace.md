## Worker report

The module `Sheaf.RingTheory.TameInertiaSurjectiveGroupTrace` states
`MulSemiringAction.groupTrace_surjective_of_isUnit_inertia`. Its only proof is
`sorry`. It introduces no definitions and changes only the item's `lean` field.
The inherited node status is `unsplit`; it is preserved as instructed.

Clause-by-clause rendering:

- A commutative ring R: `(R : Type u) [CommRing R]`. The zero ring is allowed.
- A finite group G acting by ring automorphisms: `(G : Type v) [Group G]
  [Fintype G] [MulSemiringAction G R]`. A semiring action of a group gives
  invertible ring maps, with inverses the actions of inverse group elements.
  Fintype merely chooses the enumeration required to write the finite sum;
  every finite group admits it. No faithfulness is required. Universes u and v
  are independent and explicitly declared.
- A = R^G: the target elements are `b : FixedPoints.subring R G`, Mathlib's
  actual fixed subring, whose underlying condition is that every group element
  fixes b. There is no arbitrary intermediate invariant ring.
- For every prime p, its residue field: `(p : Ideal R) [p.IsPrime]` and
  `p.ResidueField`. This is the recorded dependency's `Ideal.ResidueField`,
  defined as `IsLocalRing.ResidueField (Localization.AtPrime p)`.
- Residue inertia I_p: `p.inertia G`, Mathlib's subgroup of g such that
  `∀ x, g • x - x ∈ p`. These elements stabilize p (including the reverse
  inclusion by applying the same condition to the inverse). They induce the
  identity on R/p and therefore on its fraction field κ(p). Conversely,
  identity on κ(p) implies the congruences, because R/p embeds in κ(p).
  Thus this definition is exactly the subgroup in the node, including for
  nonmaximal primes and rings with nilpotents.
- Its order is invertible in κ(p): `htame : ∀ (p : Ideal R) [p.IsPrime],
  IsUnit (Nat.card (p.inertia G) : p.ResidueField)`. Nat.card counts the finite
  subgroup and does not require a separate chosen subgroup enumeration.
- T(r) = sum_g g(r): `∑ g : G, g • a`. The expression is the canonical group
  sum, with its value written in R. Reindexing by left multiplication proves
  that it is fixed; distributivity proves additivity, and for an invariant
  scalar b, `T(b*a)=b*T(a)`. This is exactly the node's A-linear trace.
- Surjectivity T:R→A: `(∀ b : FixedPoints.subring R G, ∃ a : R,
  ∑ g : G, g • a = (b : R))`. This is the pointwise, unbundled definition of
  surjectivity of that map, avoiding a duplicate definition and any separate
  well-definedness proof. Equality in R is equivalent to equality in the
  fixed subring because its inclusion is injective.
- Equivalently, trace one: the second conjunct is
  `(∃ a : R, ∑ g : G, g • a = 1)`. Taking b=1 gives it from surjectivity;
  multiplying a trace-one element by b gives the reverse implication.
  Both conclusions are recorded, with no strengthening of the proposition.
- No Noetherian or finite-type hypothesis: neither occurs among the binders;
  neither invertibility of |G| nor finite generation of R over A is assumed.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime` records
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`,
  and also `Ideal.ResidueField` and `Ideal.Fiber`. The statement needs only
  `Ideal.ResidueField`, so it imports its owning module
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, which publicly imports
  the localization module transitively. Its full definition and docstring,
  and those for Localization.AtPrime and Ideal.Fiber, were read. No dependency
  interface repair is needed and the fibre-ring clause is not used here.
- `Mathlib.Algebra.Algebra.Subalgebra.Operations`, `FixedPoints.subring`;
  `Mathlib.RingTheory.Ideal.Defs`, `Ideal.inertia`, and its underlying
  `AddSubgroup.inertia` in `Mathlib.Algebra.Group.Subgroup.Basic`. Their
  signatures and docstrings were opened. The module imports Ideal.Pointwise,
  which also provides `Ideal.inertia_le_stabilizer` used in interpreting it.
- The remaining import supplies the finite sum notation and API.

Source and proof: read Stacks `more-algebra.tex`, Tags 0BRH/0BRI/0BRJ, including
proofs, and the complete semilocal trace argument in
`coord/reports/Q94/lem-per-tame-admissible-scheme-quotient.md`, section
“Algebraic arguments for the new statements.” These tags are input, not a
claim that the trace criterion is a verbatim Stacks lemma. The theorem's
proof docstring reproduces that argument: orbit-polynomial integrality,
localization of invariants, finite transitive maximal orbit, faithful residue
quotient D/I, separable fixed-field trace, Chinese remainder lifting, trace
unit in every localization, and hence the unit trace ideal globally. It uses
the Galois extension L/L^D, not a possibly inseparable residue extension over
the invariant base prime.

Edge cases checked before writing:

- R is the zero ring: no prime ideals, tameness is vacuous, and its sole
  element has trace 1=0; the fixed subring is also a singleton.
- G is trivial: inertia order is 1 and the trace is the identity.
- A trivial action: every inertia is G; the hypothesis at every prime makes
  |G| a unit in R, and the trace is multiplication by this unit.
- The cyclic group of order p on a product of p copies of a characteristic-p
  field by permutation: every inertia is trivial, despite |G|=0 in the ring;
  the coordinate idempotent has trace one. This rules out replacing the
  actual tameness hypothesis with invertibility of the whole group order.
- Nonfaithful actions and nilpotents are permitted. Inertia is computed on
  κ(p), not on a strict local ring, and every prime is quantified.

Searches for existing statements (2026-10-19):

- `msearch.py ... leanfinder`: “For a finite group acting on a commutative
  ring, invertible inertia orders at every prime imply surjectivity of the
  group trace to invariants”. Eight hits; stabilizer-hom surjectivity,
  FixedPoints.toAlgAut_surjective and field trace surjectivity do not assert
  surjectivity of this sum on an arbitrary ring.
- `msearch.py ... loogle`: `"trace", "invariant"`. Three hits concerning Lie
  trace forms and modular forms; none matches.
- `msearch.py ... leansearch`: “A finite group acting on a commutative ring
  has surjective group trace if all residue inertia orders are invertible”.
  Eight hits on invariant integrality, stabilizer maps and ramification;
  none is this theorem.
- `msearch.py ... grep`: `inertia|trace.*surject|surject.*trace`, RingTheory.
  Twenty-five hits; these locate the actual inertia and field-trace APIs,
  with no theorem giving the stated ring-trace criterion.
- Direct rg in Mathlib's RingTheory/Invariant, Trace and Ideal sources, plus
  Algebra/Group/Action and Algebra/Algebra, found the inertia and fixed-subring
  definitions; algebra trace requires a different finite-module construction.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf` for the exact node id and `groupTrace|tame.*[Tt]race|[Tt]race.*tame`
  found no matching declaration. The exact proposed declaration and module
  name were absent from both source roots, Mathlib and
  `dag/lean_names_upstream.json`.

Validation: `scompile.py N2 lem-per-tame-inertia-surjective-group-trace` compiled
both the sandbox and library forms successfully (1.8 seconds each), with no
errors or unexpected warnings. There are no new nodes, dependency modules,
statement corrections, or mathematical disputes.

## Second reading by N2

A separate rereading in this worker session compared the node and completed
module; no other agents were started, as the dispatcher brief prohibits it.
The arbitrary commutative ring, finite group action, fixed subring, every
prime, actual residue inertia order and its invertibility all match. The
first conjunct asserts a trace preimage for each actual invariant element;
the second asserts trace one. Invariance and A-linearity of the displayed
sum explain the unbundled form without adding an assumption or changing the
map. Inertia modulo p agrees with identity on κ(p), also at nonmaximal primes.
The two universe variables are explicit and no binder is auto-implicit.
The zero-ring, trivial-action and free characteristic-p product cases above
still apply to the written signature. No mismatch was found and no statement
or dependency field was changed. The theorem proof remains only `sorry`.
