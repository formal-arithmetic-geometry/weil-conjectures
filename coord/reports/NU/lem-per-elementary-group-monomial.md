## Worker report

The module `Sheaf.RepresentationTheory.ElementaryGroupMonomial` states
`Representation.nilpotent_and_elementary_monomial`, with its only proof `sorry`.
It preserves the accepted stage-1 statement, proof, dependencies and review.
No definitions, new nodes, dependency repairs or statement corrections are introduced.

The inherited failure was a stage-1 unchanged-split refusal. The current node has
no Lean record and is listed at stage 2 in `coord/queue.tsv`. The stage-handoff
paragraph of `coord/brief-stage2.md` explicitly permits recording this reviewed
split's Lean statement. This delivery uses `deliver2.py`, without reopening it.

Hypotheses and clauses, read against the node:

- The first conjunct quantifies over `N : Type u`, `[Group N]`, `[Finite N]` and
  `[Group.IsNilpotent N]`. This is precisely a finite nilpotent group. Mathlib's
  nilpotence means its upper central series reaches top in finite time. Every
  term is characteristic, hence normal, and the series is increasing and begins
  at bottom. Its successor commutators lie in the previous term. Conversely a
  central series as in the node lies termwise in the upper central series:
  extend the finite series constantly by top, and apply
  `Group.nilpotent_iff_finite_ascending_central_series` (Nilpotent.lean:333).
  Switching commutator order takes inverses, so the node's order is equivalent.
  This uses the existing definition, without imposing a chosen series or class.
- `W : Type t`, `[AddCommGroup W]`, `[Module ℂ W]`,
  `[FiniteDimensional ℂ W]`, `[Nontrivial W]` give exactly the nonzero finite
  dimensional complex vector space. The group and vector-space universes are
  independent; no smallness restriction is imposed by a bundled FDRep.
- `ρ : Representation ℂ N W` is the linear group action. Although its target
  is the endomorphism monoid, the group law automatically makes every operator
  invertible. `[IsIrreducible ρ]` says its subrepresentation lattice is simple,
  i.e. it has no nonzero proper invariant subspace. Nontriviality is included
  explicitly as the node does.
- `∃ (K : Subgroup N) (χ : K →* ℂˣ)` gives exactly the subgroup and unit-valued
  character. `ofCharacter χ ℂ` is the existing upstream line representation:
  its value on k and z is `(χ k : ℂ) • z`, hence χ(k)z.
- `Nonempty (Equiv ρ (ind K.subtype (ofCharacter χ ℂ)))` asserts existence of
  a complex-linear equivariant isomorphism of the actual representations,
  rather than equality of their characters or their Grothendieck classes.
  Mathlib's induced representation is the tensor coinvariant quotient with
  diagonal K action and right-inverse N translation. Identify the node's
  `[g] ⊗ z` with `IndV.mk K.subtype (ofCharacter χ ℂ) g⁻¹ z`.
  The diagonal relation identifies `[k g⁻¹] ⊗ χ(k)z` with `[g⁻¹] ⊗ z`, which
  gives exactly `[gk] ⊗ z = [g] ⊗ χ(k)z` after reindexing. The N action sends
  g⁻¹ to g⁻¹n⁻¹ = (ng)⁻¹, hence is exactly left translation on the node's g.
  Inversion supplies a bijection of tensor bases, giving the quotient
  identification in both directions, without any added assumption.
- The field is the actual `ℂ`, not an arbitrary chosen algebraic closure.
  Mathlib supplies its characteristic-zero field structure and
  `Complex.isAlgClosed`; the latter module is imported as a proof dependency.
- The second conjunct quantifies over the finite group `E`, finite cyclic
  `C : Type v`, finite `P : Type w`, and natural numbers `p a`.
  `p.Prime`, `Nat.Coprime (Nat.card C) p`, and `Nat.card P = p ^ a`
  render respectively primality, the prime-to-p order, and the specified
  prime-power order. Naturals include exactly the allowed integers a ≥ 0.
  `(E ≃* C × P)` is the stated group isomorphism. No nilpotence assumption is
  added to this conjunct. For every nonzero finite-dimensional irreducible
  complex E representation it repeats the same subgroup, character and
  representation-equivalence conclusion. Thus the explicit consequence is
  retained as well as the general nilpotent assertion.

Dependency declarations and sources read:

- Statement dependency `def-weil-algebraic-closure` has a Mathlib match, rather
  than a `lean` record. Read `IsAlgClosed` and its root interpretation in
  `Mathlib.FieldTheory.IsAlgClosed.Basic:62`, `IsAlgClosure` at line 264,
  and `AlgebraicClosure` in `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure:127`.
  This item uses the first notion; it does not choose an algebraic closure.
- `Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic:52`
  realizes `lem-weil-complex-algebraically-closed`.
- `Representation.normal_commuting_weight_induction` in
  `Sheaf.RepresentationTheory.NormalCommutingWeightInduction` was read with
  its full signature and proof docstring, including independent universes,
  weight-space irreducibility and the canonical induction equivalence.
- `Rep.QuotientInduction.finiteGroupInductionCalculus` and its real generator
  helpers in `Sheaf.RepresentationTheory.FiniteGroupInductionCalculus` were
  read, including the full transitivity clause, naturality, and quotient
  convention. Both available project proof-dependency modules are imported
  without `public`, as required. Its bundled same-universe interface does not
  restrict this statement; stage 3 can use finite matrix models when needed.
- `lem-per-finite-prime-power-central-series` is the Mathlib match
  `IsPGroup.isNilpotent` in `Mathlib.GroupTheory.Nilpotent:1208`, applied to
  `IsPGroup.of_card` in `Mathlib.GroupTheory.PGroup:71`. Read these signatures,
  the upper-series definition, characteristic instance, endpoints and
  commutator containment. The Nilpotent module is already a statement import.
- The line construction is `Representation.ofCharacter` in
  `WeilConjectures.Mathlib.RepresentationTheory.Basic:143`, with its action
  formula at line 154. Reused directly; no second character-line definition.
- `Representation.IsIrreducible` in Mathlib's Irreducible module,
  `Representation.Equiv` in its Intertwining module, and `IndV`/`ind` in
  its Induced module were read with their definitions and documentation.

Edge cases checked: the trivial group has only one-dimensional nonzero
irreducibles and permits K = N. The zero representation is explicitly excluded.
Every one-dimensional representation permits K = N. A central series of
length zero is allowed. In the elementary clause a = 0 gives P trivial and
C may also be trivial; the cardinality and coprimality predicates allow both.
There is no faithfulness assumption. Quaternion-group dimension-two
irreducibles illustrate why induction from a proper subgroup is allowed.
Independent universes u, v, w, t include finite groups and vector spaces in
arbitrary universes. The conjunctive universal statement loses no cases.

Searches actually run through `msearch.py`:

- LeanFinder: "Every irreducible complex representation of a finite nilpotent
  group is induced from a one dimensional character of a subgroup": eight
  hits, including `Representation.IsIrreducible`, FDRep character and simple
  object criteria, and `isNilpotent_of_finite_tfae`; no monomiality theorem.
- Loogle: `Group.IsNilpotent, Representation`: zero hits.
- Mathlib grep in RepresentationTheory:
  `monomial|nilpotent|linChar|ofCharacter`: zero hits.
- LeanSearch: "Every irreducible complex representation of a finite nilpotent
  group is induced from a linear character of a subgroup": eight hits,
  including `Representation.ind`, `Representation.IndV`,
  `Representation.IsIrreducible`, and `IsPGroup.isNilpotent`; no exact result.
- Direct `rg` in both project source trees for monomiality and character-line
  names found the upstream `Representation.ofCharacter` above, and the
  distinct Brauer integral-generation theorem and its line helper; neither
  states this individual-irreducible assertion. Direct node-id grep in
  WeilConjectures found no existing declaration of this item. The upstream
  name index was also searched.

Source check: read the current blueprint's perverse-unit statement and
Artin--Gabber proof, which supply the node's ancestry rather than this
auxiliary representation assertion. The node explicitly labels its six-step
monomiality proof agent-written and the Serre reference WANTED; the module
preserves that attribution and includes all six steps in its docstring.
No mathematical statement fault or STATEMENT-DISPUTED issue was found.

Validation: `scompile.py NU lem-per-elementary-group-monomial` compiled both
the sandbox and exact library module successfully with no errors or extra
warnings. `autoImplicit` is false and all universe and term variables are
explicitly bound. The theorem signature in the node is copied verbatim.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
