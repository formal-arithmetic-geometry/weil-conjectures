## Worker report

The module `Sheaf.RingTheory.IsolatedPrimeResidueFinite` states
`isolatedPrime_finiteType_residueField` with proof `sorry`. It introduces no definitions.
The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- `{k : Type u} [Field k]` is the field in the node.
- `{B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]` is a commutative
  finite type `k`-algebra, exactly the node's finite type algebra hypothesis.
- `p : PrimeSpectrum B` is the prime ideal `p ∈ Spec B`; `p.asIdeal` is its ideal.
- `hp : IsOpen ({p} : Set (PrimeSpectrum B))` renders that the singleton `{p}` is open.
- The conclusion `p.asIdeal.IsMaximal` renders that `p` is maximal, and
  `Module.Finite k p.asIdeal.ResidueField` renders that the residue field
  `κ(p) = B_p / p B_p` is finite over `k` under the canonical algebra structure.
  `Ideal.ResidueField` supplies the localization at the prime and its residue field.

Dependency declarations used: `Algebra.FiniteType` (Mathlib),
`AlgebraicGeometry.Spec`/`PrimeSpectrum` (Mathlib), `Localization.AtPrime` and
`Ideal.ResidueField` (Mathlib), and `Algebra` (Mathlib) for the field extension structure.
All are recorded as Mathlib leaves in the dependency nodes, so no project modules are imported.

Edge cases checked: the statement permits the zero commutative ring `B` when compatible
with the field algebra structure; no Noetherian, domain, nonzero, characteristic, or
separability hypotheses are added. The prime spectrum may have any universe size, and
`Module.Finite` is the finite-dimensional conclusion without choosing generators.

Searches for an existing declaration:

- `msearch.py ... leanfinder`, query “finite type algebra over a field, isolated prime of
  Spec is maximal and its residue field is finite”: only separate Jacobson and residue-field
  ingredients; no combined declaration.
- `msearch.py ... loogle`, query “PrimeSpectrum IsOpen singleton Module.Finite residue field”:
  no exact match; related quasi-finite lemmas require an extra hypothesis.
- `msearch.py ... grep`, query `finite_of_finite_type_of_isJacobsonRing|isClosed_singleton_iff_locallyOfFiniteType|quasiFiniteAt_iff_isOpen_singleton`: ingredients only, no exact theorem.
- `rg -n` in upstream `WeilConjectures` and project `lean/Sheaf` for isolated-prime and
  finite-residue statements: no matching declaration.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` applies.

## Earlier second reading (a previous round; superseded)

The node and module were reread clause by clause. The field, commutative finite type
algebra, prime-spectrum point, open-singleton hypothesis, maximality conclusion, and
finite residue-field conclusion all match the node exactly. No hypotheses or clauses are
added or omitted, and the residue field is Mathlib's `Ideal.ResidueField` at `p.asIdeal`.

## Second reading by M1

I independently opened the sandbox node and Lean file, each of the four statement
 dependency nodes and their recorded Mathlib declarations. I read the Stacks source
 in `/home/ubuntu/c1-stacks-review/algebra.tex` (the repository's literature checkout
 is absent on this machine): 00PJ at lines 30106–30192, 00G1 at 6668,
 00G3 at 6692, and 00FV at 6524. The source explicitly assumes a field,
 a finite type algebra and a prime, with no additional standing hypothesis.
 00PJ's proof explicitly identifies isolatedness with an open singleton and proves
 it closed using the Jacobson property; 00FV gives finite residue extensions for
 maximal ideals of any finite type algebra. The node extracts maximality and
 residue-field finiteness; it does not claim the entire six-condition equivalence
 or its extra zero-dimensional conclusion. No statement correction is needed.

Object, hypothesis and conclusion list, matched item by item:

- Field `k`: `{k : Type u} [Field k]`. Exact; characteristic arbitrary.
- Commutative finite type `k`-algebra `B`:
  `{B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]`.
  Exact. `Algebra.FiniteType` in Mathlib/RingTheory/FiniteType.lean is finite
  generation of the top subalgebra, as def-weil-pbc-finite-type-algebra states.
  `Algebra` in Mathlib/Algebra/Algebra/Defs.lean carries the unital ring map.
- Prime `p` in Spec B: `(p : PrimeSpectrum B)`. Exact.
  Mathlib/RingTheory/Spectrum/Prime/Defs.lean defines this as an ideal with
  its primality proof, registered as an instance. The dependency
  def-weil-affine-spectrum records AlgebraicGeometry.Spec; I read its definition
  in Scheme.lean and its `Spec_carrier` equality to `PrimeSpectrum B`.
  Only this underlying topological space is needed here, not the structure sheaf.
- Singleton open in the Zariski topology:
  `(hp : IsOpen ({p} : Set (PrimeSpectrum B)))`. Exact. The topology is the
  standard Mathlib Zariski topology in Spectrum/Prime/Topology.lean.
- First conclusion, maximality of that same ideal: `p.asIdeal.IsMaximal`. Exact.
- Second conclusion, finite extension for the specified residue field:
  `Module.Finite k p.asIdeal.ResidueField`. Exact, joined to the first by `∧`.
  In LocalRing/ResidueField/Ideal.lean, `Ideal.ResidueField` abbreviates
  `IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)`; AtPrime/Basic.lean
  localizes at the complement of the prime. This is precisely the dependency
  def-weil-pbc-localization-at-prime's field `B_p / p B_p`.
- Specified extension structure `k → B → κ(p)`: the inferred algebra on the
  localization and quotient is the canonical composite. I read the residue
  algebra instance and scalar-tower instance in LocalRing/ResidueField/Basic.lean.
  No independently chosen field or scalar structure is quantified in the Lean.
  Over a field, `Module.Finite` says finite dimension; it does not assert finite
  cardinality of the residue field. This matches def-pc-field-extension exactly.

Edge cases: the zero ring B is permitted by the ring/algebra binders but has no
prime, so the assertion there is vacuous, as in the node. The empty spectrum is
handled the same way. No nontriviality, Noetherian, domain, algebraic-closedness,
separability or characteristic restriction is added. A finite generating family
may be empty (n = 0); no positive generator count occurs. Both universes `u v`
are explicitly bound and independent. There is no test-object quantifier with a
small universe and no unbound variable. For B = k the unique point is open,
maximal, and has a one-dimensional residue field, in agreement with the statement.

Independent searches (different queries from the worker):

- `msearch.py ... leanfinder`, “Jacobson finitely generated field algebra isolated
  singleton prime maximal finite dimensional residue field”: eight related hits,
  including `instFiniteResidueField` (finite over B for an already maximal ideal),
  and quasi-finite residue-field results with extra hypotheses; no exact match.
- `msearch.py ... loogle`, `PrimeSpectrum, IsOpen`: twelve hits. The singleton
  TFAE for Noetherian Jacobson rings supplies closedness only;
  `Algebra.QuasiFiniteAt.of_isOpen_singleton` supplies quasi-finiteness only.
  Neither states the two conclusions of this node together.
- `msearch.py ... leansearch`, “An open point in the spectrum of a finite type
  algebra over a field is maximal and has a finite dimensional residue field”:
  service unavailable (Internal Server Error), so no verdict assigned to it.
  The other searches and direct source searches succeeded.
- Direct `rg` in Mathlib RingTheory and Topology/JacobsonSpace.lean for isolated
  primes/residue fields, open singletons, and
  `finite_of_finite_type_of_isJacobsonRing`: separate Jacobson, quasi-finite and
  finite-field-algebra ingredients only. I opened their relevant signatures.
- Direct `rg` in upstream WeilConjectures and repository lean/Sheaf with the same
  conceptual terms and the full proposed declaration name: no exact combined
  statement or name collision. The existing finite-set-of-isolated-points theorem
  in Sheaf/AlgebraicGeometry/FiniteIsolatedPointsOfFiniteType.lean has a different
  conclusion and does not replace this node.

Mismatches repaired: H8, the original proof docstring summarized the route but
omitted the node's witness argument and the surjectivity/generator-transfer step.
I replaced it with all three steps, naming the proof dependency nodes and sources.
H9, the file lacked the standard license/authorship header, had an unused
`open scoped Polynomial`, imported the unused scheme module and used proof-only
Jacobson imports. I added the standard header, removed the unused scope, and
used the three modules supplying finite type, prime-spectrum topology and residue
fields. The module docstring now precedes the universe command, as in the example.
The theorem name, signature, node and its verbatim `lean.statement` remain correct
and unchanged. No definitions, additional theorems, new nodes or dependency
modules are necessary; the only proof is `sorry`, with no hollow data.

Validation: the prescribed `scompile.py` on the absolute sandbox module path
compiled cleanly on the server in 1.4 seconds, with no warnings or errors.
