## Worker report

The module `Sheaf.RingTheory.FiniteFunctionSubringResidueTest` states
`Subring.exists_maximal_residue_of_ne_top` with one
postponed proof (`sorry`). It introduces no definitions and no new DAG nodes. The
statement is the node's proper-ideal residue evaluation assertion, rendered as follows.

| Node clause | Lean rendering |
| --- | --- |
| Nonzero commutative unital ring (A) | `{A : Type u} [CommRing A] [Nontrivial A]` |
| (A) finitely generated as a Z-module | `[Module.Finite ℤ A]`; this is Mathlib `Module.Finite` (the recorded `def-weil-finitely-generated-module`) |
| finite nonempty set (X) | `{X : Type v} [Finite X] [Nonempty X]` |
| unital subring B of A^X | `(B : Subring (X → A))`; the `Subring` structure supplies coordinatewise ring operations, unity, additive inverses and multiplication closure |
| all constant functions lie in (B) | `hconst : ∀ a : A, (fun _ : X ↦ a) ∈ B` |
| proper ideal I of B | `(I : Ideal B)` and `hI : I ≠ ⊤` |
| coordinate and maximal ideal | `∃ (x : X) (q : Ideal A), q.IsMaximal ∧ ...`; `Ideal.IsMaximal` is proper and maximal among proper ideals |
| every `f ∈ I` evaluates into `q` | `(∀ f : B, f ∈ I → (f : X → A) x ∈ q)` |
| quotient is a finite nonzero field | `IsField (A ⧸ q) ∧ Finite (A ⧸ q) ∧ Nontrivial (A ⧸ q)`; `A ⧸ q` is Mathlib's ideal quotient, carrying the quotient-module operations and coset multiplication |
| characteristic is a prime | `∃ p : ℕ, Nat.Prime p ∧ CharP (A ⧸ q) p` |

The proof docstring records the source argument for stage 3: the finite-product
polynomial proves integrality of (A^X) over (B); maximality, lying-over and the
finite-product prime classification produce (x,q); the quotient is finitely generated
additively, the finitely generated abelian-group structure eliminates free summands in a
field and proves finiteness, and the least positive annihilator of (1) is prime.

Dependency declarations read and used:

- `def-weil-finitely-generated-module`: Mathlib `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-quotient-module`: Mathlib ideal quotient notation `A ⧸ q` and its
  quotient module/ring structures from `Mathlib.RingTheory.Ideal.Quotient.Basic` and
  `Mathlib.RingTheory.Ideal.Quotient.Defs` (the node's recorded `Submodule.hasQuotient`,
  `Submodule.Quotient.module`, `Submodule.mkQ` family).

The proof-only imports follow all recorded proof dependencies: `Ideal.exists_le_maximal`
(`Mathlib.RingTheory.Ideal.Maximal`), `RingHom.IsIntegral.comap_surjective`
(`Mathlib.RingTheory.Spectrum.Prime.Topology`),
`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'` (`Mathlib.RingTheory.Ideal.GoingUp`),
`PrimeSpectrum.exists_comap_evalRingHom_eq` (`Mathlib.RingTheory.Spectrum.Prime.RingHom`),
and `AddCommGroup.equiv_free_prod_directSum_zmod` (`Mathlib.GroupTheory.FiniteAbelian.Basic`).
The quotient-field leaf `Ideal.Quotient.field` is in the public quotient import.
The complete six-step proof is retained in the theorem docstring with all DAG citations.

Edge cases checked before writing: `Nonempty X` excludes the empty product case; a
singleton (X) reduces to the ordinary maximal-residue test; (I=0) is allowed while
`I=⊤` is excluded; `A=0` is excluded by `Nontrivial A`; the quotient's nonzero clause is
explicit; and characteristic (p) is explicitly required to be prime. The ring and index universes `u` and `v` remain independent and no statement clause is
weakened or strengthened.

Searches made on 2026-10-24:

- `msearch.py Q34 lem-per-finite-function-subring-residue-test leanfinder` with query
  "A proper ideal of a subring of functions from a finite nonempty set to a ring finite
  over the integers containing constant functions vanishes at a coordinate modulo a
  maximal ideal with finite residue field": 8 hits, including
  `Ideal.exists_forall_sub_mem_ideal`, `Ideal.exist_integer_multiples_notMem`,
  `exists_integral_inj_algHom_of_quotient`, and
  `PrimeSpectrum.exists_image_comap_of_finite_of_free`; none states this item.
- `msearch.py ... loogle "PrimeSpectrum.exists_comap_evalRingHom_eq,
  Ideal.Quotient.field"`: 0 hits for the combined query.
- `msearch.py ... grep
  "finite.*[Ss]ubring|[Ss]ubring.*residue|exists_comap_evalRingHom_eq" RingTheory`:
  12 hits. The prime-spectrum lemma classifies primes in the full product, but does
  not handle arbitrary proper ideals of the intermediate subring or residue finiteness.
- `msearch.py ... leansearch` with query "Every proper ideal of a subring of a finite
  power of an integer finite commutative ring containing constants lies in a coordinate
  maximal ideal with finite residue field": 8 hits, including
  `IsLocalRing.le_maximalIdeal`, `Ideal.finite_quotient_pow`, and
  `instFiniteResidueField` (module finiteness over A, not finite cardinality); no match.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `finiteFunctionSubring|finite_function_subring|function.*[Ss]ubring.*[Rr]esidue`,
  the exact item id and the chosen theorem name: no existing declaration.
  `rg` over `dag/nodes` located this item and its parent use, without a duplicate.

No `STATEMENT-DISPUTED` flag, dependency repair, or statement correction is needed.

## Second reading by Q34

I reread the node and final file clause by clause myself; the dispatcher forbids
starting other agents and the maintainer supplies the independent review.
The initial draft omitted `f ∈ I` in the evaluation conclusion and thus wrongly
asserted vanishing of all of B. I fixed it to
`∀ f : B, f ∈ I → (f : X → A) x ∈ q`. In particular this no longer forces
`1 ∈ q` when `I=0`. I also replaced an invalid type expression `Ideal.Quotient q`
with the actual ideal quotient `A ⧸ q`, added the characteristic definition import,
and included every recorded proof-dependency module. The final signature has
precisely the nonzero, integer finite-generation, finite nonempty index, constants,
and proper-ideal hypotheses. It concludes existence of the coordinate and maximal
ideal, vanishing of every ideal member, finite nonzero quotient field, and prime
characteristic. `Ideal.instHasQuotient` explicitly uses `Submodule.hasQuotient`, so
this is the recorded quotient module with its actual coset multiplication, not a
second quotient construction. The full source-based six-step proof is in its
docstring. I moved the generic algebra lemma into `Sheaf/RingTheory` and the
`Subring` namespace, following the topic convention. No node text changes were needed.

Validation: `scompile.py Q34 lem-per-finite-function-subring-residue-test` compiled
the final sandbox and real module path without errors or non-sorry warnings (3.6 and
1.5 seconds). The only non-comment declaration is the named theorem with `sorry`.

The prescribed dry run passed preflight and compiled every delivered file; only the
item node, module, and worker report are staged by the authorized delivery wrapper.
