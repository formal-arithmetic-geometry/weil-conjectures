## Worker report

The module `Sheaf.Algebra.Lie.FieldFilteredPBW` states
`UniversalEnvelopingAlgebra.exists_field_filtered_pbw_basis`. Its sole theorem has
`sorry` as its whole proof; its docstring carries all eight steps of the accepted DAG
proof, including the smaller-relation confluence argument and characteristic-two check.
There are no new definitions, extra nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes.

Hypotheses and clauses, matched individually:

- “F a field, of arbitrary characteristic” is `(F : Type u) [Field F]`.
  No characteristic, algebraic-closure, or nonzero-dimension restriction is imposed.
- “L a finite-dimensional Lie algebra over F” is `(L : Type v) [LieRing L]
  [LieAlgebra F L]` together with the given `e : Module.Basis (Fin n) F L`.
  A basis indexed by `Fin n` already implies finite dimensionality; a redundant
  `FiniteDimensional` instance would add no content. The two universes are independent.
- “Fix any ordered basis e_1,...,e_n, allowing n=0” is `(n : ℕ)
  (e : Module.Basis (Fin n) F L)`. The standard order on `Fin n` enumerates the
  given ordered basis from first to last, merely shifting the paper's labels by one.
- The tensor-algebra quotient `U(L)` and its map `j` are the existing Mathlib
  `UniversalEnvelopingAlgebra F L` and `UniversalEnvelopingAlgebra.ι F`.
  Reading `Rel`, `ringCon`, `mkAlgHom`, and `ι` in
  `Mathlib.Algebra.Lie.UniversalEnveloping` verifies that this is the quotient of
  `TensorAlgebra F L` by the relations `ιₜ ⁅x,y⁆ + ιₜ y * ιₜ x = ιₜ x * ιₜ y`.
  Over a ring these are exactly the two-sided-ideal relations of the node. The
  congruence quotient is the same F-algebra quotient, and `ι` is the composite
  of the degree-one linear inclusion with the quotient map. Milne p.200 explicitly
  characterizes the direct-sum tensor algebra by the universal property Mathlib uses.
- `m : Fin n → ℕ` is the exponent tuple in N^n, and
  `((List.finRange n).map (fun i ↦ ι F (e i) ^ m i)).prod` is precisely
  `j(e_1)^m_1 ... j(e_n)^m_n` in increasing order. A list product permits
  noncommuting factors; it is not a commutative finite-set product.
- “These monomials form an F-basis of U(L)” is the existential
  `B : Module.Basis (Fin n → ℕ) F (UniversalEnvelopingAlgebra F L)` and the
  first conjunct specifying every `B m` by that exact ordered-product formula.
- “For each d≥0” is `∀ d : ℕ`. The submodule in the second conjunct is
  `Submodule.span F {z | ∃ xs : List L, xs.length ≤ d ∧
  (xs.map (fun x ↦ ι F x)).prod = z}`. It is exactly the specified span of
  products of arbitrary vectors with length between zero and d, including the
  empty word, whose `List.prod` is one.
- “The elements E^m with sum m_i ≤ d form a basis of U_{≤d}” is the
  existential `Bd : Module.Basis {m : Fin n → ℕ // ∑ i, m i ≤ d} F (...)`
  for that very submodule and the equality
  `(Bd m : UniversalEnvelopingAlgebra F L) = B m.val`. Thus both independence
  and spanning concern the specified bounded-degree monomials in the specified
  word filtration, with no arbitrary replacement subspace.
- “For n=0, U(L)=F” is `n = 0 → Function.Bijective
  (algebraMap F (UniversalEnvelopingAlgebra F L))`. Bijectivity of the canonical
  F-algebra homomorphism is exactly that identification as F-algebras, retaining
  its scalar normalization. “The only basis element is 1” also follows directly
  from the first conjunct: `Fin 0 → ℕ` has one element and `List.finRange 0`
  is empty, so its product is one. The filtered clause includes this same case
  for every degree.

Dependency declarations read and used:

- `def-weil-field` has Mathlib match `Field`, read in
  `Mathlib.Algebra.Field.Defs`, including its nontrivial division-ring inheritance.
- `def-wf-lie-algebra` has a structured Mathlib match. For the notion used here,
  `LieRing` and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic` supply the alternating,
  bilinear bracket and Leibniz/Jacobi identity. These are publicly imported through
  `Mathlib.Algebra.Lie.UniversalEnveloping`; no private copy is introduced.
- Proof dependency `lem-sfb-tensor-word-basis` is matched by
  `TensorAlgebra.equivFreeAlgebra`, `TensorAlgebra.equivFreeAlgebra_ι_apply`, and
  `Module.Basis.tensorAlgebra`. Their full signatures and docstrings were read in
  `Mathlib.LinearAlgebra.TensorAlgebra.Basis`; that module is a plain proof import.
- Proof dependency `lem-sfb-triangular-linear-relations` has no Lean record or
  Mathlib match at the time of this delivery. It is needed only for the later proof,
  not to type this statement, so no import can yet be added. Its role and exact
  smaller-relation hypothesis are preserved in the proof docstring. The maintainer
  can add its proof import when it is stated. No statement dependency is missing.
- `Module.Basis` was read in `Mathlib.LinearAlgebra.Basis.Defs`; the ordered-list
  API was read in `Mathlib.Data.List.FinRange`.

Edge cases checked before drafting: zero Lie algebra / n=0 has the unique empty
exponent tuple and monomial one, with every filtered space the scalar line; d=0
has just the all-zero exponent tuple and the span of the empty product; n=1
recovers the power basis; an abelian algebra recovers usual polynomial monomials;
a nonabelian two-dimensional example with [a,b]=b still requires ordered products;
characteristic two uses alternation, with no division or extra scalar assumption.
Independent field/Lie-algebra universes impose no size equality. No hypothesis
assumes the PBW conclusion or injectivity of the generator map.

Searches (all new external searches used the prescribed `msearch.py NI
lem-sfb-field-filtered-pbw` wrapper):

- `leanfinder`, query “Ordered monomials in any basis of a finite dimensional Lie
  algebra over an arbitrary field form a filtered PBW basis of its universal
  enveloping algebra”: eight hits, including `UniversalEnvelopingAlgebra`, its
  instances and defining `Rel`, the free-Lie/free-algebra equivalence, and root-system
  Lie constructions; none is PBW for an arbitrary finite-dimensional Lie algebra.
- `loogle`, query `UniversalEnvelopingAlgebra`: twelve hits, the quotient, its
  instances, `ι`, `lift`, `mkAlgHom`, and universal-property lemmas; no basis theorem.
- `grep`, query `PBW|Poincar.*Birkhoff|ordered.monomial`, Mathlib subdirectory
  `Algebra/Lie`: three hits, only comments in `Free.lean` and `SerreConstruction.lean`
  referring to the PBW theorem as an unavailable ingredient.
- `rg -n 'PBW|pbw|filtered_pbw|orderedMonomial|envelopingFiltration'` in both
  `lean/WeilConjectures` and `lean/Sheaf`, plus searching the upstream name index:
  no upstream PBW declaration; the project has integral Kostant PBW modules over
  ℚ and their rational divided-power constructions. They do not state this
  arbitrary-characteristic filtered theorem. The signatures of the Kostant module
  and its references to the separate rational-PBW node were read.
- `grep -rn 'lem-sfb-field-filtered-pbw' lean/WeilConjectures`: no hit.
- The live item, every statement dependency, and all proof dependencies were read;
  the live item has no Lean record. No existing declaration states its result.

Source checked locally: Milne, Algebraic Groups (2017), physical PDF pp.212–217,
printed pp.200–205, especially Theorem 10.36 and the adjoining construction on
printed p.200 and the full reduction proof on pp.201–204. The theorem is over an
arbitrary field; bounded-degree reduction is the refinement recorded by the node.
No statement dispute or node fault was found. The inherited stage-1 “already split”
ending is resolved by the explicit stage-handoff rule in `coord/brief-stage2.md §0`:
a passing stage-1 split with no Lean record is the input for this stage-2 assignment.

Validation: the delivered module compiled cleanly with `scompile.py`, separately
as sandbox and library module against the live published build. The `deliver2.py --no-push` dry run passed server preflight and repeated
per-file compilation, printing `OK (dry run)` for commit `733b79bf14a`. The
final delivery reruns these checks before its push. No live source file was edited
and no direct Git command was run.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
