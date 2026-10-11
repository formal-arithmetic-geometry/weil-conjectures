## Worker report

The module `Sheaf.RingTheory.TensorFiniteTypeLimit` states
`Algebra.tensor_finite_type_limit`, with the two clauses of Stacks Algebra Lemma 00I3
in one conjunction. The field hypothesis is `[Field k]`; `R` and `S` are
commutative rings with their `k`-algebra structures. A finitely generated
`k`-subalgebra is represented by `R' : Subalgebra k R` (respectively
`S' : Subalgebra k S`) together with the proposition `Algebra.FiniteType k R'`
(respectively `Algebra.FiniteType k S'`). The tensor products are Mathlib's
`R ⊗[k] S` and `R' ⊗[k] S'`.

For clause (1), the hypothesis `¬ IsReduced (R ⊗[k] S)` and conclusion
`∃ R' S', Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
¬ IsReduced (R' ⊗[k] S')` render the nonreduced assertion and finite-type
subalgebra witnesses. For clause (2), the hypothesis
`∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0` renders a nonzero zero-divisor
pair, and the conclusion gives the corresponding pair in the finite-type
subalgebra tensor product. The proof is `sorry`, as required at stage 2.

The dependency `def-pc-field-extension` is a Mathlib leaf (`Algebra` in
`Mathlib.Algebra.Algebra.Defs`); its convention is exactly the `[Field k]`
plus `[Algebra k R]` form used here. The proof-level filtered-colimit nodes are
not statement dependencies and are not imported in this statement module.

Edge cases checked: the statement allows arbitrary universes for `k`, `R`, and
`S`; zero rings and zero tensor products are not excluded by the binders; the
zero-divisor clause explicitly requires both factors to be nonzero; and no
characteristic or finite-dimensionality assumption is added.

Source read: [Stacks Tag 00I3](https://stacks.math.columbia.edu/tag/00I3),
clauses (1) and (2) and the proof. The local literature checkout is absent;
the online source confirms the node's statement. Clause (3) is outside this node.
The module docstring carries all three proof steps of the DAG node.

Searches made (actual tool results):

* `msearch.py leanfinder "finite type subalgebra limit argument tensor product zero divisor"`:
  eight hits, including `exists_fg_and_mem_baseChange`,
  `IsReduced.tensorProduct_of_flat_of_forall_fg`, and
  `TensorProduct.Algebra.exists_of_fg`. The first and last are element
  representatives; the middle reduces only one factor and only reducedness.
  None states the two-clause lemma. Read the middle declaration and docstring
  in `Mathlib/RingTheory/Flat/Basic.lean:642`.
* `msearch.py loogle "Subalgebra.FG, Algebra.FiniteType, IsReduced, TensorProduct"`:
  zero hits.
* `msearch.py leansearch "nonreduced tensor product and zero divisors descend to finitely generated subalgebras"`:
  unavailable: Internal Server Error; no claim of a negative search result.
* `msearch.py grep "exists_finset.*tensorProduct|finitely generated.*subalgebra.*tensor|tensorProduct_of_flat_of_forall_fg" RingTheory`:
  two hits, the flatness lemma and its use in geometrically reduced algebras.
* `rg -n 'tensor_finite_type_limit|tensor.*finite.*type'` over pinned Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  one unrelated Mathlib comment and two references to this node/other nodes
  in project docstrings, no existing statement or declaration name.
* `grep -rn 'lem-weil-pbc-tensor-finite-type-limit' WeilConjectures`:
  no matches.
* Additional Mathlib searches and source reads located `Subalgebra.FG` in
  `Mathlib.RingTheory.Adjoin.FG:95`, `Algebra.FiniteType` in
  `Mathlib.RingTheory.FiniteType:40`, and `Subalgebra.fg_iff_finiteType:197`.
  `IsReduced` in `Mathlib.Algebra.GroupWithZero.Basic:191` says every nilpotent
  is zero, so negating it is exactly nonreducedness. These existing notions
  suffice; no definitions or dependency modules are added.

## Earlier second reading (a previous round; superseded)

Independent second reading is pending the dispatcher-assigned second worker.
This section is a placeholder required by the dry-run preflight, not a claim
that an independent reading has occurred. The author's own check matches the
shared field/algebra binders, both finite-type subalgebra witnesses, and the
nonreduced and nonzero zero-divisor conclusions clause by clause as described
in the worker report. The second worker should replace this section after reading.

## Second reading by V1

Independent second reader, dispatcher-assigned; opened the sandbox node and Lean
module together, the statement dependency node, and the pinned declarations.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. Base field k: `(k : Type u) [Field k]`. No algebraic closure, perfection,
   characteristic, or finite-dimensionality assumption. Read
   `def-pc-field-extension` and its recorded `Algebra` declaration in
   `Mathlib.Algebra.Algebra.Defs:95`: an algebra carries the unital ring map.
   This item only uses the base field and algebra structure, and does not assert
   that R or S is a field extension; appropriately, neither has `[Field]`.
2. Two k-algebras R and S: `(R : Type v) [CommRing R] [Algebra k R]` and
   `(S : Type w) [CommRing S] [Algebra k S]`. Stacks algebra.tex conventions
   explicitly require commutative rings with 1 and allow the zero ring. Read
   section-geometrically-reduced and the paragraph immediately preceding
   lemma-limit-argument: there is no extra standing reducedness assumption.
3. Tensor product: `R ⊗[k] S`, Mathlib's algebra tensor product with the displayed
   k-algebra structures, and `R' ⊗[k] S'` with their induced structures.
4. Clause (1) hypothesis: `¬ IsReduced (R ⊗[k] S)`. Read `IsReduced` and
   `IsNilpotent` in Algebra.GroupWithZero.Basic: all nilpotents must be zero,
   exactly the node's reducedness notion.
5. Clause (1) witnesses: `∃ (R' : Subalgebra k R) (S' : Subalgebra k S)`;
   read Subalgebra in Algebra.Algebra.Subalgebra.Basic:29, a subring containing
   the image of k. Its subtype is the actual included subalgebra, not another
   abstract algebra or an assumed embedding.
6. Clause (1) finite generation and conclusion:
   `Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
   ¬ IsReduced (R' ⊗[k] S')`. Read FiniteType:40, Subalgebra.FG in Adjoin.FG:95,
   and `Subalgebra.fg_iff_finiteType` in FiniteType:197. This means finite
   generation as an algebra, not finiteness as a module.
7. Clause (2) hypothesis: `∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0`.
   In a commutative ring this is precisely a nonzero zero divisor: x is nonzero
   and is annihilated by nonzero y. Neither factor can be the spurious zero.
8. Clause (2) conclusion: independent existential subalgebra witnesses with both
   finite-type predicates and `∃ x y : R' ⊗[k] S', x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0`.
   The two implications are conjoined; the node does not require common
   witnesses for the two clauses, or particular lifts of the original elements.
   Quantifier order is correct. The source's idempotent clause (3) is outside
   this node, so its absence is correct.

Source reading: the local literature checkout has no Stacks .tex. Read the raw
Stacks algebra.tex in this item's scratchpad, lines 32-41 (conventions),
10037-10059 (section introduction), and 10098-10135 (injectivity observation,
lemma-limit-argument, and proof), obtained from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex .
Also checked https://stacks.math.columbia.edu/tag/00I3 . The two node clauses
are exactly the first two source clauses. No statement correction is needed;
there is no statement_change record to audit and no new node or dependency
module in this delivery.

Edge cases: R or S may be the zero ring; the tensor is then zero and reduced
and has no nonzero zero-divisor pair, making both antecedents false. The empty
finite generating set is permitted by FG/FiniteType. There is no index set,
scheme, or degree parameter in the signature. The hidden nilpotence exponent
ranges over all natural numbers, including 0; in a nonzero ring the zeroth
power cannot vanish, and in the zero ring there is no nonzero witness.
Independent bound universes u, v, w permit differently sized fields/algebras;
there is no independent universe of test objects that could make a hypothesis
vacuous. All characteristics are covered. No variable or universe is unbound.

Independent searches, with queries different from the first worker's:

- LeanFinder via msearch: "nilpotent elements and vanishing products witnessed
  in finite generated tensor subalgebras": eight hits. Read the closest
  `IsReduced.tensorProduct_of_flat_of_forall_fg` in RingTheory.Flat.Basic:642
  and `TensorProduct.Algebra.exists_of_fg` in TensorProduct.DirectLimitFG:248.
  The former is a one-factor reducedness criterion with flatness; the latter
  only represents an element. Neither states both node clauses.
- Loogle via msearch: `IsReduced, Subalgebra.FG`: one hit, the same flatness
  criterion. No exact statement.
- LeanSearch via msearch: "nonzero nilpotents descend along the union of finite
  generated subalgebras of two tensor factors": Internal Server Error,
  explicitly unavailable, not a negative result.
- msearch grep `zero.divisor|zerodivisor|nilpotent|IsReduced` in
  RingTheory/TensorProduct: zero hits. Broader rg over pinned Mathlib,
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json used
  `tensor_finite_type_limit`, `tensorProduct_of_flat_of_forall_fg`,
  `exists_of_fg`, `exists_fg_and_mem_baseChange`, `zero.divisor.*tensor`,
  `tensor.*zero.divisor`, `nilpotent.*subalgebra`, and
  `nonreduced.*tensor|tensor.*nonreduced|zero.divisor.*finitely|zerodivisor.*finitely`.
  Read upstream WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG:
  its results descend unit ideals, not reducedness or zero divisors. Other
  hits are element representation, geometrically reducedness, and unrelated
  Cartier/blowup results. No exact existing statement or name collision.

H5/H6/H8/H9: no definition or extra theorem is introduced; the only theorem
has `sorry`. Both docstrings identify the source and blueprint node. Its proof
text reproduces all three DAG steps, including directed finite subalgebras,
representatives and eventual zero after tensoring, two successive descents,
and nonzeroness from nonzero images. Imports supply the algebra tensor product
and FiniteType; lines are within 100 characters and the namespace is Algebra.
The node's lean.statement was compared with the file signature and is verbatim
identical. No mathematical, signature, documentation, or dependency mismatch
was found; the Lean and node are preserved. Changed only this report by adding
this independent second reading. Compilation and delivery preflight are run
with the launcher tools before delivery.
