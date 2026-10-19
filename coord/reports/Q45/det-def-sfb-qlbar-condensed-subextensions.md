## Worker report

The module `lean/Sheaf/Paper/FiniteSubextensionsDirected.lean` states
`PadicAlgCl.finiteSubextensions_directed`.  It uses the canonical Mathlib algebraic closure
`PadicAlgCl ℓ` of `ℚ_[ℓ]`, and the existing upstream notion
`PadicAlgCl.FiniteIntermediateField ℓ`, whose elements are intermediate fields with a
`FiniteDimensional ℚ_[ℓ]` instance.

For clause 1, a finite family is `E : Fin n → FiniteIntermediateField ℓ`.  Its compositum is
written as the complete-lattice supremum
`iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (fun i : Fin n => (E i).1)`.
The first conjunct states finite dimensionality, the second says every `E i` is contained in
that supremum, and the third is the degree bound using `Module.finrank` and the finite product.
The empty-family case is included by `Fin 0`, whose supremum and product are the empty
compositum and the empty product.  `Nonempty (FiniteIntermediateField ℓ)` states that the
base field is a finite subextension, and the following existential gives a common upper bound
for any two fields, i.e. directedness under inclusion.

For clause 2, the `Finset (PadicAlgCl ℓ)` conjunct says every finite subset is contained in a
finite subextension.  The final universal-existential says every element of `PadicAlgCl ℓ` lies
in a finite subextension; since each subextension is by definition a subset of the algebraic
closure, this is exactly the two inclusions asserting that the closure is their union.

The source dependencies are represented as follows: the prime-adic field is Mathlib's
`ℚ_[ℓ]` (`Padic`), the chosen algebraic closure is `PadicAlgCl ℓ` (`AlgebraicClosure`), finite
dimensionality is `FiniteDimensional`, and the degree is `Module.finrank` from
`Mathlib.LinearAlgebra.Dimension.Finrank`.  The finite-subextension subtype is the existing
upstream declaration `PadicAlgCl.FiniteIntermediateField` in
`WeilConjectures.CategoryTheory.RingObjects.EllAdic`; no private copy is introduced.

The prime hypothesis is the explicit section binder `(ℓ : ℕ) [Fact ℓ.Prime]`.
`Padic` is defined in `Mathlib.NumberTheory.Padics.PadicNumbers` as the Cauchy completion
for the prime-adic norm. `PadicAlgCl` is Mathlib's abbreviation for
`AlgebraicClosure ℚ_[ℓ]` in `Mathlib.NumberTheory.Padics.Complex`, so the ambient field
is precisely a fixed algebraic closure, with its canonical algebra structure.
`FiniteDimensional` is the finite-module abbreviation in
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`; `Module.finrank` is defined in
`Mathlib.LinearAlgebra.Dimension.Finrank`. The inclusion order on the existing
finite-intermediate-field subtype inherits its partial order from `IntermediateField`;
the theorem supplies its nonemptiness and common-upper-bound clauses explicitly.

The actual public import used for the finite-intermediate-field interface is
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, which publicly imports
the owning `WeilConjectures.CategoryTheory.RingObjects.EllAdic` module. This framework
is read from the side-project sources, as required by the current isolation instructions;
it is absent from the older source checkout. The report's earlier description of this
interface as found in the older checkout was inaccurate.

The proof dependencies are Mathlib leaves: `IntermediateField.adjoin_rank_le_of_isAlgebraic_right`
and `IntermediateField.finiteDimensional_adjoin` in
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`, and `Module.finrank_mul_finrank`
in `Mathlib.LinearAlgebra.Dimension.Free`. They supply, respectively, the relative
compositum degree estimate, the finite-algebraic-generator assertion, and the tower formula.
The finite-family induction uses the binary estimate and the tower formula, starting with
the bottom intermediate field of degree one. For each finite subset, adjoining its
algebraic elements gives the containing finite extension; singleton subsets yield the union.
The tower-formula module is imported without `public`, since it is a proof dependency.
The resumed worker expanded the declaration's proof docstring to all four DAG steps,
removed an unused universe and a stray final variable command, and left the theorem
signature and all natural-language node fields unchanged.

Edge cases checked: `n = 0` (empty compositum and product), the singleton family, the base
field as the nonempty witness, the empty finite subset, and singleton finite subsets.  The
statement imposes no separability, disjointness, completeness, or nonempty-index hypothesis.

Searches made:

* `msearch.py ... leanfinder "finite intermediate fields in an algebraic closure are directed under compositum and every finite subset lies in a finite subextension"`: eight related hits, including `IntermediateField.instIsCompactlyGenerated`, `Field.Emb.Cardinal.directed_filtration`, and finite-adjoin lemmas; no whole statement.
* `msearch.py ... loogle "PadicAlgCl.FiniteIntermediateField, IntermediateField, Module.finrank"`: no hits (the namespace is project-side rather than Mathlib-indexed).
* `msearch.py ... grep "FiniteIntermediateField|finite_intermediateField|finrank_sup" Mathlib/FieldTheory`: no direct hit for the whole statement.
* `rg` over the source and project found the exact existing notion `PadicAlgCl.FiniteIntermediateField` and its `Nonempty` and `IsDirectedOrder` instances in the side project's `WeilConjectures/CategoryTheory/RingObjects/EllAdic.lean`. The generic finite-subextension infrastructure in the older checkout's `WeilConjectures/AlgebraicGeometry/IntermediateFieldLimit.lean` does not state the entire conjunction here.
* The resumed worker read the current blueprint source, every statement dependency and its Mathlib declaration, and the three proof-dependency matches. A repeated Mathlib-wrapper grep for `finiteSubextensions_directed|finrank_sup_le|finiteDimensional_adjoin` returned zero indexed hits; direct source reads confirm the ingredient declarations. Direct project searches found no declaration of the full conjunction in either read-only checkout.
* A resumed `msearch.py` LeanFinder query, "Finite intermediate fields of an algebraic closure have finite composita of degree at most the product of degrees and cover every finite subset", returned eight related declarations, including `finiteExts`, `IntermediateField.fg_top`, and `IntermediateField.exists_finset_of_mem_supr'`; none states the whole conjunction.

Compilation with `scompile.py` succeeds with no warnings other than the expected `sorry` declaration
warning (the final clean compile emits no style warnings).  No new nodes or dependency repairs
were needed.

## Second reading by Q45

I independently read the sandbox node and module against the source markdown
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-qlbar-condensed/det-def-sfb-qlbar-condensed-subextensions.md` and its parent
unit. The markdown contains the two numbered assertions, with no extra standing
hypothesis. I also read Stacks `fields.tex`, definition-compositum (09ID),
lemma-multiplicativity-degrees (09G9), lemma-algebraic-finitely-generated (09GH),
and definition-algebraic-closure (09GS), including their surrounding assumptions.
The compositum is taken inside a specified common ambient field; neither linear
disjointness nor separability is assumed. There is no repair note for this item.

The object/hypothesis/conclusion inventory, matched to Lean, is:

1. Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. This is precisely the sole numerical
   hypothesis; it includes ell = 2. Verdict: exact.
2. Base field k = Q_ell: `ℚ_[ℓ]`. I opened the dependency
   `def-weil-l-adic-numbers` and its Mathlib match `Padic`, the Cauchy completion
   for the ell-adic norm (`PadicNumbers.lean:531`). Verdict: the same field.
3. A fixed algebraic closure: `PadicAlgCl ℓ`. I opened
   `def-weil-algebraic-closure`, `AlgebraicClosure` and `IsAlgClosure`, and
   `Complex.lean:54`: this abbreviation is exactly `AlgebraicClosure ℚ_[ℓ]`,
   not its completion. This implements the source's fixed choice. The dependency
   explicitly permits choosing one algebraic closure once and for all; choices
   in other universes are isomorphic over k by `IsAlgClosure.equiv` (whose
   universe-polymorphic signature I read), so this fixed-model convention does
   not change the field-theoretic assertion. Verdict: exact chosen object.
4. Finite subextensions and their order: `FiniteIntermediateField ℓ`, whose
   actual definition in the side framework's
   `WeilConjectures/CategoryTheory/RingObjects/EllAdic.lean:115` is
   `{E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}`.
   I read its finiteness, nonempty and directed-order instances. Its subtype
   order inherits the partial order of intermediate fields. No arbitrary
   embedding, extra finiteness assumption or private definition occurs.
   Verdict: exact.
5. Degree: `Module.finrank ℚ_[ℓ] E.1`. I opened the two dimension dependency
   nodes, `FiniteDimensional` (the abbreviation for `Module.Finite`) and
   `Module.finrank`. All fields whose degrees appear are finite-dimensional,
   either by their subtype property or by the first conclusion. Verdict: exact
   natural-number dimension, including for the compositum.
6. Finite family and compositum: `∀ (n : ℕ) (E : Fin n → FiniteIntermediateField ℓ)`
   and the supremum in `IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)`. This is the
   smallest intermediate field containing all family members, in the same
   ambient closure. The first inner conjunct is `FiniteDimensional` of that
   supremum; the second is `∀ i, (E i).1 ≤ iSup ...`; the third is its
   `Module.finrank` bounded by `∏ i, Module.finrank ... (E i).1`.
   Verdict: all three clauses of the finite-family assertion, in order.
7. Directed poset: `Nonempty (FiniteIntermediateField ℓ)` and
   `∀ E F, ∃ G, E.1 ≤ G.1 ∧ F.1 ≤ G.1`, with the inherited partial order just
   identified. Existing instances already prove these two parts, but not the
   whole node. Verdict: exact meaning of directed poset; no extra conclusion.
8. Every finite subset is contained: `∀ S : Finset (PadicAlgCl ℓ), ∃ E, ∀ x,
   x ∈ S → x ∈ E.1`. Finsets encode every finite subset of this fixed field.
   Verdict: exact quantifier order, with E allowed to depend on S.
9. Union of all finite subextensions: `∀ x : PadicAlgCl ℓ, ∃ E, x ∈ E.1`.
   Every E is already a subfield of the specified closure, so the opposite
   union inclusion is built into its type. Verdict: exactly equality with the
   union, rather than merely generation or density.

Edge cases: `Fin 0` is allowed and gives bottom, the embedded base field, with
empty product 1 and degree 1; no nonempty-family binder excludes it. The empty
finite subset is allowed and the bottom field supplies a witness. Repeated
fields, singleton families, x = 0, and x in the base field are covered without
new assumptions. A zero field is excluded by the source's field assumption,
not an extra restriction. Empty schemes and scheme dimensions are inapplicable
because no scheme occurs. There is no independent index universe or free universe
parameter: this is a finite list of subfields of the fixed closure, of arbitrary
length. All variables are bound, including ell and its prime instance.

Independent duplicate searches used different wording from the worker:

- LeanFinder: "A finite set of elements in an algebraic field extension belongs
  to one finite intermediate field and finite joins have degree bounded by a
  product". Eight hits included `finrank_sup_le`,
  `finiteDimensional_iSup_of_finset`, `finiteExts`, and `fg_iSup`.
- Loogle: `IntermediateField, FiniteDimensional, Finset`. Three hits, including
  the two finite-finset supremum lemmas; none states the full conjunction.
- LeanSearch: "Finite subextensions of an algebraic closure cover every finite
  subset and their finite compositum has degree at most the product of their
  degrees". Eight related hits, including `finiteExts`, relative rank bounds,
  and finite intermediate-field counting; none is this node.
- Direct `rg` searched Mathlib field theory, the older source's
  `WeilConjectures`, repository `lean/Sheaf`, the side ring-object framework and
  `dag/lean_names_upstream.json`, using `finrank_iSup`, `finiteDimensional_iSup`,
  `finrank_sup_le`, `FiniteIntermediateField`, `exists_finset_of_mem_supr`, and
  `finiteSubextensions_directed`. I opened the partial-match declarations.
  The existing subtype and directedness instances are reused; no existing
  declaration states the entire node. In particular `finiteExts` is a set of
  finite intermediate fields, not this theorem.

I opened every statement dependency and its recorded declaration, and all three
proof dependency matches. The relative rank bound, finite algebraic adjoin,
and tower degree formula have the required field/tower hypotheses. The imports
expose these declarations. The theorem docstring follows all four DAG proof
steps, including empty-family induction, finite subsets and both union
inclusions. There is exactly one theorem with proof `by sorry`, no new data
definition, helper theorem, new node or dependency repair. No statement_change
is present or needed, hence there is no correction/citer audit to perform.

No mathematical or signature mismatch was found. I preserved the Lean and node
record and added this independent reading only. I checked that `lean.statement`
is verbatim the theorem signature in the sandbox file. Compilation and delivery
preflight are recorded below after running the prescribed wrappers.

Second-reader validation: `scompile.py Q45 det-def-sfb-qlbar-condensed-subextensions
<absolute sandbox module path>` succeeded. Its local attempt timed out at 60 s;
the wrapper's current-server confirmation compiled the delivered module in 1.9 s
with nice 19, two threads and the unchanged 60-second limit, without warnings.

`deliver2.py Q45 det-def-sfb-qlbar-condensed-subextensions --no-push` printed
`OK (dry run): commit b775ac1e3b passes the preflight and compiles; nothing pushed`.
The shared fetch lock caused a wait but the wrapper completed successfully.
