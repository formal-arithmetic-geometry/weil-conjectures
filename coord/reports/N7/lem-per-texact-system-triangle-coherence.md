## Worker report

The module `Sheaf.CategoryTheory.Triangulated.TExactSystemTriangleCoherence` states
`CategoryTheory.Triangulated.TStructure.texact_system_triangle_coherence` and its
single-functor companion `texact_triangle_cutoff_coherence`. Both proofs are `sorry`.
The repair adds one definition node, `def-per-truncation-cohomology-comparison`,
with an `existing: true` binding to the already landed `truncationCohomologyComparison`.
It replaces `lem-a1-cohomology-comparison-pasting` in `stmt_deps`; the latter stays in
`proof_deps`. No Lean source changes, dependency repairs, or statement corrections are needed.

Source read: BBD, Proposition 1.3.3(i),(ii), printed pp. 29--30, the adjacent 1.3.4--1.3.6
and H^i convention, and Proposition 1.1.9/Corollary 1.1.10, printed pp. 23--24.
The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.md`
was also read. The system identities are the agent assembly described by the node,
not an assertion that BBD separately numbers this system lemma.

Hypotheses, in statement order:

- A small nonempty directed poset is `{I : Type uI} [PartialOrder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The categories form `C : I → Type uC`, with a separate
  morphism universe `vC`. No colimit is formed, so no equality between the index and
  category universes is imposed. These explicit universe bounds implement the size
  convention; its recorded pro-etale `ModuleDerivedCategory` is a realization of that
  convention, not the category family in this abstract statement.
- Each `C i` has `Category`, `Preadditive`, `HasZeroObject`, `HasShift` by integers,
  additive shifts, `Pretriangulated`, and `IsTriangulated`. These are exactly the
  recorded Mathlib encoding of a triangulated category.
- `t i : TStructure (C i)` and `_bounded : ∀ i, (t i).bounded = ⊤` give the bounded
  t-structures. No nondegeneracy or uniform bound is added.
- `T i j hij` is the transition for `hij : i ≤ j`. Its `CommShift ℤ`, `IsTriangulated`,
  and `IsTExact (t i) (t j)` instances express the specified coherent shifts, exactness,
  and preservation of both halves at every integer degree.
- `unit i : T i i le_rfl = 𝟭 (C i)` is the node's literal diagonal identity.
  `eqToIso (unit i)` only transports across this equality. No additional shift
  compatibility of this transport is assumed: exactness of a and its unit equations
  force it, as explained explicitly in proof step 5 of the node.
- `a i j k hij hjk` is exactly the supplied natural associator. Its `NatTrans.CommShift`
  instance means it commutes with the specified shifts. `_unitLeft`, `_unitRight`
  are the two unit equations using `unit`; `_pentagon` is the four-index associativity
  equation evaluated on an arbitrary object. Evaluation loses no information about
  equality of natural transformations, and functor parentheses have definitionally
  the same objects in the displayed equation.
- The single-functor theorem retains the same two bounded t-categories, shift structure,
  exactness and t-exactness. The transformation clause quantifies over a second such
  functor and any `η : F ⟶ G` with `NatTrans.CommShift η ℤ`; η need not be invertible.

Conclusions, clause by clause:

- Both signs of the displayed system equation are the first conjunction of
  `texact_system_triangle_coherence`: `eTruncLTIso` at `r + 1` is c-minus for τ≤r,
  and `eTruncGEIso` at `r` is c-plus for τ≥r. Lean's `≫` writes composition in the
  reverse textual order from the node's mathematical convention.
- The next conjunction is `c_{i/i,r}=1`, transported through the equality `unit i`.
  After substituting `unit`, both `eqToIso` components become identities, giving
  the literal identity assertion. No freely chosen comparison is substituted.
- The existential family `e i j hij n` is a natural isomorphism in the category of
  triangles, from the mapped whole truncation triangle to that of the mapped object.
  Its components are c-minus, the middle identity, and c-plus. Taking `n=r+1`
  gives precisely `(c^-_r,1,c^+_{r+1})`.
- In `texact_triangle_cutoff_coherence`, the fourth equation in the component block
  writes the third square explicitly: `cPlus ≫ δ = F.map δ ≫ σ ≫ shift.map cMinus`.
  The shift is exactly `(F.commShiftIso (1 : ℤ)).hom`; no replacement boundary or
  unrelated shift map appears. A triangle isomorphism entails all three squares.
- Changes of cutoff are the existing `natTransTriangleLTGEOfLE n m hnm`, whose
  components are the existing canonical truncation cutoff maps and the identity.
  Both the single-functor theorem and the system existential give the equality of
  whole triangle natural transformations with those maps, including the last arrow.
  These canonical maps already have identity and transitivity laws in Mathlib.
- The whole-triangle identity equation supplies the canonical lift `uT` of the
  equality transport, specifying each of its three components as that transport.
  Its existence is a conclusion, not an additional exactness hypothesis on the
  identity transition. The composition equation uses `mapTriangleIso a` and
  `mapTriangleCompIso`. Thus it compares actual triangle morphisms with their
  specified shift structures, rather than only their first two components.
- H^r is the existing `truncGELE r r ⋙ shiftFunctor _ r`, i.e. τ≥r τ≤r followed by
  `[r]`. The single-functor theorem asserts heart membership of H_i^r K, T H_i^r K,
  and H_j^r T K. The actual natural isomorphism is the already defined
  `truncationCohomologyComparison`, not an arbitrary isomorphism or a per-degree map.
- The formula block spells out its construction: first σ at the double truncation,
  then the r-shift of c-plus at τ≤r K followed by τ≥r applied to c-minus. This is
  exactly the formula in proof step 5 and gives the required shifted heart object.
- The last two system conjunctions give respectively the h system equation and
  `h_{i/i}=1`, again transported through the literal identity equality.
- The transformation clause of the single-functor theorem gives the c-minus and
  c-plus squares and the h square. It also supplies a lift `ηT` on triangle
  categories with the three components η at the corresponding vertices, and an
  equality of whole triangle natural transformations intertwining e_F and e_G.
  Thus compatibility with exact transformations includes the boundary square.
  The quantified e_G is required to have exactly the same normalized components;
  its existence follows from the same single-functor assertion applied to G.
- The single-functor and transformation theorem is stated independently of any poset.
  For two composable functors, the system assertion specializes to a three-element
  chain with its canonical composite, identities, and associators. It therefore
  includes the single-functor identity and composition assertions as well.

Dependency declarations read and used:

- `def-weil-triangulated-category`: Mathlib's `Pretriangulated`, `IsTriangulated`,
  `Functor.CommShift`, and `Functor.IsTriangulated` with the recorded ambient structures.
- `def-weil-t-structure`: `TStructure`, `bounded`, `heart`, `truncLT`, `truncGE`,
  `truncGEδLT`, `triangleLTGE`, and their canonical cutoff transformations in
  `Mathlib.CategoryTheory.Triangulated.TStructure.{Basic,Heart,TruncLTGE}`.
- `lem-pod-texact-truncation-comparison`:
  `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`,
  `CategoryTheory.Triangulated.TStructure.texact_truncation_comparison`, with its
  normalization, uniqueness, naturality, identity and composition clauses read.
  Its public upstream import supplies the actual `Functor.IsTExact`,
  `Functor.eTruncLTIso` and `Functor.eTruncGEIso` constructions.
- `lem-weil-heart-short-exact-triangles`:
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`,
  `TStructure.homology₀`, and the publicly imported `ShortExact` truncation/adjunction
  infrastructure. The heart and double-truncation conventions were read directly.
- Definition dependency `def-per-truncation-cohomology-comparison` and retained proof
  dependency `lem-a1-cohomology-comparison-pasting`:
  `Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting`,
  `truncationCohomologyComparison` and its formula, naturality, composition, identity,
  and pasting declarations. The module is publicly imported because its definition
  appears in the signatures. It already imports the normalized comparison module.
- The proof dependency `lem-pod-texact-truncation-triangle-comparison` has no Lean
  record on the read base; no nonexistent module is imported. The existing upstream
  `Functor.eTruncGEδLT_comm` in
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`
  was read and already states the required boundary equation. Thus no private copy
  of its construction or new helper definition is needed in this delivery.

Edge cases checked before and after writing: a singleton directed poset (only identity
comparisons), repeated indices in a composable triple, zero categories/objects, equal
cutoffs n=m, arbitrary negative integers, and cutoffs outside an object's cohomological
range. The distinguished triangles and normalized isomorphisms make sense in every
case. For K=A[-r] in a bounded derived category with A in the heart, the double
truncation is A[-r], and the final `[r]` yields A; omitting that shift would be wrong.
The category and morphism universes are separate, and the index has its own bound.
No hypothesis of finite indexing, uniform boundedness, or invertible η was introduced.

Searches actually run:

- msearch leanfinder: `Normalized t-exact truncation triangle and shifted heart
  cohomology comparisons respect system associators, cutoff changes and exact natural
  transformations` returned 8 hits, including `truncGEδLT` and homological-functor
  composition lemmas, none stating this system coherence.
- msearch loogle: `CategoryTheory.Triangulated.TStructure.triangleLTGE,
  CategoryTheory.Functor.CommShift` returned 0 hits.
- msearch grep: `truncLTMap|truncGEMap|eTrunc|[Cc]ohomology.*[Cc]omparison` in
  CategoryTheory/Triangulated returned 11 hits, primarily ETrunc and SpectralObject
  imports/definitions, no system assertion.
- msearch leansearch: `Canonical comparisons for exact t-exact functors commute with
  truncation triangles cutoff changes and shifted cohomology, coherently under
  associators` returned 8 hits including triangleLTGE and truncLT, no exact match.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for eTrunc, t-exact comparisons,
  cohomology comparison/pasting and system-triangle coherence found the normalized
  upstream primitives and the landed cohomology module used above. The exact item-id
  search in WeilConjectures had no match. Searches for both proposed theorem names
  across Mathlib, WeilConjectures and Sheaf had no match.

Validation: scompile.py checked the delivered file separately both as a sandbox module
and at its library module path: both clean (7.9 s and 3.5 s on the final run).
The first probe caught an unqualified `Triangle`; opening `Pretriangulated` fixed it.
A final semantic reading removed an explicit unit-shift hypothesis: the existing unit
laws imply it, and the triangle lift of the identity is now asserted as a conclusion.
`set_option autoImplicit false` enforces that all variables are bound. Every declaration
has its source/blueprint docstring, and every postponed proof belongs to this DAG node.

## New nodes

`def-per-truncation-cohomology-comparison` owns the canonical natural isomorphism
`CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison`, already defined
in `Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting`, line 85. Its statement
is precisely the h^r formula from BBD 1.3.3/1.3.6: first commute F with [r], then
shift c-plus at tau-less-equal-r K, then shift tau-greater-equal-r of c-minus.
The declaration is a direct composite of associators and the specified isomorphisms,
not a choice from an existence theorem. This needs no new module or proof.
The definition itself works without boundedness, as do its actual truncation
adjunctions; the consumer retains all its boundedness hypotheses. The declaration's
section variables bind the source/target categories, t-structures, exact functor,
shift comparison, and t-exactness; its explicit j parameter is the integer r.
The signature in lean.statement is copied verbatim from the existing declaration.

The new searches on 2026-10-24 are recorded in its mathlib_searches: LeanSearch
returned eight generic truncation/triangulated-functor hits; Loogle returned zero
(unknown identifier truncationCohomologyComparison); Mathlib grep returned zero.
Direct source search found no upstream definition and found the landed Sheaf
composite. DAG inspection found its record only on the theorem node, with no
definition node owning it; blueprint_refs.py search returned five unrelated nodes.
Thus this delivery records the existing definition without duplicating it.
For r=0, the shift comparison is the specified zero-shift comparison; for negative r
and zero K all factors remain the same canonical natural isomorphisms. The singleton
system and repeated-index cases of the consumer are unchanged.

## Returned delivery repair

The return on immutable head 545686af277e identified H2: a theorem in stmt_deps
was being used only to import a plain definition. The new definition node resolves
that ownership defect, replaces that theorem in stmt_deps, and leaves it in
proof_deps for the identity/composition/naturality proof steps. The Lean module
and the item's mathematical statement are unchanged. The saved packet first
passed the required dry run at 64c16478b86; that mechanical pass did not resolve H2.
No unchanged re-push is used: the repaired packet contains the new node and report
and statement-dependency changes.

Repair validation: the repaired module and existing-declaration #check compiled
on the server. The first repaired preflight required the current schema's
`import_flags` field on the new node; it is supplied as an empty list.
Self-check confirmed that the item's statement and proof dependencies are unchanged,
that the theorem remains only a proof dependency, and that the new definition node's
Lean signature is copied verbatim from the existing explicit construction.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
