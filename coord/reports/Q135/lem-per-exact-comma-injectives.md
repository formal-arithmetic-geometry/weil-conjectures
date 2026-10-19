## Worker report

The module `Sheaf.CategoryTheory.ExactCommaInjectives` states
`CategoryTheory.exactComma_injectives` with `sorry` and defines the graph functor
`CategoryTheory.exactCommaGraph` by actual objects and morphisms. Nothing is proved.
There are no new nodes, dependency repairs, or statement corrections. The graph is
part of this node's own explicit construction and is recorded in lean.declarations.
The item has no repair note in coord/repair-notes and no return in Q135's returns.
The earlier Q134 completion in deliveries.log is stage 1, not a Lean statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The two abelian categories are arbitrary `A : Type u₁`, `B : Type u₂` with
  `Category.{v₁} A`, `Category.{v₂} B`, `[Abelian A]`, `[Abelian B]`.
  All four universes and both categories are explicitly bound, independently.
- Enough injectives is `[EnoughInjectives A] [EnoughInjectives B]`: its presentation
  field supplies exactly a mono into an injective object for each object.
- The additive exact functor is `(L : A ⥤ B) [L.Additive]` together with
  `[PreservesFiniteLimits L] [PreservesFiniteColimits L]`. This is equivalent to
  preserving short exact sequences, exactly as the node specifies: the four-way
  `Functor.exact_tfae` in Mathlib.Algebra.Homology.ShortComplex.ExactFunctor,
  lines 220–226, equates its first and fourth entries for additive functors between
  abelian categories. This changes neither the hypothesis nor the conclusion.
- The additive right adjoint is `(R : B ⥤ A) [R.Additive] (adj : L ⊣ R)`.
  No exactness assumption on R is made.
- The triples are the existing `Comma L (𝟭 B)`. Its fields left/right/hom are
  precisely P/N/u : LP ⟶ N. `CommaMorphism.w` reads
  `L.map a ≫ u' = u ≫ b`, the node's commuting square in Lean composition order.
  Mathlib's commaCategory composes both components separately; its canonical
  instPreadditiveComma adds pairs separately. No second triple category is defined.
- Abelianness is `∃ h : Abelian (Comma L (𝟭 B)), ...`. The equality
  `h.toPreadditive = instPreadditiveComma L (𝟭 B)` specifies that this is the
  componentwise addition required in the node, rather than some unrelated addition.
  The right hand side explicitly names the pre-existing comma structure.
- Kernels and cokernels computed in both components are expressed by preservation
  of finite limits and colimits by *each* evaluation: a kernel is the limit of
  parallelPair f 0 and a cokernel the corresponding colimit. Both evaluations are
  already additive Mathlib instances, so they preserve zero maps. Thus their
  preservation sends every chosen kernel/cokernel cone to the component kernel/
  cokernel cone. This gives the specified computation up to its unique canonical
  isomorphism, independent of choices of limits. Conversely, the node's abelian
  structure and componentwise kernels/cokernels, with additive evaluations, give
  finite-limit/finite-colimit preservation; no extra computation is required.
- Enough injectives for triples is `EnoughInjectives (Comma L (𝟭 B))`.
- The two exact evaluations are exactly `Comma.fst L (𝟭 B)` and
  `Comma.snd L (𝟭 B)`, with both finite-(co)limit preservation conjuncts each.
  Their injective-preservation clauses are the respective
  `.PreservesInjectiveObjects` conjuncts, using Mathlib's existing injective notion.
- Delta is `exactCommaGraph L`: obj P is literally `(P, L.obj P, 𝟙 (L.obj P))`,
  and map a has left a and right L.map a. The last three conjuncts state
  `.Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` for that functor.

Dependency declarations read and used:

- def-sp-abelian: mathlib_match CategoryTheory.Abelian,
  Mathlib.CategoryTheory.Abelian.Basic, full class and docstring at lines 102–116.
  Its finite-products/normal-mono/normal-epi definition is the node's abelian notion.
- def-sp-injective-resolutions: recorded CategoryTheory.Injective,
  Mathlib.CategoryTheory.Preadditive.Injective.Basic, lines 28–33. The existing
  CategoryTheory.InjectiveResolution signature/docstring was also read in
  Mathlib.CategoryTheory.Preadditive.Injective.Resolution, lines 39–54; this item's
  statement uses the injective-object clause, not the resolution clause.
- def-sp-enough-injectives: mathlib_match CategoryTheory.EnoughInjectives in the
  same Basic module, lines 49–65 (InjectivePresentation and presentation).
- The two proof-tool leaves are imported without public: Mathlib's
  CategoryTheory.Adjunction.leftAdjoint_preservesColimits in
  Mathlib.CategoryTheory.Adjunction.Limits, and
  CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
  in Mathlib.CategoryTheory.Preadditive.Injective.Preserves (already public because
  its PreservesInjectiveObjects definition is part of the statement).
  The source signatures/docstrings at Limits lines 91–100 and Preserves lines 48–52
  were read. The entire nine-step proof from the node is retained in the theorem
  docstring, with each ingredient, its construction and its dependency named.

Source checked: literature/stacks-project/homology.tex, lemma-adjoint-preserve-injectives
(Tag 015Z), lines 7270 onward. It proves the adjoint/injective ingredient; the comma
calculation is the node's explicitly identified auxiliary construction, not claimed
as a verbatim Stacks theorem. The graph construction comes from the item itself.

Edge cases checked before writing: L = identity gives the arrow category and its
identity-arrow graph; L = zero gives the product category and graph `(P,0,0)`.
The zero object/triple is included. A trivial abelian category is allowed. No
nonzero, faithfulness, essential-surjectivity, boundedness, or exactness of R is
assumed. Empty finite diagrams are covered by finite-limit and finite-colimit
preservation (hence zero objects); there is no index-size restriction. Independent
object and hom universes on A and B remain independent. For a non-exact right
adjoint, the injective proof still uses only L exact and the adjunction. No disputed
statement was found.

Searches made using msearch.py (raw receipts are in sandbox searches.jsonl):

- LeanFinder: "An exact additive left adjoint between abelian categories has an
  abelian comma category with enough injectives and exact evaluation functors
  preserving injectives". Eight hits, including abelianOfAdjunction,
  EnoughInjectives.of_adjunction and Functor.exact_tfae. These are transfer criteria
  and the equivalence of exactness notions; none states the comma theorem.
- Loogle: `CategoryTheory.Comma, CategoryTheory.Abelian`: zero hits.
- LeanSearch: "Injective objects in a comma category of an exact left adjoint
  between abelian categories": eight hits, giving generic Injective, injective
  presentations, adjunction preservation and PreservesInjectiveObjects; no match.
- Mathlib grep: `Comma.*[Ii]njective|[Aa]belian.*Comma|Comma.*[Aa]belian` in
  CategoryTheory: zero hits.
- Mathlib grep: `def.*(graph|Graph|diagonal|Diagonal)|def.*⥤.*Comma` in
  CategoryTheory/Comma: six hits, generic comma maps and the Grothendieck functor;
  none is the graph functor with objects `(P,LP,id)`.
- Direct rg in upstream WeilConjectures and project lean/Sheaf for Comma/comma,
  graph and exactComma names, plus the item's blueprint id, found only unrelated
  comma site/limit/arrow constructions and no statement of this item. Also checked
  dag/lean_names_upstream.json for the proposed names: no collision. Read the full
  Mathlib Comma.Basic and Preadditive.Comma declarations rather than redefining
  those notions. Read Limits.Comma to check componentwise limit semantics.

Validation: scompile.py compiled the module cleanly in sandbox and library contexts
(about 2–3 seconds per invocation, the fixed 60-second limit). A separate temporary
sandbox probe imported the module and printed the full theorem: every category,
universe and hypothesis is present. The final delivery wrapper compiles again and
runs the server preflight. The only postponed proof is exactComma_injectives.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
