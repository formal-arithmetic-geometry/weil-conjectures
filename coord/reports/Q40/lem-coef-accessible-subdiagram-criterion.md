## Worker report

The module `Sheaf.CategoryTheory.AccessibleSubdiagramCriterion` states
`CategoryTheory.accessible_subdiagram_criterion`, with `sorry` as its only proof.
It states both the equivalence and the fixed-rank moreover clause. It introduces
no definitions or extra nodes and changes only the item's `lean` field.

The previous attempt confused the reviewed stage-1 split by N4 with completion
of stage 2. The current item has no Lean record. This delivery supplies that
record and its statement module; it does not resplit the node or change its
review, proof, dependencies, source, or natural-language statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed small universe is `v`: cardinals are `Cardinal.{v}`, small indexing
  categories and posets have type `Type v`, and the generating set is
  `ObjectProperty.Small.{v} D`. The ambient category has unrestricted object
  universe `u` and small Hom types via `{A : Type u} [Category.{v} A]`.
- Local presentability is `[IsLocallyPresentable.{v} A]`. Its definition is
  existence of an infinite regular rank at which A is cocomplete and generated
  by a small family of presentables under small cardinal-filtered colimits.
- The infinite regular cardinal sigma is `(σ : Cardinal.{v}) [Fact σ.IsRegular]`.
  Mathlib's `Cardinal.IsRegular` includes infinitude as its `aleph0_le` field.
- The full subcategory is `B : ObjectProperty A`, whose associated
  `B.FullSubcategory` retains all ambient morphisms. Repleteness is precisely
  `[B.IsClosedUnderIsomorphisms]`.
- Closure under ambient small sigma-filtered colimits is `hclosed`, quantified
  over `K : Type v`, `SmallCategory K`, `IsCardinalFiltered K σ`, and `F : K ⥤ A`.
  If all `F.obj k` satisfy B and `c` is a colimit cocone, it asserts `B c.pt`.
- Clause (i) is the existential `D : ObjectProperty A` with
  `ObjectProperty.Small.{v} D`, `D ≤ B`, and, for every `Y` satisfying B, a small
  sigma-filtered shape K with `D.colimitsOfShape K Y`. The latter is the
  existence of a colimit presentation with vertex Y and every diagram object
  in D. There is deliberately no presentability condition on D.
- Clause (ii) starts `∃ (bound : Cardinal.{v}), ∀ (τ : Cardinal.{v})` with an
  explicit regularity instance and `bound < τ`. The single bound precedes all
  choices of I, X, c and S. Strict versus non-strict eventual bounds makes no
  difference to the stated sufficiently-large quantifier.
- The source's relation sigma << tau is written without a new definition:
  `σ < τ` and `∀ (a b : Cardinal.{v}), a < τ → b < σ → a ^ b < τ`.
  This is the exact powers condition in the node, not an assumption of
  Mathlib's alternative cofinal-subsets formulation of `Cardinal.SharplyLT`.
- Each test is over `I : Type v`, its `PartialOrder I`, and
  `IsCardinalFiltered I τ`, with `X : I ⥤ A`. The canonical category instance
  on a poset is used. Presentability of every stage is
  `∀ i, IsCardinalPresentable (X.obj i) τ`.
- The ambient colimit belonging to B is `Nonempty (IsColimit c) → B c.pt → ...`
  for each `c : Cocone X`. This is equivalent to using the chosen colimit of X:
  local presentability supplies small colimits, all colimit vertices are
  isomorphic, and B is replete. No colimit or comparison map is postulated.
- The prescribed subset and its size are `S : Set I` and `Cardinal.mk S < τ`.
  The output `J : Set I` satisfies all four required conditions: `S ⊆ J`,
  `Cardinal.mk J < τ`, `IsCardinalFiltered J σ`, and a colimit in B.
- J has its inherited subtype order. The restricted diagram is exactly
  `(OrderHom.Subtype.val J).toFunctor ⋙ X`, so both objects and transition
  morphisms are restricted along the actual inclusion J into I. Its colimit
  is expressed by a cocone d with `Nonempty (IsColimit d) ∧ B d.pt`.
- The moreover clause is the second conjunct of the theorem. It quantifies
  over any particular infinite regular tau with the same sharpness conditions,
  assumes `IsCardinalLocallyPresentable A τ`, and assumes the same test property
  at that tau, without requiring approximation at other ranks.
- The objects specified by the moreover clause are exactly
  `B ⊓ isCardinalPresentable A τ`. Their smallness up to isomorphism is
  `ObjectProperty.EssentiallySmall.{v}` of that property. Generation is the
  following universal assertion that every Y in B has a small tau-filtered
  `colimitsOfShape` presentation in that same property. Essential smallness
  lets one replace diagram objects by a small set of isomorphism representatives,
  conjugating transition maps. Thus this states generation by a small family
  of ambient tau-presentables, without asserting sigma-presentability or
  presentability only inside B.

Dependency declarations and imports:

- `def-weil-pbc-category-colimit`: the recorded
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  with `Cocone` and `IsColimit`. I read the declaration and docstring, including
  the generated colimit declaration from `to_dual`. The statement uses its
  cocone universal-property interface `Cocone`/`IsColimit` directly.
- `Mathlib.CategoryTheory.Presentable.LocallyPresentable` supplies
  `IsLocallyPresentable` and `IsCardinalLocallyPresentable`, and transitively
  `IsCardinalPresentable`, `IsCardinalFiltered`, `ObjectProperty.Small`,
  `ObjectProperty.EssentiallySmall`, `ObjectProperty.colimitsOfShape`, and
  `ObjectProperty.IsClosedUnderIsomorphisms`. Their definitions and docstrings
  were read; none imposes presentability on the clause-(i) generating family.
- `Mathlib.CategoryTheory.Category.Preorder` supplies `Preorder.smallCategory`
  and `OrderHom.toFunctor`; `OrderHom.Subtype.val` is the actual inclusion.
- Proof-only imports cover the stated Mathlib proof dependencies:
  `Mathlib.CategoryTheory.Presentable.SharplyLT.Basic`,
  `Cardinal.SharplyLT.exists_isCardinalFiltered_set_of_exists_cofinal`;
  `Mathlib.CategoryTheory.Presentable.Directed`,
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`; and
  `Mathlib.CategoryTheory.Limits.Final`,
  `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`.
  The ambient presentables-small and small-colimit-presentable results are
  already imported transitively through `LocallyPresentable` and
  `CardinalFilteredPresentation`/`Limits`.
- The nodes `lem-coef-accessible-functor-presentability-ranks` and
  `lem-coef-presentable-presentation-comparison` have no recorded Lean modules
  to import. They are proof dependencies only, not prerequisites for typing
  this statement, and remain named in its complete proof docstring.

Edge cases checked before writing:

- Empty B is allowed: take empty D. Closure and both generation assertions
  are vacuous, and no test colimit belongs to B. No inhabitant of B is required.
- B equal to all of A is allowed. The criterion reduces to the ordinary
  presentability rank argument and enlargement of small subsets.
- S may be empty. J must nevertheless be sigma-filtered and hence nonempty;
  no artificial `Nonempty S` or nonempty generator hypothesis is imposed.
- An empty indexing poset I is excluded by cardinal-filteredness itself,
  as required by the cocone condition for the empty diagram. Empty generating
  sets remain possible exactly when B is empty.
- Sigma equal to aleph0 is included. Tau is strictly larger than sigma as
  the node requests. Finite cardinals are excluded only by `IsRegular`,
  which is exactly the node's infinite regular convention.
- A terminal test poset, an already small test diagram, zero objects in an
  additive ambient category, and repeated isomorphic generators impose no
  additional assumptions. Repleteness makes the choice of colimit irrelevant.
- The small universe `v` is used consistently for ranks, subsets, generators
  and diagrams; the ambient object universe stays independent.

Searches for an existing statement (2026-10-16 UTC):

- `msearch.py ... leanfinder`: query "A replete full subcategory of a locally
  presentable category is set generated under filtered colimits if and only
  if large filtered diagrams admit small subdiagrams in the subcategory".
  Eight hits: presentable-object instances, filtered-generator lemmas, and
  `MorphismProperty.isLocallyPresentable_isLocal`. None states this arbitrary
  full-subcategory criterion or its fixed-rank moreover clause.
- `msearch.py ... loogle`: query `"IsCardinalFiltered", "IsCardinalPresentable"`.
  Four hits concerning cardinal-filtered generators and comma categories;
  no match. Those generators require presentability and would strengthen (i).
- `msearch.py ... grep`: query
  `accessible.*subcategory|subcategory.*accessible|subdiagram` in
  `CategoryTheory/Presentable`. Only a descriptive line in `Dense.lean` matched.
- `rg` of `WeilConjectures/` and `lean/Sheaf` for the node id, the candidate
  declaration name, and `accessible.*subdiagram|subdiagram.*criterion` found
  no statement; only explanatory references in `AccessibleArrowInverseImage`.
  Related searches found the Mathlib presentability and object-property
  interfaces used above. No existing criterion was copied or redefined.

Source check: opened the cited HTT PDF online and read Definitions A.2.6.2--3,
Proposition A.2.6.5 and its proof on PDF pages 835--837. Its criterion and the
fixed-rank argument agree with the node. No statement correction or dispute.
The prose proof in the module follows all seven existing node steps.

Validation: the prescribed `scompile.py` compiled the module both as sandbox
source and at its library module path in approximately one second each,
with no errors or warnings. Every universe and variable is explicitly bound.
The node's Lean signature is copied verbatim from the file.


## Second reading by Q40

Independent second reader, 2026-10-17. I opened the repository node, the sandbox
node and Lean module, and the actual Mathlib declarations used by the statement.
The source is HTT rather than Stacks: I independently opened
[HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), PDF pages 835--837
(zero-based), and read Definitions A.2.6.2--3, Proposition A.2.6.5, Lemma A.2.6.6,
and the proof of the proposition. The appendix concerns ordinary categories.
The definition requires closure and a small generating family; it does not
require those generators to be sigma-presentable. The first proof paragraph
establishes the fixed-rank conclusion used in the node. No additional ambient
hypothesis is omitted. The node's explicit repleteness and strict inequality
sigma < tau are retained. No source-based correction is needed.

My inventory of the node, matched item by item to the Lean:

1. A fixed small universe, small Hom sets, and an unrestricted ambient object
   universe: `universe v u`, `{A : Type u} [Category.{v} A]`; all small categories,
   ranks, subsets, and generating families are relative to `v`. Verdict: exact;
   there is no equality restriction between `u` and `v`.
2. A locally presentable ordinary category A:
   `[IsLocallyPresentable.{v} A]`. I read `LocallyPresentable.lean:41,80--83` and
   its generator superclass in `CardinalFilteredPresentation.lean`. It means
   cocompleteness for small diagrams and generation at some infinite regular
   cardinal, as required. Verdict: exact.
3. An infinite regular sigma: `(σ : Cardinal.{v}) [Fact σ.IsRegular]`.
   `Cardinal.IsRegular` has the infinitude field `aleph0_le` and the cofinality
   condition equivalent to the node's union condition. Verdict: exact.
4. A replete full subcategory B: `(B : ObjectProperty A)` and
   `[B.IsClosedUnderIsomorphisms]`. An object predicate specifies the full
   subcategory with inherited Hom sets; the class is closure under ambient
   isomorphisms. Verdict: exact, without any unrelated category structure.
5. Closure under small sigma-filtered colimits in A: `hclosed` quantifies over
   every `K : Type v`, `SmallCategory K`, `IsCardinalFiltered K σ`, ambient
   functor F and cocone c, and takes `(∀ k, B (F.obj k))` and
   `Nonempty (IsColimit c)` to `B c.pt`. Verdict: exact, including the universal
   property and computation in A.
6. Clause (i), a small set of objects of B:
   `∃ D : ObjectProperty A, ObjectProperty.Small.{v} D ∧ D ≤ B ∧ ...`.
   `ObjectProperty.Small` is smallness of the actual subtype of objects, rather
   than an extra presentability condition. Verdict: exact.
7. Clause (i), generation under small sigma-filtered ambient colimits: for
   every `Y : A` with `B Y`, there is a small sigma-filtered K and
   `D.colimitsOfShape K Y`. I read `ObjectProperty/ColimitsOfShape.lean:82--84,
   133--137`: this is `Nonempty (D.ColimitOfShape K Y)`, a diagram in A with
   every object in D and a colimit cocone having vertex Y. Verdict: exact.
8. Equivalence: the first parenthesized expression is an `↔` between precisely
   this generating-family assertion and the approximation assertion.
   Verdict: both directions, with no missing clause.
9. The uniform eventual bound in (ii): `∃ bound : Cardinal.{v}, ∀ τ, ...`;
   `bound < τ` is imposed before any I, X, c, or S is chosen. Verdict: exact;
   an eventual strict bound is equivalent to a non-strict one after increasing
   the bound.
10. Every admissible infinite regular tau with sigma << tau:
    `(_ : Fact τ.IsRegular)`, `σ < τ`, and
    `∀ a b : Cardinal.{v}, a < τ → b < σ → a ^ b < τ`. Verdict: the node's exact
    powers condition, without substituting a different sharpness definition.
11. Each test diagram: `I : Type v`, `PartialOrder I`,
    `IsCardinalFiltered I τ`, `X : I ⥤ A`, and
    `∀ i, IsCardinalPresentable (X.obj i) τ`. I read the cardinal-filtered
    cocone definition and the presentability definition through the coyoneda
    functor. Verdict: small tau-filtered posets and ambient tau-presentable
    stages, with no finiteness, inhabited-subset, or extra rank assumption.
12. The ambient colimit belongs to B: for each `c : Cocone X`, the hypotheses
    are `Nonempty (IsColimit c)` and `B c.pt`. Verdict: equivalent to the
    chosen-colimit formulation; existence follows from local presentability
    and all colimit vertices are isomorphic, with membership invariant by
    repleteness. Quantification over cocones adds no mathematical hypothesis.
13. Every prescribed tau-small subset: `∀ S : Set I, Cardinal.mk S < τ → ...`.
    Verdict: exact and in the correct order after the diagram and its colimit.
14. The output subposet contains S and has the stated size and filteredness:
    `∃ J : Set I, S ⊆ J ∧ Cardinal.mk J < τ ∧ IsCardinalFiltered J σ ∧ ...`.
    Verdict: all three clauses, with the inherited subtype order on J.
15. The restricted colimit is in B: an actual cocone d on
    `(OrderHom.Subtype.val J).toFunctor ⋙ X` with
    `Nonempty (IsColimit d) ∧ B d.pt`. Verdict: restriction of both objects and
    arrows along the real inclusion, with the required ambient colimit.
16. The moreover assertion applies at a single particular regular tau:
    the second conjunct quantifies tau with the same rank inequalities,
    assumes `IsCardinalLocallyPresentable A τ`, and assumes the same
    approximation test only at that tau. Verdict: it does not incorrectly
    require eventual approximation for this conclusion.
17. Its generating objects are exactly the objects of B tau-presentable in A:
    `B ⊓ isCardinalPresentable A τ`. Verdict: ambient presentability, not
    sigma-presentability or presentability internal to B.
18. Its two conclusions are smallness up to isomorphism,
    `ObjectProperty.EssentiallySmall.{v} (B ⊓ isCardinalPresentable A τ)`, and
    a small tau-filtered `colimitsOfShape` presentation in that property for
    every Y in B. I read `ObjectProperty/Small.lean`, including
    `EssentiallySmall.exists_small_le`. Representatives can be chosen inside
    this property and diagram arrows conjugated by their isomorphisms.
    Verdict: exactly a small family up to isomorphism generating B under the
    stated ambient colimits, rather than merely a smallness conclusion.

Dependency review: the only statement dependency is
`def-weil-pbc-category-colimit`; I opened its JSON record and read the recorded
`Mathlib.CategoryTheory.Limits.HasLimits` chosen-colimit definition and the
`Cocone`/`IsColimit` interfaces it records. They are imported transitively by
`LocallyPresentable`, and directly used in the signature. I also read the
proof-support signatures `exists_isCardinalFiltered_set_of_exists_cofinal`,
`exists_cardinal_directed`, `isColimitWhiskerEquiv`,
`isCardinalPresentable_of_isColimit`, and the essentially-small-presentables
instance, checking the surrounding regularity, local-smallness and universe
parameters. The existing imports supply the four Mathlib proof leaves.
The two proof dependencies without Lean records do not supply any missing
notion needed to type the statement. No new nodes or dependency modules are
included, so H12/H13 do not require additional node repairs.

Edge cases: B may be empty (the empty generating property works), or all of A;
no inhabitant is assumed for B or D. S may be empty. I and J are nonempty as a
consequence of cardinal-filteredness (the empty diagram must have a cocone),
not a stronger separately added assumption. Sigma = aleph0 is included;
finite ranks are excluded exactly by infinite regularity. A zero object, when
A happens to have one, satisfies no extra restriction. A terminal indexing
poset and repeated isomorphic stages are allowed. There is no scheme,
characteristic, or numeric-degree parameter to restrict; empty schemes as
ambient-category objects have no exceptional treatment. Object universe u
remains independent of v; small diagrams and all cardinal bounds consistently
use v. These match every relevant edge case of the node.

Independent duplicate searches, logged by msearch.py on 2026-10-17:

- LeanFinder: `Set generation by filtered colimits characterized by finding
  small directed subposets whose colimits lie in a replete class of objects`.
  Eight hits; I inspected the nearest `ObjectProperty.ind` and
  `IsCardinalFilteredGenerator.exists_colimitsOfShape` interfaces. They concern
  ordinary filtered closure or generators required to be presentable, and
  do not state the equivalence and fixed-rank conclusion here.
- Loogle: `"ObjectProperty", "IsCardinalFiltered"`. Twelve hits, all the
  cardinal-filtered-generator API; its `le_isCardinalPresentable` field is
  stronger than the node's clause (i). No matching criterion.
- LeanSearch: `For a subcategory stable under filtered colimits, a small
  generating family exists precisely when sufficiently large directed
  presentations can be approximated by small subdiagrams in that subcategory`.
  Eight hits, local-presentability and cardinal-filtered-generator structures
  and constructors, not this theorem.
- `rg -n -i 'small.*subdiagram|subposet|set.?generat|presentable.*subset|subset.*presentable'`
  across Mathlib's `CategoryTheory/Presentable`, upstream `WeilConjectures`,
  and the repository's `lean/Sheaf`; a second search used
  `accessible.?subdiagram|subdiagram.?criterion|accessible.*subcategory`.
  No duplicate. `AccessibleArrowInverseImage.lean` only cites this criterion
  in its proof plan. The exact declaration name also has no upstream-name
  table hit. Existing Mathlib definitions are reused throughout.

H5/H6/H8/H9 review: the delivery has one theorem with only `sorry` as its proof,
no new definitions or instances, no private notation, no `let` or hidden
`show ... from` in its statement, and no unbound universe or variable. The
module and theorem docstrings carry the correct source and blueprint id. I
matched all seven prose proof steps to the node: subset enlargement, cocone
assembly, fixed-rank generation, choice of a permissible rank, uniform
presentability bound, the second presentation, and presentation comparison
followed by closure/repleteness. Lines are at most 100 characters. The
sandbox node differs from the current repository node only in `lean`, and
`lean.statement` equals the file's signature verbatim.

Mismatches and changes: none found in the mathematical statement, dependency
interfaces, node record or module. I left the correct Lean and node unchanged
and added this second-reading report. There is no statement correction, no
new node, and no dependency module.

Independent validation: `scompile.py Q40 lem-coef-accessible-subdiagram-criterion`
compiled the delivered module in both its sandbox and library paths, in
0.9 s and 1.0 s respectively, with exit status 0, no errors and no warnings.
