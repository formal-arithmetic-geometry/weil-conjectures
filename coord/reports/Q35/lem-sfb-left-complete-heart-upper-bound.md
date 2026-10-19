## Worker report

The module `Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound` states
`DerivedCategory.upperBound_of_heart_of_leftComplete`. Its sole theorem has proof
`sorry`; it introduces no definition, no axiom, and no other DAG statement.
The theorem docstring supplies the finite-window induction, Roos argument and
eventual-isomorphism argument needed for a future proof. The node's statement and
all fields other than `lean` are unchanged.

Hypotheses and conclusion, clause by clause:

- The abelian categories are `(A : Type uA) [Category.{vA} A] [Abelian A]` and
  `(B : Type uB) [Category.{vB} B] [Abelian B]`. All six universe parameters are
  explicit and independent. Their unbounded derived categories use the recorded
  `DerivedCategory` with `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]`. Cohomology is `homologyFunctor A i` or
  `homologyFunctor B j`, with integer degrees.
- Existence and exactness of countable products in each abelian category are
  `[HasCountableProducts A] [CountableAB4Star A]` and the corresponding B binders.
  Mathlib's `CountableAB4Star` says that limits over countable discrete categories
  preserve finite colimits. In an abelian category, product functors already
  preserve finite limits, so this is exactly preservation of short exact
  sequences, as specified in the node. It imposes neither arbitrary products
  nor exactness for uncountable products.
- Left completeness is `hcomplete`, quantified over every `K : DerivedCategory A`.
  Its tower has terms `(TStructure.t.truncGE (-(n : ℤ))).obj K` for `n : ℕ`.
  Its transitions are the canonical `TStructure.t.natTransTruncGEOfLE`
  from cutoff `-((n+1 : ℕ) : ℤ)` to cutoff `-(n : ℤ)`; the only arithmetic proof
  is `by omega`. The first arrow of its Roos triangle is exactly
  `Pi.lift (fun n ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)`.
  Only the final arrow `δ` is existential. `IsDerivedLimitTriangle` specifies
  the distinguished triangle with middle arrow `1-s`; an arbitrary initial
  arrow or a bare `IsDerivedLimit` would not capture the canonical-map clause.
- Within `hcomplete`, `[HasProduct (fun n ↦ ...)]` is universally quantified,
  not an extra global hypothesis that derived products exist. It expresses
  the property independently of any product witness. Such witnesses exist
  under the stated exact-products hypotheses by Stacks 07KC, also recorded as
  `CategoryTheory.derivedCategory_hasCountableProducts` in
  `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsExistence`.
  Thus this formulation is not vacuous and adds no mathematical assumption.
- The functor is `(T : DerivedCategory A ⥤ DerivedCategory B)` with
  `[T.CommShift ℤ] [T.IsTriangulated]`. These encode its shift comparison and
  exactness; additivity follows from the latter. Countable product preservation,
  including the actual projections, is
  `[∀ (I : Type) [Countable I], PreservesLimitsOfShape (Discrete I) T]`.
  Preservation of a limiting fan means precisely that its images of the
  projections remain a limiting fan, not merely an abstract isomorphism of
  product objects. The universe-zero index suffices for countable sets by
  shrinking; no object or morphism universe of A or B is restricted.
- The class is an unrestricted `S : Set A`, with no closure properties, and the
  uniform bound is an arbitrary `c : ℤ`. The heart embedding `M[0]` is
  `(singleFunctor A 0).obj M`. The hypothesis `hheart` says for every `M ∈ S`
  and every integer `j` with `c < j` that
  `IsZero ((homologyFunctor B j).obj (T.obj ((singleFunctor A 0).obj M)))`.
- The conclusion applies to every `b : ℤ` and `K : DerivedCategory A`.
  `hS : ∀ i : ℤ, (homologyFunctor A i).obj K ∈ S` covers every degree;
  `hbound : ∀ i : ℤ, b < i → IsZero ((homologyFunctor A i).obj K)` gives the
  stated upper bound. The result is exactly vanishing for every `j : ℤ`
  with `b + c < j` of `H^j(TK)`.
- No lower bound for K, no lower bound for T, and no heart bound outside S
  occur in the signature. In particular S is not replaced by all objects.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (Mathlib leaf).
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` from `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  `DerivedCategory.homologyFunctor` from its `HomologySequence` module and
  `DerivedCategory.singleFunctor` from `Basic` (the cochain-complex
  degree embedding followed by Q).
- `def-kun-truncations`: publicly imports the recorded
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`. As its documentation
  specifies, good derived truncations use `DerivedCategory.TStructure.t` and
  the existing t-structure APIs, not its new hocolimit predicate. Specifically
  `CategoryTheory.Triangulated.TStructure.truncGE`, `truncGEπ`, and
  `natTransTruncGEOfLE` are read in
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`.
- `def-weil-derived-limit`: `CategoryTheory.IsDerivedLimitTriangle` from its
  recorded `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`. Its
  full signature and definition were read, together with
  `towerTransitionEndomorphism` and `towerProductShift`, ensuring the sign is
  `1-s` and the projections have the stated transition components.
- `def-weil-triangulated-category`: `CategoryTheory.Functor.IsTriangulated` and
  `Functor.CommShift`, using `Mathlib.CategoryTheory.Triangulated.Functor`.
- `def-weil-category-product`: `HasCountableProducts`, `piObj`, `Pi.π`, `Pi.lift`
  and the product-preservation APIs from Mathlib's `Limits.Shapes.Countable`,
  `Limits.Shapes.Products` and `Limits.Preserves.Shapes.Products`.
  `CountableAB4Star` is reused from
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`, already publicly
  available through the recorded truncation module.

Sources read: `literature/stacks-project/derived.tex`, the definitions and
remarks at labels `section-derived-limit`, `definition-derived-limit`,
`lemma-products`, and `remark-map-into-derived-limit-truncations`; and the
current blueprint main-20261015 proof of
`det-prop-int-compactness-direct-sums`, paragraph (2). The latter is the
class-relative uniform-bound application; this node is an agent lemma rather
than a direct quotation of Stacks.

Edge cases checked mathematically before writing:

- For T equal to the identity, c=0 gives the original upper bound. For T=[r],
  c=-r gives b-r, confirming the cohomological shift sign.
- T=0, K=0, a single cohomological degree, and an infinite negative tail all
  give the expected conclusion. The tower starts at n=0, as in 0H72; omitting
  or adding a finite initial segment does not change the derived limit.
- Negative b and c are allowed without any natural-number coercion on them.
  If -n>b, that finite truncation is zero; the finite-window argument starts
  there without assuming K is bounded below.
- S may be empty, contain only zero objects, omit the chosen zero object,
  or fail to be closed under isomorphisms or extensions. No closure is used:
  the layers are isomorphic to the specified cohomology objects of K and T
  transports these isomorphisms. If S is empty there is no K satisfying hS.
- Product preservation covers all countable index sets, including the empty
  and finite ones. Left completeness quantifies over all K and any product
  witness and fixes the canonical first arrow.
- The possible lim^1 contribution in degree b+c+1 is not ignored. The
  eventual-isomorphism argument in the docstring removes it, so the result
  is b+c rather than b+c+1, without a lower amplitude bound.

Searches (all made for Q35 and this item; exact tool outputs are in the
sandbox's `searches.jsonl`):

- `msearch.py leanfinder`, query: "A triangulated functor preserving countable
  products extends a class relative upper cohomological bound on heart objects
  to bounded above complexes using left completeness". Eight hits, including
  `DerivedCategory.IsLE`, `IsGE`, bounded-representative lemmas and t-structure
  support declarations. Read the relevant signatures; none is the statement.
- `msearch.py loogle`, query:
  `DerivedCategory.IsLE, CategoryTheory.Functor.IsTriangulated`. Zero hits.
- `msearch.py grep`, query:
  `leftComplete|LeftComplete|left_complete|heart.*upper`. Zero Mathlib hits.
- `msearch.py leansearch`, query: "A triangulated functor preserving countable
  products extends an upper bound from a class of heart objects to bounded
  above complexes in a left complete derived category". Eight hits, defining
  triangulated functors, mapping distinguished triangles, induced exact
  functors, or binary product preservation. None gives this bound.
- `rg` of the upstream `WeilConjectures` tree, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `upperBound_of_heart_of_leftComplete`,
  `leftComplete|LeftComplete|left_complete|heart.*upper`; and an upstream
  search for the exact item id. No duplicate theorem. The side theorem
  `AlgebraicGeometry.Scheme.ProEt.left_complete_quasiIso` is about the
  canonical strict truncation-limit comparison for pro-etale module
  complexes, not the upper bound for an arbitrary triangulated functor.
  The upstream `Pretriangulated.IsHomotopyLimit.map` transports a Roos cone
  through a product-preserving functor but has no heart or cohomology bound.

Validation: the delivered file compiles cleanly through `scompile.py`, both
sandbox elaboration and its intended module path. No warning or error remains.
All variables/universes are explicitly bound; no file-local notation, private
notion, or local instance is used. The only postponed declaration is the named
theorem above. No statement correction, new node, or dependency repair is needed.

The current node has seven proof steps. All stated proof-dependency modules are
imported without `public`: `Sheaf.Algebra.Homology.LowerTruncationStepTriangle`,
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit`,
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`Mathlib.CategoryTheory.Shift.ShiftSequence`, and
`Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`. Their recorded
declarations are respectively `DerivedCategory.exists_lowerTruncationStepTriangle`,
`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`,
`DerivedCategory.HomologySequence.exact₁`/`exact₂`/`exact₃`,
`CategoryTheory.Functor.shiftIso`, and
`CategoryTheory.derivedCategory_countableProducts_core`. The docstring follows
these seven steps and spells out the finite-component splitting of `1-s`.

## Second reading by Q35

I independently read the sandbox node, its Lean module, all six statement
dependency nodes and their recorded interfaces. I read derived.tex at
section-derived-limit (08TB), definition-derived-limit (08TC), lemma-products
(07KC), and remark-map-into-derived-limit-truncations (0H72), together with
the blueprint proof of det-prop-int-compactness-direct-sums, paragraph (2).
The class-relative assertion is explicitly an agent lemma extracted from that
application; it is not falsely presented as a theorem quoted from Stacks.
There is no statement_change, new node, or dependency module in this delivery.
There is no repair-notes record for this item in the shared checkout.

My object/hypothesis/conclusion checklist, in the order of the node:

1. Two arbitrary abelian categories: `(A : Type uA) [Category.{vA} A]
   [Abelian A]` and the corresponding B binders. Verdict: exact; no module,
   sheaf, coefficient-ring, finiteness, or enough-injectives specialization.
2. Their unbounded derived categories and integer cohomology:
   `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`,
   `DerivedCategory A/B`, and `homologyFunctor A/B i`. Verdict: exact.
   I opened Mathlib DerivedCategory.Basic and HomologySequence: these are
   localization at quasi-isomorphisms and the induced cochain cohomology,
   not bounded derived categories or homology with a different grading.
3. Existence and exactness of countable products in A and B:
   `[HasCountableProducts A] [CountableAB4Star A]`, and similarly B.
   Verdict: exact. In GrothendieckAxioms.Basic, CountableAB4Star requires
   HasExactLimitsOfShape for countable discrete diagrams, i.e. preservation
   of finite colimits by the product functor. That functor already preserves
   finite limits, so in abelian categories this is precisely exactness on
   short exact sequences. Arbitrary uncountable products are not assumed.
4. Standard good lower truncations and the actual tower transitions:
   `(TStructure.t.truncGE (-(n : ℤ))).obj K` and
   `(TStructure.t.natTransTruncGEOfLE (-((n+1 : ℕ) : ℤ)) (-(n : ℤ))
   (by omega)).app K`. Verdict: exact. I opened the recorded composite
   truncation module and Mathlib TruncLTGE. The latter map goes from cutoff
   `-(n+1)` to cutoff `-n`; it is not the upper-truncation inclusion.
5. Left completeness for every K with its canonical maps:
   `hcomplete` universally quantifies K and a product witness, and requires
   an `IsDerivedLimitTriangle` whose first arrow is
   `Pi.lift (fun n ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)`.
   Only the connecting arrow δ is existential. Verdict: exact. I retrieved
   the current DerivedLimit and TowerTransitionEndomorphism sources using
   `scompile.py --source`; their definitions give exactly the distinguished
   triangle with middle map `1 - Pi.lift (fun n ↦ Pi.π _ (n+1) ≫ f n)`.
   Thus neither the sign nor the canonical-map condition is lost.
   Quantifying the product witness does not make the condition vacuous:
   Stacks 07KC, and the opened declaration
   `CategoryTheory.derivedCategory_hasCountableProducts`, supply that witness
   under hypothesis 3, for all the independently chosen universe parameters.
   Changing the chosen product transports δ along its unique projection
   compatible isomorphism, so this quantification adds no requirement.
6. Exact triangulated functor T with preservation of countable products:
   `(T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ]
   [T.IsTriangulated]` and
   `[∀ (I : Type) [Countable I], PreservesLimitsOfShape (Discrete I) T]`.
   Verdict: exact. I opened Functor.IsTriangulated and its Additive instance.
   Preservation of limits preserves the limiting fan with its projections,
   rather than merely furnishing unrelated isomorphic product objects.
7. An arbitrary class S of heart objects and an integer c:
   `(S : Set A) (c : ℤ)`. Its embedding is `(singleFunctor A 0).obj M`.
   Verdict: exact. Basic.lean defines this singleFunctor using the complex
   concentrated in that degree and the localization. There is no assumed
   closure of S under extensions, isomorphisms, or inclusion of zero.
8. The uniform heart bound is `hheart`, for every `M ∈ S` and integer
   `j > c`, asserting `IsZero` of degree j cohomology of T(M[0]).
   Verdict: exact; there is no bound on heart objects outside S.
9. For every integer b and every K, the conclusion assumes
   `hS : ∀ i : ℤ, (homologyFunctor A i).obj K ∈ S` and
   `hbound : ∀ i : ℤ, b < i → IsZero ((homologyFunctor A i).obj K)`.
   Verdict: exact, including all negative degrees in hS. The quantifier
   order permits every b and K after fixing T, S, and c.
10. The conclusion is, for every integer `j > b+c`,
    `IsZero ((homologyFunctor B j).obj (T.obj K))`. Verdict: exact b+c,
    without an extra degree, a lower bound on K, a lower amplitude bound
    on T, or an absolute cohomological-dimension hypothesis.

Edge cases: S can be empty (then no K satisfies hS), non-isomorphism-closed,
or contain only zero objects. K=0 is covered whenever its actual cohomology
objects satisfy hS, and T=0 is covered. Negative b,c and b=c=0 are allowed.
For T the identity and c=0 the conclusion recovers hbound; for T=[r],
c=-r gives b-r, checking the shift convention. The tower includes n=0
and has the correct transition from truncation -1 to truncation 0. For
negative b, some initial truncations are zero; no nonzero-term hypothesis
excludes them. Infinite negative cohomology tails are allowed. Empty and
finite countable products are included. Universe parameters uA,vA,wA and
uB,vB,wB remain independent: HasCountableProducts transports countable
index sets using `Shrink.{0}` (Countable.lean:63-66), and preservation of
countable products transports along the same discrete equivalences.
There is no scheme or characteristic in the assertion to restrict.

Independent searches, with different wording from the first reader:

- `msearch.py leanfinder`: "A product preserving exact functor is right t
  exact up to a uniform shift if it is bounded on a specified class in the
  heart and the source derived category is left complete". Eight hits:
  induced exact functors, commutation with shifts, homological functors,
  Ext maps and exact sequences. None states the class-relative bound.
- `msearch.py loogle`: `CategoryTheory.Functor.IsTriangulated,
  DerivedCategory.homologyFunctor`. No hits.
- `msearch.py leansearch`: "In left complete derived categories, an exact
  functor preserving countable products extends a uniform upper
  cohomological bound on a class of heart objects to bounded above objects
  with cohomology in that class". Eight hits concerning exact functors,
  mapDerivedCategory and CountableAB4; none is this statement.
- `msearch.py grep`: `upperBound_of_heart|heart.*upperBound|leftComplete|
  left_complete`. No Mathlib hits. Direct rg searches of upstream
  WeilConjectures, side lean/Sheaf, Mathlib homological algebra and
  triangulated-category sources used `heart.*bound|bound.*heart|
  complete.*upper|upper.*complete|cohomological.*amplitude|right.?t.?exact`.
  The nearby integral t-structure and exceptional-functor statements concern
  particular geometric functors and do not quantify arbitrary A,B,T,S.
  The upstream-name inventory has no duplicate declaration or item tag.
  HomotopyLimit.IsHomotopyLimit.map only transports a Roos cone; I opened
  its full signature and it contains neither this heart bound nor this
  conclusion. Existing canonical notions are all reused.

I also read the proof dependency interfaces, including the actual canonical
middle arrow in exists_lowerTruncationStepTriangle. The seven docstring steps
match the node: finite-window induction, eventual invertibility in each
cohomological degree, product-compatible Roos triangle, and a finite recursive
section of 1-s. In particular the possible degree b+c+1 contribution is
eliminated by the section, rather than silently assumed zero.

Mismatches found: none. I preserved the Lean module and node record unchanged
and added this independent review. The only theorem body is `sorry`; no data
definition, private notion, extra theorem, or file-local notation was added.
The module/declaration docstrings contain their source and blueprint id;
all lines meet 100 characters. A direct extraction confirms lean.statement
equals the source signature verbatim. All variables and six universes are
bound. The required scompile.py run passed both sandbox and intended module
compilation cleanly, in 1.7 seconds each, with no warnings or errors.
