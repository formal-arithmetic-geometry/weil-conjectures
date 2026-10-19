## Worker report

The module `Sheaf.CategoryTheory.PresheafBoundedIntersectionReplacement` states
`CategoryTheory.Presheaf.exists_bounded_intersection_replacement`, with `sorry`
as its entire proof. No result is proved. Its docstring contains all fourteen
DAG proof steps, including their dependency references and the comparison of
total-element size with Cisinski's category-of-elements size.

Three helper definitions give the three expressions explicitly introduced in
the item's own statement: `totalCardinal`, `weaklySaturated`, and
`IsLambdaInjective`, all in namespace `CategoryTheory.Presheaf`. These are
helpers belonging to the owning node, recorded in `lean.declarations`, under
the human's missing-helper authorization. There are no independent new notions,
new nodes, dependency repairs, or changes to the natural-language statement.
All helpers have real data and source/blueprint docstrings.

The hypothesis and clause correspondence is as follows.

| Node | Lean rendering |
| --- | --- |
| Input universe U, and U-small ordinary A | Explicit `universe u`, `{A : Type u} [Category.{u} A]`. |
| P = Fun(A-op, Set-U) | Every presheaf has type `Aᵒᵖ ⥤ Type u`; R is an endofunctor of exactly that category. |
| Arbitrary auxiliary presheaf B | `(B : Aᵒᵖ ⥤ Type u)`, with no other hypothesis. |
| U-small set of monomorphisms Λ | `(Λ : Set (Arrow (Aᵒᵖ ⥤ Type u))) [Small.{u} Λ]` and `hΛ`, which asserts `Mono a.hom` for each member a. The smallness binder is essential because the ambient arrow category has object universe u+1. |
| wsat(Λ) | `weaklySaturated Λ` is the infimum of all morphism properties containing the members and isomorphisms, closed under `pushouts`, `transfiniteCompositions.{u}`, and `retracts`. The transfinite API uses well-order-continuous diagrams at limits; the retract API uses retracts of arrows. |
| Λ-injectivity | `IsLambdaInjective Λ Z`: every `u : D ⟶ Z` extends to `v : E ⟶ Z` with `f ≫ v = u` for each generator f. |
| Total-element size | `totalCardinal F = Cardinal.mk (Σ a : A, F.obj (Opposite.op a))`. |
| Existential R, eta, infinite regular lambda < alpha | `∃ R η (κ α : Cardinal.{u})`, where η is `𝟭 _ ⟶ R`; the conclusion states aleph0 bounds, `κ.IsRegular`, `α.IsRegular`, and `κ < α`. κ is the node's lambda, renamed because λ is a Lean keyword. Mathlib regularity includes infinitude and is equivalent to the stated union condition. |
| Alpha exceeds Mor(A) and size of B | `Cardinal.mk (Σ a b : A, (a ⟶ b)) < α` and `totalCardinal B < α`. The sigma type tags every arrow by its source and target. |
| (1), both clauses for every F | `weaklySaturated Λ (η.app F) ∧ IsLambdaInjective Λ (R.obj F)`. |
| (2), mono preservation | For every map f, `Mono f → Mono (R.map f)`. |
| (2), intersection and canonical identification | For every `S T : Subfunctor Y`, the intersection of `Subfunctor.range (R.map S.ι)` and `Subfunctor.range (R.map T.ι)` equals `Subfunctor.range (R.map ((S ⊓ T).ι))` inside R(Y). Because R preserves monos, these ranges are canonically the images of the indicated sources. Thus this is the specified identification by the canonical inclusions, with no arbitrary isomorphism or comparison map. |
| (3), both bounds | `totalCardinal F < α` implies both `totalCardinal (R.obj F) < α` and the strict bound on `Σ a, B.obj (op a) × (R.obj F).obj (op a)`. The latter is exactly the total-element set of the pointwise product B × R(F), without choosing a different product object. |
| (4) | The supremum of the actual image subfunctors `range (R.map S.ι)` over all S with `totalCardinal S.toFunctor < α` equals top. Supremum in Mathlib's `Subfunctor` complete lattice is objectwise union. |
| (5) | `T : κ.ord.ToType → Subfunctor Y` and `∀ ξ ζ, ξ ≤ ζ → T ξ ≤ T ζ`. The supremum of the images of R(T ξ) equals the image of R applied to the inclusion of `⨆ ξ, T ξ`, as subfunctors of R(Y). The index is the initial ordinal of κ, not an arbitrary type of that cardinality. |
| All constructions and colimits remain in U | Values, cardinal bounds, and ordinal indices all have universe u. In particular R lands in `Aᵒᵖ ⥤ Type u` and the weak-saturation definition explicitly uses `transfiniteCompositions.{u}`. Natural transformations between U-valued presheaves are U-small; no larger presheaf value universe is introduced. |

Statement dependency: `def-weil-size-convention` has a reviewed convention
record, with both module and declaration null. It explicitly instructs citers
to express universe hypotheses directly, which is done here; it requires no
import and is not replaced by a new definition. Its source and record were read.

Mathlib interfaces used include `CategoryTheory.Arrow`/`Arrow.mk`
(`Mathlib.CategoryTheory.Comma.Arrow`), `MorphismProperty.pushouts` and
`transfiniteCompositions` (`Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition`),
`MorphismProperty.retracts` (`Mathlib.CategoryTheory.MorphismProperty.Retract`),
`Subfunctor`, its complete lattice, `toFunctor`, and `ι`
(`Mathlib.CategoryTheory.Subfunctor.Basic`), `Subfunctor.range`
(`Mathlib.CategoryTheory.Subfunctor.Image`), `Cardinal.mk`,
`Cardinal.IsRegular` (`Mathlib.SetTheory.Cardinal.Regular`), and
`Ordinal.ToType` (`Mathlib.SetTheory.Ordinal.Basic`, through Arithmetic).
Definitions and full signatures/docstrings for these interfaces were read.

The stated proof prerequisites are imported as well: colimits from
`Mathlib.CategoryTheory.Limits.HasLimits`; regular cardinal bounds from
`Mathlib.SetTheory.Cardinal.HasCardinalLT`; transfinite recursion from
`Mathlib.Order.RelClasses`; square and exponential arithmetic through
`Mathlib.SetTheory.Cardinal.Arithmetic`; successor regularity through
`Mathlib.SetTheory.Cardinal.Regular`; and well-ordering through the
Cardinal.Order import exposed by Arithmetic. There are no Sheaf proof
prerequisite modules to import for this node.

Source check: opened
https://cisinski.app.uni-regensburg.de/CatLR.pdf, Construction 2.4.36 and
Lemma 2.4.37, printed pages 64–65 (zero-based PDF pages 79–80), on 2026-10-17.
The node already records the separate preservation rank and larger size bound,
the arbitrary auxiliary product factor B, and the total-element convention.
The DAG proof explains these refinements; the Lean preserves that exact node.

Edge cases checked before finalization: A empty; Λ empty; a generator with
empty domain; S or T empty; S ∩ T empty; F empty; B empty; large Y; the constant
increasing chain; noninjective attaching maps; and the smallness of Λ despite
its large ambient arrow type. No nonemptiness assumption is imposed on A, B,
Λ, F, or the subpresheaves. In the empty-generator case R may be identity. An
empty-domain generator can make R(empty) nonempty, so intersection preservation
is deliberately stated as the intersection of the two images and does not
assert preservation of the initial presheaf. The product bound alone would not
bound R(F) when B is empty; both separate bounds are present. All supremum
expressions are explicitly parenthesized as equalities of subfunctors.

Searches (all no exact match):

- `msearch.py ... leanfinder "presheaf small object replacement preserving intersections monomorphisms regular cardinal bounded size"`: eight generic small-object/cardinal hits, such as `HasSmallObjectArgument.exists_cardinal`; none supplies intersection or support/size clauses.
- `msearch.py ... loogle "MorphismProperty.transfiniteCompositionsOfShape, Subfunctor, Cardinal.IsRegular"`: zero hits (the service did not recognize the first unqualified identifier). The actual Mathlib declarations were then read directly.
- `msearch.py ... grep "weaklySaturated|transfiniteCompositions|IsInjective|Subfunctor" CategoryTheory`: 25 hits, identifying the transfinite-composition and Subfunctor APIs used here; no bounded replacement theorem.
- `msearch.py ... leansearch "presheaf functorial injective replacement preserves intersections small subobjects cardinal bound"`: eight hits about preservation of already injective objects, sheafification finite limits, and unrelated cofiltered images. None is this theorem.
- `rg` on Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json` for `totalCardinal|IsLambdaInjective|def weaklySaturated`: no matching declaration. Broader presheaf/replacement/intersection and saturation searches in the upstream and side libraries found specialized simplicial saturation and generic accessible factorization, not this result.
- The prescribed upstream grep for the exact node id found no declaration.

No STATEMENT-DISPUTED flag or node fault. The only postponed proof is
`CategoryTheory.Presheaf.exists_bounded_intersection_replacement`.

Validation: `scompile.py Q21 lem-coef-presheaf-bounded-intersection-replacement`
compiled the final module both as a sandbox file and under its library module
name, cleanly within the 60-second limit. The required `deliver2.py --no-push`
dry run is the final check; the independent second reader will add their own
reading and deliver.


## Second reading by Q21

I am the independent second reader; I did not write the statement. I read the
repository node, its sandbox copy, the entire Lean module, the size-convention
node and its blueprint source, and every recorded proof-dependency statement.
There is no repair note for this item. Only the `lean` field differs between
the sandbox node and the repository node; there is no `statement_change`, new
node, or dependency-module delivery to audit.

Source read independently: [Cisinski, Higher Categories and Homotopical
Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf), Construction
2.4.36 and Lemma 2.4.37, printed pages 64–65, zero-based PDF pages 79–80.
Construction 2.4.36 starts with an arbitrary set of monomorphisms and constructs
the replacement by simultaneous attachments and transfinite iteration. The
extra cylinder structure in the surrounding chapter is needed for the separate
functor I and its homotopy applications, not for this construction of L.
Lemma 2.4.37 supplies monomorphism/intersection preservation, small supports,
size control and preservation of long increasing unions. The node explicitly
records its agent formulation with a separate iteration/preservation rank and
larger size bound, plus arbitrary auxiliary B. I checked these refinements
against its fourteen-step argument: the regular rank bounds generator sizes
and supports; alpha = (2^theta)^+ bounds the iterated replacement and the
product with B. This does not silently add a cylinder or model-category
hypothesis to the arbitrary-generator statement. The source measures size by
arrows of A/F; its comparison with total elements is explicitly justified in
Step 14. Source text was available through the browser PDF text reader; PDF
screenshot retrieval failed with a cache miss, without obstructing the reading.

My object, hypothesis and conclusion checklist, made from the node before
matching it to Lean, is the following. Every row passes.

| Node object/hypothesis/clause | Lean rendering and verdict |
| --- | --- |
| Input universe U and U-small ordinary category A | `universe u`, `{A : Type u} [Category.{u} A]`. Both objects and arrows are U-small; no nonemptiness or geometric structure is assumed. Pass. |
| P is all U-valued presheaves on A | `Aᵒᵖ ⥤ Type u` in every binder and both ends of R. This is the full presheaf category, without sheaf or abelian hypotheses. Pass. |
| Arbitrary auxiliary B in P | `(B : Aᵒᵖ ⥤ Type u)`, without a size or nonemptiness hypothesis. Pass. |
| A U-small set Lambda of monomorphisms | `(Λ : Set (Arrow (Aᵒᵖ ⥤ Type u))) [Small.{u} Λ]` and `hΛ : ∀ a, a ∈ Λ → Mono a.hom`. Smallness concerns the set of generators, despite the larger ambient arrow-object type; it places no uniform cardinal bound on their domains/codomains in the hypotheses. Pass. |
| Generated weak saturation, with all stated closures | `weaklySaturated Λ` takes `sInf` of properties containing exactly the generators and all isomorphisms, with `W.pushouts ≤ W`, `transfiniteCompositions.{u} W ≤ W`, and `W.retracts ≤ W`. I read the Mathlib definitions: pushouts are genuine `IsPushout` squares, transfinite compositions use well-order-continuous functors and a colimit cocone, and retracts use `RetractArrow`. Retract closure also transports membership across arrow isomorphisms. Thus this is the least class with the node's closures, including limit continuity and the input-universe restriction. Pass. |
| Lambda-injectivity | `IsLambdaInjective Λ Z` quantifies over every generator f and every `u : D ⟶ Z`, and asks for `v : E ⟶ Z` with `f ≫ v = u`. It asks for existence rather than uniqueness of an extension. Pass. |
| Total-element size | `totalCardinal F = Cardinal.mk (Σ a : A, F.obj (Opposite.op a))`. Objects label every element, as in the node's disjoint union. Pass. |
| One R, eta, lambda, alpha working simultaneously | The single outer existential binds endofunctor R, `η : 𝟭 _ ⟶ R`, and `(κ α : Cardinal.{u})`, before any quantification over input F, Y, subpresheaves, or chains. κ denotes the node's lambda. Pass. |
| Infinite regular lambda < alpha | Both `aleph0` lower bounds, `κ.IsRegular`, `α.IsRegular`, and `κ < α` are present. I read `Cardinal.IsRegular` and `sum_lt_of_isRegular`/`card_iUnion_lt_iff_forall_of_isRegular`; this is the node's regular-union convention for infinite cardinals. Pass. |
| Alpha exceeds arrows of A and total size of B | `Cardinal.mk (Σ a b : A, (a ⟶ b)) < α` and `totalCardinal B < α`. The first sigma type contains every arrow, labelled by both ends. These are conclusions, not stronger assumptions. Pass. |
| (1) Every unit lies in wsat(Lambda), and every R(F) is Lambda-injective | `∀ F, weaklySaturated Λ (η.app F) ∧ IsLambdaInjective Λ (R.obj F)`. The same R and eta are used throughout. Pass. |
| (2) R preserves all monomorphisms | `∀ {X Y} (f : X ⟶ Y), Mono f → Mono (R.map f)`. No inclusion-only restriction. Pass. |
| (2) The canonical map identifies R(S intersection T) with the intersection inside R(Y) | The equality of `Subfunctor.range (R.map S.ι) ⊓ Subfunctor.range (R.map T.ι)` with `Subfunctor.range (R.map ((S ⊓ T).ι))`. I opened `Subfunctor`, `toFunctor`, `ι`, its mono instance, and `range`: these are actual subsets and inclusion maps. Because R preserves monos, equality of these images is exactly the canonical identification; an arbitrary isomorphism is not substituted. Pass. |
| (3) Small F has small R(F), and B times R(F) is small | Under `totalCardinal F < α`, the conclusion contains both `totalCardinal (R.obj F) < α` and the cardinal bound on `Σ a, B.obj (op a) × (R.obj F).obj (op a)`. The latter is the total-element set of the pointwise product, with the same object label in both factors. Pass. |
| (4) For every Y, images of R(T) for all alpha-small T cover R(Y) | The supremum over `(S : Subfunctor Y)` and the proof of `totalCardinal S.toFunctor < α` of the actual range of `R.map S.ι` equals top. `Subfunctor.iSup_obj` identifies this supremum with objectwise union. The bound applies to S, not Y. Pass. |
| (5) Increasing lambda-chain and its canonical union identification | `T : κ.ord.ToType → Subfunctor Y`, with `∀ ξ ζ, ξ ≤ ζ → T ξ ≤ T ζ`; equality of the supremum of the ranges of `R.map (T ξ).ι` with the range of `R.map ((⨆ ξ, T ξ).ι)`. I read `Ordinal.ToType`/`type_toType`: this is the initial ordinal of cardinality κ with its actual order, not an arbitrarily ordered set of that cardinality. Monomorphism preservation makes these ranges the specified subpresheaves. Pass. |
| Constructions and colimits stay in U | Presheaf values, tagged element sets, cardinal bounds and ordinal indices are all at level u; weak saturation explicitly uses transfinite compositions at level u. The functor category itself is allowed its necessary larger object universe. No equality of unrelated site universes or extra smallness of the entire presheaf category is assumed. Pass. |

Dependency interfaces: `def-weil-size-convention` has null module/declaration
and an explicit reviewed `convention: true` instruction to express size
hypotheses directly. This module follows it; it does not invent a replacement
object. I also opened the recorded Mathlib proof interfaces: the generated
colimit declarations in `Limits.HasLimits`, `Cardinal.mul_eq_self`,
`Cardinal.cantor`, `Cardinal.power_mul`, `Cardinal.isRegular_succ`,
`HasCardinalLT.exists_regular_cardinal`, `WellFoundedLT.fix`/`fix_eq`, and
`exists_wellFoundedLT`. The imports expose the node's recorded proof plan.
No missing or unusable dependency interface was found.

Edge cases checked independently: A empty (all tagged element sets and arrow
sets empty); Lambda empty (identity replacement is allowed); empty generator
domain (the replacement of the initial presheaf need not be initial); F or B
initial; either subpresheaf or their intersection empty; arbitrary-size Y in
the given presheaf universe; constant increasing chains; and finite categories
and finite generators. No binder excludes these cases. In particular, clause
(2) does not assert preservation of the initial object, and clause (3) keeps
the separate R(F) bound when B is empty. A noninjective attaching map is
allowed: only the generator itself is required monic. The chain rank cannot
be zero because it is infinite; the node has that same requirement. Scheme
emptiness, n = 0 and characteristic impose no further cases here: no scheme,
integer degree or coefficient ring occurs. All universe levels and variables
are explicitly bound, and the set of generators has exactly the stated
smallness hypothesis.

My independent searches used different wording from the first reader:

- `msearch.py ... leanfinder "An injective envelope functor on set valued presheaves preserves binary meets of subobjects and unions of chains with a regular cardinal bound"`: eight hits, including presentable functor limits and Grothendieck-abelian subobject/injectivity results; none has this category, arbitrary generator family, intersections and five simultaneous clauses.
- `msearch.py ... leansearch "weak saturation of morphisms generated by pushouts transfinite compositions and retracts"`: eight hits, including `MorphismProperty.llp_rlp_of_hasSmallObjectArgument'` and generic model structures; none defines the generated closure or supplies this presheaf theorem with cardinal/support properties.
- `msearch.py ... loogle 'CategoryTheory.MorphismProperty, "injective"'`: ten hits about injective morphisms in concrete categories and unrelated derived constructions. These do not define extension against a chosen family of arrows.
- Direct `rg` on Mathlib's CategoryTheory and SmallObject files, upstream `WeilConjectures`, the project's `lean/Sheaf`, and `dag/lean_names_upstream.json`, for weak saturation, injective replacement, total/cardinal size, and preservation of intersections. I opened the actual candidate `SSet.Enhanced.WeaklySaturated` in `PushoutJoinSaturation.lean`: it is a property of a class of simplicial maps, not generated weak saturation for arbitrary presheaves. I opened `MorphismProperty.exists_accessible_functorial_factorization` in `AccessibleSmallObjectFactorization.lean`: it states generic factorization/accessibility with a universal closure clause, without intersection and size/support conclusions. Neither is an exact replacement for this item or its helper definitions. The existing categorical `Injective` class is injectivity against all monos; it is not Lambda-injectivity for an arbitrary specified set. No exact definition or theorem was found.

H5/H6/H8/H9 checks: the three helper definitions have explicit real data;
none chooses data from a postponed existence theorem. The only theorem is
`CategoryTheory.Presheaf.exists_bounded_intersection_replacement`, with the
whole proof `sorry`. Its docstring contains all fourteen proof steps and the
named prerequisites, including the support argument and the source size
comparison. Every declaration and the module docstring has its source and
blueprint id. There are no private/local replacement notions or file-local
notation/instances, no unbound variable, no over-100-character Lean line, and
no changed natural-language statement. The node's `lean.statement` was checked
verbatim against the theorem signature and is identical.

Mismatches found: none. Changes made by this second reading: appended this
independent report only; the correct Lean and node record were left unchanged.
Independent validation: the prescribed `scompile.py Q21
lem-coef-presheaf-bounded-intersection-replacement <module path>` completed
successfully, both sandbox and library module checks, with no warnings or
errors (1.0 s and 1.1 s respectively). The delivery dry run follows below.

Delivery validation: `deliver2.py Q21 lem-coef-presheaf-bounded-intersection-replacement --no-push` printed `OK (dry run)` for commit `bef48ad605`: preflight and compilation passed, nothing pushed.
