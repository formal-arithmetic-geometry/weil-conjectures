## Worker report

The module `Sheaf.CategoryTheory.TruncationCoupleExact` states that for a left exact additive functor `F` between Grothendieck abelian categories and a bounded-below complex `K` with the stated lower cohomology vanishing, there exists a type-zero `CategoryTheory.BigradedExactCouple B 0` whose bigraded objects and three structure maps are heterogeneously equal to the corresponding components of `CategoryTheory.truncationCouple F K a ha`. The exact-couple fields of the existential witness render the three zero composites and kernel/image equalities required by `def-sp-exact-couple`; the five displayed HEq clauses identify `D`, `E`, `alpha`, `f`, and `g` with the truncation-couple data, including the dependent source and target indices.

Dependencies used: `Sheaf.CategoryTheory.TruncationCouple` declaration `CategoryTheory.truncationCouple`; `Sheaf.CategoryTheory.ExactCouple` declaration `CategoryTheory.BigradedExactCouple`; Mathlib leaves `CategoryTheory.Functor.rightDerived` and `CategoryTheory.IsGrothendieckAbelian` recorded by the dependency nodes.

Edge cases checked: the lower bound `a` and condition `ha` are retained even when vacuous; indices `p,q : ℤ` are unrestricted; type-zero bidegrees are represented by the exact-couple structure (whose `g` target uses `p + 0`, `q - 0`), with HEq handling these dependent types; the zero and empty cases are not excluded by the category assumptions.

Searches made: the target's recorded stage-1 LeanSearch, Loogle/LeanFinder, and Mathlib grep searches found no exact-couple declaration or truncation-couple exactness theorem. `rg` over `WeilConjectures/` and `lean/Sheaf/` found only the existing truncation-couple and exact-couple definitions cited above. No new nodes or statement correction were needed.

## Earlier second reading (a previous round; superseded)

I read the node statement clause by clause. The functor hypotheses are the explicit `F.Additive` and `PreservesFiniteLimits` instances, and both Grothendieck abelian category hypotheses are binders. The complex, integer lower bound, and implication expressing vanishing below the bound are all retained verbatim. The conclusion introduces one `BigradedExactCouple B 0`; its `D` and `E` fields and each of `alpha`, `f`, and `g` are identified with the five components returned by `truncationCouple`. The exact-couple structure itself supplies every zero-composite and kernel/image clause from the node dependency.

## Second reading by J1

I opened the item node and all four statement dependency nodes, the complete
`TruncationCouple.lean` construction, the fields of `BigradedExactCouple` in
`ExactCouple.lean`, and the Mathlib declarations behind the two Mathlib leaves.
The local literature checkout is absent, so I read the source files read-only
on the project server: the blueprint node at order 1210, `derived.tex` Remark
08J5 (including the consecutive-upper-truncations triangle), Proposition 05SE,
and Definition 0147 / sequence 0148; `homology.tex` Definition 011Q. Those
places impose no extra finiteness, nonzero-object, or geometric hypotheses.
The blueprint statement is exactly the item's statement; the node's repaired
four-step proof correctly uses T_{q+1} for exactness at alpha.

Clause-by-clause checklist (all verdicts: exact match):

- Objects A and B are Grothendieck abelian categories: `{A : Type u₁}` and
  `{B : Type u₂}`, the independent `Category.{v₁}` / `Category.{v₂}` and
  `Abelian` instances, and `IsGrothendieckAbelian.{v₁} A` /
  `IsGrothendieckAbelian.{v₂} B`. I read Mathlib's class at
  `CategoryTheory/Abelian/GrothendieckCategory/Basic.lean:70`: at w = hom
  universe it gives exact small filtered colimits and a separator, with small
  colimits inferred at line 99; local smallness at that size is automatic.
- Object v : A -> B and additivity: `(F : A ⥤ B) [F.Additive]`.
  `Functor.Additive` is map-additivity, equivalent to preservation of finite
  biproducts in abelian categories, as recorded by def-sp-left-exact-additive.
- Left exactness: `[PreservesFiniteLimits F]`. I read that Mathlib class and
  `Functor.preservesFiniteLimits_of_preservesKernels` in `Preadditive/LeftExact`:
  with additivity and the abelian category structures, this is equivalent to
  the node's kernel preservation, and is not an extra assumption.
- Object K is a bounded-below cochain complex: `(K : CochainComplex.Plus A)`.
  I opened `CochainComplexPlus.lean:30,42`; Plus is precisely the full
  subcategory defined by existence of an integer strict lower bound.
- Integer lower cohomology bound: `(a : ℤ)` and
  `(ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q))`. This retains exactly
  the stated vanishing condition, although the proof does not use it.
- The specified truncation couple: every component in the conclusion comes
  from `truncationCouple F K a ha`, the recorded dependency declaration.
  I read its D and E definitions: H^{p+q} of the derived upper truncation and
  derived single complex H^q(K)[-q], using the recorded chosen-resolution
  bridge. I read alpha (derived truncation inclusion), g (derived projection),
  and f (derived triangle's HomologySequence.δ). No new copy is introduced.
- Conclusion introduces the exact structure on those data:
  `∃ X : BigradedExactCouple B 0`, followed by `HEq X.D ...` and
  `HEq X.E ...`. These are equalities of the entire indexed families, not
  merely pointwise isomorphisms or an unrelated exact couple.
- All three specified arrows, with quantifiers over every integer p and q:
  the three `∀ p q, HEq ...` clauses identify alpha with tuple component
  `.2.2.1`, f with `.2.2.2.1`, and g with `.2.2.2.2`. The dependency signatures
  give bidegrees (-1,+1), (+2,-1), and (0,0). At type zero the exact-couple
  g target is E(p+0,q-0); HEq handles the dependent targets without adding
  any mathematical freedom. Once the object equalities are transported,
  the arrow HEqs assert equality of the specified morphisms.
- Three zero composites: `X.alpha_f_zero`, `X.f_g_zero`, and
  `X.g_alpha_zero` render alpha after f, f after g, and g after alpha equal
  to zero at every bidegree.
- ker alpha = im f: `X.exact_alpha` is im(f(p,q)) =
  ker(alpha(p+2,q-1)); reindex p -> p-2 and q -> q+1 to obtain the node's
  equality in D^{p,q}. Equality symmetry only changes the display order.
- ker f = im g: `X.exact_f` at type zero is im(g(p,q)) = ker(f(p,q)),
  with the harmless zero-index transports.
- ker g = im alpha: `X.exact_g` is im(alpha(p,q)) =
  ker(g(p-1,q+1)); reindex p -> p+1 and q -> q-1. Both sides of each
  equality are Mathlib subobjects of the same object, exactly as the node
  requires. Thus the existential structure is equivalent to all the desired
  exactness clauses for the original data, and gives no stronger conclusion.

Edge cases: p, q and a range over all integers, including zero and negative
values. No first-quadrant, nonzero, field, characteristic, or finiteness
hypothesis appears. The zero complex is admitted (with every a and its
vanishing proof), and zero Grothendieck categories are not excluded. The
indexing here is the fixed set ℤ², not an arbitrary family whose empty case
would need another binder; empty schemes and characteristic are inapplicable
because no schemes or coefficient rings are parameters. All four universes
are independently declared and there is no object-universe equality or
small-category restriction. Derived-category existence is handled internally
by the dependency's standard construction, not an extra theorem hypothesis.
The inferred p and q binders are ℤ by their morphism arguments; nothing is
left auto-implicit.

Independent searches (2026-10-11, recorded by msearch.py in searches.jsonl):

- LeanSearch: "the canonical truncation filtration of a bounded below complex
  gives an exact couple". Service unavailable (Internal Server Error), not
  counted as a negative mathematical search.
- LeanFinder: "homology of derived upper truncations forms a bigraded exact
  couple". Eight results, including
  `HomologicalComplex.shortComplexTruncLE_shortExact` and
  `CochainComplex.shortComplexTruncLE_shortExact`, but no exact couple or
  truncation-couple exactness theorem. These state short exact complexes for
  a truncation and its quotient, not exactness of the derived bigraded couple.
- Mathlib grep: `couple|truncation.*exact|truncLE.*exact` in Algebra/Homology.
  Ten hits, again the truncation short-exact-complex ingredients only.
- Direct rg with those alternative words over the complete source
  `WeilConjectures/` and project `lean/Sheaf/` found only the recorded couple
  construction and exact-couple definition, plus unrelated truncation lemmas.
  Direct rg for `exact.?couple|truncationCouple_exact|lem-sp-truncation-couple-exact`
  in `WeilConjectures/` and `dag/lean_names_upstream.json` found no declaration.
  Therefore this theorem is new; neither existing ingredient states it.

Repairs: H8, the source used an ellipsis rather than an identifiable place and
its proof docstring was only a summary. Replaced both source references with
chapter, unit, node order and the precise Stacks tags; wrote out all four
proof steps with their dependency nodes, the derived connecting-map
identification and the essential T_{q+1} reindexing. H9, added the standard
copyright/license/authorship header. The mathematical signature and node
record are unchanged; no statement correction, new node, or dependency
module is necessary. There is only one theorem, with proof `sorry`; no data
definition or other proof is added. Both imports are used.

Validation: scompile.py compiled this module on the server in 1.4 seconds,
exit code 0, with no warnings. By direct comparison, `lean.statement` is
verbatim the theorem signature, all lines are at most 100 characters, and
all variables and universes are bound.

## Reviewer fix (R-tce1008, stage 2)

The delivered conclusion `∃ X : BigradedExactCouple B 0` tied to the truncation-couple data by five `HEq` clauses introduced a second couple object and relied on dependent `HEq` across the `p + 0`, `q - 0` index transports of the type-0 `g`. Restated, per the lead, as exactness of exactly the landed couple `truncationCouple F K a ha` (c333e8bcb): at each vertex, the zero composite `w` and `(ShortComplex.mk _ _ w).Exact`, for f then alpha at D^{p+2,q-1}, g then f at E^{p,q}, and alpha then g at D^{p-1,q+1}, all p q : ℤ; these are the three zero composites and three ker = im conditions of def-sp-exact-couple. Import of `Sheaf.CategoryTheory.ExactCouple` replaced by `Mathlib.Algebra.Homology.ShortComplex.Exact`. Hypotheses unchanged. Compiled clean.
