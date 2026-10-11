## Worker report

The module states `AlgebraicGeometry.proper_coproduct_two`. It uses the Mathlib
scheme coproduct `W₁ ⨿ W₂`, with coprojections `coprod.inl` and `coprod.inr`,
and the induced map `coprod.desc p₁ p₂`. The first conjunct renders clause (1)'s
claim that the first coprojection is an open immersion; the second conjunct does
the same for the second coprojection. The `IsCompl` conjunct renders that the
underlying set is the disjoint union of the two images (both disjointness and
coverage). The final conjunct says that, under the hypotheses `[IsProper p₁]`
and `[IsProper p₂]`, the induced map is proper.

Dependency declarations used are `AlgebraicGeometry.Scheme` from
`Mathlib.AlgebraicGeometry.Scheme` (`def-pc-scheme`),
`AlgebraicGeometry.IsOpenImmersion` from Mathlib's open-immersion modules
(`def-weil-open-immersion`), and `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (`def-weil-proper-morphism`).
The coproduct and its open-immersion/complement facts are Mathlib's
`CategoryTheory.Limits.coprod`, `AlgebraicGeometry.instHasFiniteCoproductsScheme`,
`AlgebraicGeometry.instIsOpenImmersionCoprodInl`/`...Inr`, and
`AlgebraicGeometry.isCompl_range_inl_inr`; they are used as the notions in the
statement and are not reproved here.

Edge cases checked: the schemes may be empty or equal, and no nonemptiness,
separation, or characteristic assumptions are added; `IsCompl` handles empty
components and guarantees both disjointness and exhaustive coverage. The two
properness assumptions are typeclass hypotheses exactly on `p₁` and `p₂`.

Searches made: `msearch.py leanfinder "proper morphism coproduct of two schemes IsProper coprod.desc"`
returned finite/affine coproduct analogues but no properness theorem; `msearch.py
loogle "IsProper coprod.desc"` returned no hits; `msearch.py grep "coprod.desc IsProper"
AlgebraicGeometry` returned no hits. Repository `rg` found no existing project
statement. Mathlib source search found open immersion and complement lemmas in
`AlgebraicGeometry/Limits.lean`, but no `IsProper (coprod.desc ...)` result.

No statement dispute or node fault was found.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: `S`, `W₁`, `W₂`, `p₁`, and `p₂` are the
same objects as in the node. The first two conjuncts state open immersions of
exactly `ι₁` and `ι₂`; `IsCompl` states precisely that their images are disjoint
and cover the coproduct; and the final universally quantified instance
hypotheses and properness conclusion match clause (2). The explicit coproduct
and induced map are Mathlib's canonical ones, so no extra structure or case is
introduced.

## Second reading by H1

I independently opened the node copy, its theorem, and all three statement
dependency nodes. The object/hypothesis/conclusion inventory and matching are:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme S | `{S : Scheme.{u}}` in the grouped binder | Exact; no base field, Noetherian, or separation hypothesis. |
| Schemes W₁ and W₂ and maps p₁, p₂ to S | `{W₁ W₂ : Scheme.{u}} (p₁ : W₁ ⟶ S) (p₂ : W₂ ⟶ S)` | Exact; these are scheme morphisms, not just continuous maps. |
| W is their scheme coproduct | `W₁ ⨿ W₂` | Exact; Mathlib's chosen categorical coproduct, representing the node's disjoint union up to its unique coproduct isomorphism. |
| Coprojections ι₁ and ι₂ | `coprod.inl : W₁ ⟶ W₁ ⨿ W₂` and `coprod.inr : W₂ ⟶ W₁ ⨿ W₂` | Exact canonical coprojections. |
| p restricts to pₖ on each coprojection | `coprod.desc p₁ p₂ : W₁ ⨿ W₂ ⟶ S` | Exact induced map; `coprod.inl_desc` and `coprod.inr_desc` supply the defining identities, so no additional equality hypothesis is needed. |
| Clause (1), first coprojection open | First `IsOpenImmersion` conjunct | Exact. |
| Clause (1), second coprojection open | Second `IsOpenImmersion` conjunct | Exact. |
| Clause (1), disjointness and coverage of the underlying set | `IsCompl (Set.range coprod.inl) (Set.range coprod.inr)` with the explicit morphism types | Exact: complementary subsets mean both disjoint and exhaustive. The scheme morphism coercions are their maps on points. |
| Clause (2), only if both component maps are proper | `∀ [IsProper p₁] [IsProper p₂], ...` inside the final conjunct | Exact implication, after the unconditional clause (1); properness is not assumed for that clause. |
| Clause (2), induced map proper | `IsProper (coprod.desc p₁ p₂ : W₁ ⨿ W₂ ⟶ S)` | Exact; no stronger conclusion. |

Dependency signatures read directly in the pinned Mathlib source:
`Scheme` extends `LocallyRingedSpace` with `local_affine`, and `Scheme.Hom`
is a morphism of locally ringed spaces (`Scheme.lean:42,74`).
`IsOpenImmersion` is the underlying locally-ringed-space open immersion
(`AlgebraicGeometry/OpenImmersion.lean:38`), matching the dependency's
`mathlib_match` (its `lean` is null). `IsProper` extends `IsSeparated`,
`UniversallyClosed`, and `LocallyOfFiniteType` (`Morphisms/Proper.lean:42`).
I also read the diagonal closed-immersion field of `IsSeparated`, the
arbitrary-base-change closed-map field of `UniversallyClosed`, and its
`QuasiCompact` instance (`UniversallyClosed.lean:167`). Thus the locally finite
type formulation is equivalent to the node's finite type formulation.
None of these dependencies needs a replacement module or extra definition.

Source reading: the repository's literature files are not present on this
machine, so I read the local Stacks .tex copies at
`/home/ubuntu/c1-stacks-review/coherent.tex` (lines 7374 onward, label
`lemma-union-closed-proper-over-base`), `schemes.tex` (lines 2510 onward,
`section-glueing-schemes`), and `morphisms.tex` (lines 9854 onward,
`definition-proper`). The proof at 0CYR uses properness of a finite disjoint
union without proving it. Its ambient map X → S is locally of finite type
because it concerns closed subsets proper over S; this is not an additional
hypothesis on S or on the two independent proper scheme maps here. The gluing
construction with empty off-diagonal overlaps gives precisely clause (1),
with no ambient finiteness assumption. Definition 01W1 gives exactly the
three properness properties in the node's proof. No source-wide Noetherian,
field, characteristic, or nonemptiness condition is needed for this lemma.

Edge cases: either component or both may be empty; `IsCompl` still says exactly
empty/nonempty complementary pieces, and properness of the maps is meaningful
in those cases. The base may be empty (then any given maps have empty sources).
Equal component schemes are allowed: the coprojections still have disjoint
images in the coproduct. No variable index set or cohomological degree occurs;
empty index sets, n = 0, and zero objects are therefore not additional cases
of this binary scheme statement. No characteristic is fixed. The declared
universe `u` is arbitrary, and the common universe is the standard encoding
of the category of schemes and its binary coproduct; it introduces no extra
independent small universe for test schemes or algebras. All variables and
universes in the statement are explicitly bound.

Independent searches used different wording from the worker:
- `msearch.py leanfinder "finite disjoint union of proper schemes is proper over the base"`
  returned finite/affine analogues and coproduct existence, no exact properness result.
- `msearch.py loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.coprod.desc"`
  returned zero hits.
- `msearch.py leansearch "The disjoint union of two proper morphisms of schemes is proper"`
  was unavailable (Internal Server Error); no negative verdict is inferred from it.
- `msearch.py grep "(IsProper|UniversallyClosed|IsSeparated).*(coprod|sigmaDesc)|(coprod|sigmaDesc).*(IsProper|UniversallyClosed|IsSeparated)" AlgebraicGeometry`
  returned zero hits. Direct `rg` also searched the project's `lean/Sheaf`,
  source `WeilConjectures`, and Mathlib algebraic geometry using "disjoint union",
  "coproduct", "proper", and the proposed full declaration name. No duplicate
  statement was found. I opened upstream `IsZariskiLocalAtSource.coprodDesc`:
  it requires a source-local property, so does not state this properness lemma.
  I opened Mathlib `Limits.lean:344–352`: the first clause exists there,
  but no theorem found supplies the complete node, including clause (2).
  The upstream name map contains neither this node nor its declaration.

Mismatches repaired: H8, the original theorem docstring only summarized the
four proof steps and omitted their dependency names and arguments. I expanded
it with each step's construction: the clopen pieces; finite affine covers
and their algebra structures; closed-set images under arbitrary base change;
and the four clopen self-product pieces and closed diagonal criterion.
H9, the module lacked the example's copyright/license/author header; added it.
No Lean statement or node statement was changed. The node has no
`statement_change`, and there are no new nodes or dependency modules to review.
The only theorem proof remains `by sorry`; there are no definitions, hollow
data, or extra proved lemmas. Both imports supply notions used in the signature.
