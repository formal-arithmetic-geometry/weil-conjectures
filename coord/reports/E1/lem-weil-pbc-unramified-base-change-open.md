## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen` states
`AlgebraicGeometry.unramified_baseChange_restrict_open`.  It renders the node's
unramified hypothesis as `LocallyOfFiniteType f ∧ IsOpenImmersion
(pullback.diagonal f)`, using the recorded Mathlib characterization.  Clause (1)
quantifies a morphism `g : S' ⟶ S` and states local finite type and open diagonal
for `pullback.snd f g : pullback f g ⟶ S'`, the second projection of the fibre
product.  Clause (2) quantifies open subsets `U : X.Opens`, `V : S.Opens` and the
image condition `hUV : ∀ x : U, f.base x.1 ∈ V`; it states local finite type and open diagonal for the canonical restriction
`f.resLE V U hUV : U.toScheme ⟶ V.toScheme`; Mathlib's `resLE_comp_ι` gives
the defining factorization through the open inclusions.

The four statement dependencies are used as follows: schemes and morphisms are
Mathlib `AlgebraicGeometry.Scheme`; fibre products are Mathlib
`CategoryTheory.Limits.pullback` and `pullback.snd`; unramifiedness is the
recorded conjunction `LocallyOfFiniteType` and `IsOpenImmersion (pullback.diagonal
f)` from `def-weil-unramified-morphism`; open subschemes are Mathlib
`Scheme.Opens`, `toScheme`, and `ι`, matching `def-weil-open-immersion`.

Edge cases checked: the base-change morphism `g` is arbitrary (including an empty
or terminal scheme); `U` and `V` may be empty or the whole schemes; no nonemptiness,
separation, or finiteness hypotheses are added; the factorization condition covers
all image-inclusion cases.

Searches made:

- LeanFinder (`unramified morphisms stable under base change and restriction to
  open subschemes`): found Mathlib formally-unramified stability and diagonal
  declarations, but no single declaration of the combined statement.
- Loogle (`LocallyOfFiniteType, IsOpenImmersion, pullback.diagonal`): unavailable,
  unknown identifier `LocallyOfFiniteType`.
- Mathlib grep (`LocallyOfFiniteType.*IsOpenImmersion|pullback.diagonal` in
  `AlgebraicGeometry`): found `FormallyUnramified.isOpenImmersion_diagonal`
  (Morphisms/FormallyUnramified.lean:126) and pullback diagonal infrastructure,
  but no combined theorem.
- Project grep for `unramified_baseChange_restrict_open` and unramified base-change
  statements: no existing declaration of this node.

## Earlier second reading (a previous round; superseded)

Worker self-check only, included for the dry-run preflight. The independent second
reader has not yet read this delivery and must replace this section before pushing.

## Final statement rendering

Clause (2) now uses the existing canonical restriction `Scheme.Hom.resLE` directly,
rather than existential factorization data. Its full definition and docstring were
read in Mathlib/AlgebraicGeometry/Restrict.lean:775; `resLE_comp_ι` at line 789 gives
the factorization. The open-image hypothesis is `U ≤ f ⁻¹ᵁ V`, exactly f(U) ⊆ V.
The conclusion has precisely local finite type and open diagonal for this restriction.

The local Stacks source is absent on this clone, so the sources were read online:
[02GA](https://stacks.math.columbia.edu/tag/02GA) states base-change stability;
[02G6](https://stacks.math.columbia.edu/tag/02G6), final Moreover clause, states
restriction stability for arbitrary open subschemes with the image containment.
LeanSearch was also run with `unramified scheme morphism base change restriction opens`:
service unavailable (Internal Server Error), recorded without a no-match verdict.
The source-repository node-id search had no hits.

## Second reading by E1

Independent review of the unchanged node, its four statement dependencies, and
`UnramifiedBaseChangeOpen.lean`. No `statement_change`, new definition nodes, or
dependency modules occur in this delivery.

Source check: the local Stacks checkout is absent. I read the actual
`morphisms.tex` from the Stacks project's upstream repository, at labels
`lemma-base-change-unramified` and `lemma-unramified-characterize`, and checked
the rendered tags [02GA](https://stacks.math.columbia.edu/tag/02GA),
[02G6](https://stacks.math.columbia.edu/tag/02G6), and
[02GE](https://stacks.math.columbia.edu/tag/02GE). The first two assume arbitrary
morphisms of schemes; there is no standing Noetherian, separation, finite
presentation, field, or characteristic hypothesis. The node selects the
unramified assertions, not the additional G-unramified assertions in the source.
The diagonal characterization in 02GE matches the dependency node.

Object/hypothesis/conclusion checklist (all verdicts: exact):

| Node item | Lean rendering and verdict |
| --- | --- |
| Schemes X and S and morphism f | `{X S : Scheme.{u}}`, `f : X ⟶ S`; the recorded `Scheme` and `Scheme.Hom` are locally affine locally ringed spaces and their morphisms. |
| f unramified | `hf : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`; precisely the conjunction recorded by `def-weil-unramified-morphism`, with no stronger global finite-type assumption. |
| Arbitrary scheme S' and map g | `{S' : Scheme.{u}}`, `g : S' ⟶ S`; no property or additional instance required of g. |
| Base-change object and structure map | `pullback f g` and `pullback.snd f g`; `def-pc-fibre-product` records this chosen categorical pullback and second projection to S'. |
| Clause (1): f' unramified | The first two conclusion conjuncts assert `LocallyOfFiniteType (pullback.snd f g)` and its diagonal is an open immersion. |
| Open subschemes U and V | `∀ (U : X.Opens) (V : S.Opens)`; `Scheme.Opens` and `toScheme` give the canonical open subschemes with the restricted structure sheaf, matching `def-weil-open-immersion`. |
| Image inclusion f(U) ⊆ V | `hUV : U ≤ f ⁻¹ᵁ V`; pointwise this says every point of U maps into V, including empty opens. |
| The restriction U → V | `f.resLE V U hUV`; I read `Scheme.Hom.resLE` and `resLE_comp_ι` in `Restrict.lean:775–790`. The latter identifies its composite with V's inclusion as U's inclusion followed by f, so this is the required restriction. |
| Clause (2): restriction unramified | Last conjunct universally asserts local finite type and open diagonal for exactly `f.resLE V U hUV`. |

The conclusion associates as A ∧ (B ∧ C), equivalently (A ∧ B) ∧ C.
The binder g universally quantifies clause (1); it does not limit clause (2),
which has no occurrence of g. Clause (2) is available for every f by instantiating
g with the identity of S if needed. U, V, and their image-inclusion proof are
universally quantified in the node's order.

Dependency signatures inspected in pinned Mathlib: `Scheme` and `Scheme.Hom`
in `Scheme.lean:42,74`; `pullback`, `pullback.fst`, and `pullback.snd` in
`HasPullback.lean:95,111,115`; `LocallyOfFiniteType` in `FiniteType.lean:43`
(finite-type maps on arbitrary affine-open pairs); `IsOpenImmersion` in
`OpenImmersion.lean:38` (the underlying locally ringed space notion); and
the two diagonal/formally-unramified instances in `FormallyUnramified.lean`.
These serve the actual dependency notions, with no private replacement.

Edge cases: empty X, S, or S' are allowed whenever the displayed morphisms
exist; U = ⊥ and V = ⊥ are allowed subject only to the image inclusion;
whole opens are allowed. No index set, coefficient object, or integer n is
introduced, so empty index sets, zero objects, and n = 0 add no omitted case.
Schemes over any commutative ring and in every characteristic are included.
The declared arbitrary universe u is the shared universe of the category of
schemes and its pullbacks; no fixed small universe or test-object universe is
imposed. All variables and the universe are bound explicitly.

Independent searches, using wording different from the worker's:

- LeanFinder via `msearch.py`: "scheme morphism with open diagonal and locally
  finite type preserved under pullback and resLE". Eight results: diagonal
  locality infrastructure, `FormallyUnramified.isOpenImmersion_diagonal`, and
  local-finite-type pullback instances; none states both clauses of this node.
- LeanSearch via `msearch.py`: "unramified morphism arbitrary fibre product
  restriction open subschemes". Service returned Internal Server Error;
  unavailable, not evidence of absence.
- Direct rg in Mathlib for local finite type and resLE found the restriction
  instance in `FiniteType.lean:98` and the base-change instances at 84–92.
  Reading `FormallyUnramified.lean` found base-change stability and the
  diagonal characterization, not the combined statement.
- Direct rg over all `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the declaration name and alternative
  unramified/base-change/restriction wording found no existing combined
  declaration. I also read the upstream extension
  `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`:
  its equalizer, section, stalk, and residue-field results are different
  statements. Project references to this node occur in other proof docstrings,
  not declarations realizing the node.

No mathematical mismatch found; Lean and node signature are unchanged and
agree verbatim after whitespace normalization. The existing six-step docstring
follows the DAG proof, including the local-finite-type and infinitesimal
uniqueness arguments for restriction. There are no definitions, hidden data
holes, local notation, private copies, or proved theorems; the sole proof is
`sorry`. The import supplies all notions used. The second reading changes only
this report, adding the independent source and clause-by-clause audit.
