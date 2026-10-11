## Worker report

The module `Sheaf.RingTheory.FilteredColimitOfFactorization` states
`CommAlgCat.exists_filtered_colimit_of_factorization`, with its sole proof `sorry`.
It is exactly the direction (2) implies (1) of Stacks Tag 07C3; no definition,
new node, dependency module, or statement correction is needed. The original
node changes only in `lean`.

Source checked: https://stacks.math.columbia.edu/tag/07C3, Lemma 10.127.4,
statement and second proof paragraph. The local `literature/stacks-project/algebra.tex`
is absent on this machine, so the official online source was read. The four-step
proof from the node is carried in the theorem docstring, including its named
proof dependencies and the transport-of-colimit argument.

Hypotheses and clauses, in order:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- A commutative R-algebra Λ: `(Λ : CommAlgCat.{max u v} R)`; its bundled
  instances provide exactly the commutative ring and R-algebra structures.
- A set E of commutative R-algebras: `(E : Set (CommAlgCat.{max u v} R))`.
  Membership is literal membership, not membership merely up to isomorphism.
- Every B in E has finite presentation: `hfp : ∀ B ∈ E,
  Algebra.FinitePresentation R B`. Mathlib's class requires a surjection
  `MvPolynomial (Fin n) R →ₐ[R] B` with finitely generated kernel, precisely
  the finite-generators-and-relations description in the node, including n,m = 0.
- For every finitely presented A and every α: `hfactor` quantifies over
  `A : CommAlgCat.{max u v} R`, then `Algebra.FinitePresentation R A`, then
  every `α : A ⟶ Λ`.
- The required B, β, γ: `∃ B, B ∈ E ∧ ∃ (β : A ⟶ B) (γ : B ⟶ Λ),
  β ≫ γ = α`. Morphisms in CommAlgCat are exactly R-algebra homomorphisms;
  categorical composition β ≫ γ is the underlying algebra-map composition γ ∘ β.
- A small filtered category J: `∃ (J : Type (max u v + 1))
  (_ : SmallCategory J) (_ : IsFiltered J)`. Filteredness includes nonemptiness,
  common targets for pairs of objects, and equalization of parallel arrows.
- A diagram of commutative R-algebras: `D : J ⥤ CommAlgCat.{max u v} R`.
- Each diagram object lies in E: `∀ j : J, D.obj j ∈ E`.
- R-algebra coprojections to Λ and compatibility:
  `ι : D ⟶ (Functor.const J).obj Λ`; its components are the required ι_j,
  and naturality imposes `D.map a ≫ ι.app j = ι.app i` for a : i ⟶ j.
- The specified cocone with vertex Λ is a colimit:
  `Nonempty (IsColimit (Cocone.mk Λ ι))`. IsColimit is data in Type, so
  Nonempty asserts existence of this universal-property witness in Prop.
  Its desc, fac, and uniq fields give exactly existence and uniqueness of
  the compatible map Λ → M for every other cocone.

Dependency used: `def-weil-pbc-category-colimit` records
`Mathlib.CategoryTheory.Limits.HasLimits`, with `CategoryTheory.Limits.colimit`,
`CategoryTheory.Limits.Cocone`, `CategoryTheory.Limits.IsColimit`, and
`CategoryTheory.IsFiltered`. Here the specified vertex Λ is retained by
`Cocone`/`IsColimit`, rather than asserting only an isomorphism with a chosen
colimit. Their full definitions/docstrings were read in Limits/Cones.lean,
Limits/IsLimit.lean, Limits/HasLimits.lean, and Filtered/Basic.lean. The limits
modules are transitively imported through CommAlgCat.Basic; Filtered.Basic
is imported explicitly. Additional standard Mathlib notions used are
`CommAlgCat`/its categorical morphisms (Algebra/Category/CommAlgCat/Basic.lean)
and `Algebra.FinitePresentation` (RingTheory/FinitePresentation.lean).

Edge cases checked before writing: E = ∅ cannot satisfy the factorization
hypothesis, since R itself is finitely presented and has its structural map
into Λ. Thus the nonempty index conclusion does not introduce an unspoken
assumption. Zero rings and zero algebras are allowed: no Nontrivial binder
appears. Presentations with no variables or no relations are allowed by
Algebra.FinitePresentation. No Noetherian, characteristic, finite-type-only,
or smoothness hypothesis is imposed. There is no assumption that Λ itself
is finitely presented. The two universes permit an arbitrary base ring and
algebras in any containing universe. The set of bundled algebras lives in
Type (max u v + 1), so the full subcategory on pairs (B in E, B → Λ)
is small in that universe without a further ObjectProperty.Small assumption
on E. SmallCategory at that level may lift hom types; it does not restrict
the underlying mathematical category. Any given set of rings and maps can
be placed in these universes, so no set-sized case is excluded.

Searches for an existing statement (2026-10-11):

- msearch.py leansearch: "Every map from a finitely presented commutative algebra
  factors through a member of E implies filtered colimit of members of E".
  Service unavailable (Internal Server Error), recorded as unavailable.
- msearch.py leanfinder: "An algebra is a filtered colimit of a set of finitely
  presented algebras if every map from a finitely presented algebra factors
  through a member of that set". Eight hits, mainly
  RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit,
  RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit,
  CommRingCat.preservesFilteredColimits_coyoneda, and categorical finite
  presentability lemmas: they give the other direction or component notions.
- msearch.py loogle: "CategoryTheory.ObjectProperty.ind_iff_exists,
  Algebra.FinitePresentation". Zero hits.
- msearch.py grep: `ind_iff_exists|07C3|factorization.*colimit`, CategoryTheory.
  Found ObjectProperty.ind_iff_exists and MorphismProperty.ind_iff_exists.
  The full signature/docstring and proof of the former were read: it requires
  IsFinitelyAccessibleCategory and categorical finite presentability, so it
  does not state this algebra-specific lemma with just the node's hypotheses.
- rg in WeilConjectures and lean/Sheaf for
  `factorization.*colimit|ind_iff_exists|07C3|lem-weil-pbc-factorization-criterion-filtered-colimit`:
  only a proof-docstring citation in Sheaf/RingTheory/IndStandardSmooth.lean;
  no existing declaration of this criterion. The required grep by node id
  in WeilConjectures returned no hit. A broader rg for factorization, 07C3,
  and ind_iff_exists gave unrelated factorization statements.
- rg of the proposed declaration name and two plausible variants in
  dag/lean_names_upstream.json, Mathlib, WeilConjectures, and lean/Sheaf
  returned no name collision.

Validation: scompile.py compiled the single module cleanly on the server in
1.4 seconds, exit code 0, with no errors or warnings. All variables and
universes are explicitly bound. There are no disputed statements or node faults.
The independent second reading is left to the second reader, as instructed.

## Second reading by J1

I independently opened the node copy and `FilteredColimitOfFactorization.lean`,
then the sole statement dependency `def-weil-pbc-category-colimit` and the actual
Mathlib declarations it records. I read the official Stacks Tag 07C3 page and
`algebra.tex` at `lemma-when-colimit`, including its proof and the chapter's
Conventions section, from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
(the local Stacks checkout is absent). Rings there are commutative with identity,
including the zero ring. No extra standing hypothesis applies. The node is precisely
the implication (2) implies (1), not the converse or the full equivalence.

The object/hypothesis/conclusion list, matched in order:

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` | Exact; identity allowed to equal zero. |
| Commutative R-algebra Λ | `(Λ : CommAlgCat.{max u v} R)` | Exact; the bundle carries CommRing and Algebra R. |
| Set E of commutative R-algebras | `(E : Set (CommAlgCat.{max u v} R))` | Exact; actual membership, with no closure under isomorphism assumed. |
| Every member of E has finite presentation | `hfp : ∀ B ∈ E, Algebra.FinitePresentation R B` | Exact; the class's `out` specifies a surjection from `MvPolynomial (Fin n) R` with FG kernel, equivalent to the stated finite presentation by generators and relations. |
| Every finitely presented A | `∀ (A : CommAlgCat.{max u v} R), Algebra.FinitePresentation R A →` in `hfactor` | Exact; no finite presentation requirement on Λ. |
| Every R-algebra map α from A to Λ | `∀ (α : A ⟶ Λ)` | Exact; CommAlgCat.Hom wraps AlgHom, not a bare ring map. |
| Some B in E and maps β, γ with γ ∘ β = α | `∃ B, B ∈ E ∧ ∃ (β : A ⟶ B) (γ : B ⟶ Λ), β ≫ γ = α` | Exact, including quantifier order; categorical composition is γ.hom.comp β.hom. |
| Some small filtered category J | `∃ (J : Type (max u v + 1)) (_ : SmallCategory J) (_ : IsFiltered J)` | Exact; IsFiltered includes nonemptiness, common targets, and equalization. |
| Diagram j ↦ B_j of R-algebras, all in E | `D : J ⥤ CommAlgCat.{max u v} R` and `∀ j : J, D.obj j ∈ E` | Exact; the functor also supplies all transition maps and laws. |
| Compatible coprojections B_j → Λ | `ι : D ⟶ (Functor.const J).obj Λ` | Exact; naturality is `D.map a ≫ ι.app j = ι.app i` for a : i → j. |
| The cocone (Λ, ι) is a colimit in R-algebras | `Nonempty (IsColimit (Cocone.mk Λ ι))` | Exact; existence of desc and its fac/uniq fields is precisely the stated universal property. |

Dependency verification: I read `CommAlgCat.Basic` (bundle, Hom, category
composition), `FinitePresentation` (class definition), `Limits/Cones` (Cocone),
`Limits/IsLimit` (IsColimit), `Filtered/Basic` (IsFilteredOrEmpty and IsFiltered),
and `Category/Basic` (SmallCategory). The dependency's recorded Cocone/IsColimit
and filteredness declarations are exactly the notions used. IsColimit is data,
so Nonempty is necessary to express the universal property in the theorem's Prop.
There is no substitute colimit notion and no missing dependency module.

Edge cases: E = ∅ makes the hypothesis impossible: a universe-lifted copy of R
is finitely presented and has its structural R-algebra map to Λ. Consequently
the nonempty filtered index is justified even in this case. Zero base rings
and zero algebras are included; there is no Nontrivial hypothesis. Empty schemes
are inapplicable to this algebra statement. Presentations with n = 0 and with
zero relations are included by Fin n and FG (including the zero ideal).
Characteristic is unrestricted. There are no field, Noetherian, or finite-type
substitutions. With w = max u v, all algebra carriers have a universe containing
R; any particular set-sized family can be placed in such a w. The type of
bundled algebras, and hence the set-indexed category of pairs (B, B → Λ), is in
Type (w + 1). Its hom types can be lifted to w + 1 to give SmallCategory.
Thus the conclusion's universe bound accommodates the construction without an
unspoken smallness assumption on E. All binders and both universes are explicit.

Independent searches on 2026-10-11 (queries differ from the first reader's):

- LeanSearch via msearch: "Factorization through a prescribed set of finitely
  presented commutative R algebras characterizes filtered colimits of that set".
  Service unavailable (Internal Server Error); no negative verdict inferred.
- LeanFinder via msearch: "A commutative R-algebra is a filtered colimit of
  algebras in a set if all morphisms from finitely presented R-algebras factor
  through that set". Eight hits: finite-presentation factorization through an
  already supplied filtered colimit and CommRingCat filtered-colimit constructions;
  none gives this converse criterion for a prescribed set of R-algebras.
- Loogle via msearch: `CommAlgCat, CategoryTheory.IsFiltered`: zero hits.
- Mathlib grep via msearch: `IsFinitelyAccessibleCategory|ind_iff_exists|07C3`
  in CategoryTheory: thirteen hits. I opened ObjectProperty.ind_iff_exists and
  its proof: the categorical criterion requires IsFinitelyAccessibleCategory
  and categorical finite presentability, so it is not this exact statement
  under the supplied algebraic hypotheses. MorphismProperty.ind_iff_exists is
  the corresponding Under-category result, not a match either.
- Independent rg on all Mathlib for `07C3|when-colimit|exists_filtered_colimit_of_factorization|ind_iff_exists`
  finds only the categorical ind criteria. I also opened
  Algebra/Category/Ring/FinitePresentation: it concerns factoring maps through
  a given colimit, the reverse direction here.
- Independent rg on WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `07C3|exists_filtered_colimit_of_factorization|filtered.*colimit.*factor|factor.*filtered.*colimit|ind_iff_exists`
  gives only unrelated/documentation references, including the intended use in
  IndStandardSmooth. No exact existing theorem or proposed-name collision.

H5/H6/H8/H9: there are no definitions, auxiliary proved facts, or private copies.
The sole theorem proof is `by sorry`. Header, namespace and all three imports
serve the statement. Module and theorem docstrings carry the correct source
and blueprint id. The theorem docstring reproduces all four node proof steps:
the representative category P₀ ∪ E; its full subcategory on E and factorization;
the dual cofinality argument; transport of the colimit and its universal property.
No correction, new node, dependency module, or disputed statement is needed.
No Lean or node mismatch was found, so their correct contents were preserved;
this reading adds only this review section and fresh search records.

Second-reader validation: scompile.py compiled the unchanged 61-line module
cleanly on the server in 1.4 seconds, exit code 0, no errors or warnings.
A literal signature comparison confirms lean.statement equals the declaration
up to := verbatim. Every Lean line is at most 100 characters.

## Reviewer fix (R-fcf1004)

The delivered conclusion took the index category in `Type (max u v + 1)`, one universe
above the algebras. That weakens "a small filtered category J": small relative to
`CommAlgCat.{max u v} R` means objects in `Type (max u v)` (the convention of the landed
sibling lem-weil-pbc-algebra-colimit-fp-algebras-over-it, `ObjectProperty.Small.{max u v}`
/ `Small.{max u v}`), and the consumer lem-weil-pbc-colimit-standard-smooth-algebras needs
`ObjectProperty.ind.{max u v}`, which the `+ 1` index cannot feed. The stronger form holds
without any smallness assumption on `E`: finitely presented algebras have a small set of
isomorphism classes, so a subset `E' ⊆ E` of representatives gives a `max u v`-small full
subcategory that the factorization hypothesis still reaches (compose with an isomorphism).
Fix: `J : Type (max u v)`; docstring and proof steps 1-2 now use the representatives `E'`
(also needed for `P = P₀ ∪ E'` to satisfy the smallness binder of the 0BUF statement).
All other binders and clauses are as delivered. Recompiled cleanly.
