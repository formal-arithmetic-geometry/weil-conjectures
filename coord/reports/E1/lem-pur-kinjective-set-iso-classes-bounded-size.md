## Worker report

Module: `Sheaf.CategoryTheory.BoundedSubobjectSize`.
Declaration: `CategoryTheory.bounded_subobject_size_quotient_and_small_iso_classes`.
The two conclusions are one conjunction, with one `sorry` proof and no new definitions.
The node is unchanged except for its `lean` record. No missing notions, unusable dependencies,
statement corrections or disputed statements were found.

Source checked: Stacks Project `injectives.tex`, Lemma `lemma-set-iso-classes-bounded-size`,
lines 1398–1414 of the upstream source, fetched read-only from
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex .
The literature checkout is absent on this machine. The source states both clauses exactly
as the node does, and supplies the generator/coproduct proof.

Hypothesis and clause correspondence:

- A category A: `{C : Type u} [Category.{v} C]`, with independent explicit universes `u v`.
- Grothendieck abelian: `[Abelian C] [IsGrothendieckAbelian.{v} C]`. This is the dependency's
  Mathlib match at its prescribed small-set universe `v`; small coproducts and small subobjects
  follow from the recorded definition, without extra hypotheses.
- Specified generator U: `(U : C) (_hU : IsSeparator U)`. The underscore avoids unused-binder
  warnings for the proof placeholder and does not remove the generator assumption.
- A cardinal κ: `(κ : Cardinal.{v})`, no nonzero, infinite, or regular-cardinal restriction.
- Object size is number of subobjects: `Cardinal.mk (Shrink.{v} (Subobject M))`. Mathlib's
  `Subobject` already identifies monomorphisms by equivalence over M; Grothendieck well-poweredness
  gives its small model. Shrinking changes neither the subobjects nor their cardinality.
- Clause (1), every object of size at most κ: `∀ M : C, ... ≤ κ → ...`.
- At most κ copies of U: `∃ (I : Type v), Cardinal.mk I ≤ κ`, and the constant-family coproduct
  `(∐ fun _ : I ↦ U)`. This is the categorical direct sum in an abelian category.
- M is its quotient: `∃ p : (∐ fun _ : I ↦ U) ⟶ M, Epi p`. In an abelian category an epi
  identifies the target with the quotient by its kernel, so no chosen kernel is extra data.
- Clause (2), bounded-size isomorphism classes form a set:
  `Small.{v} (Skeleton (ObjectProperty.FullSubcategory (fun M : C ↦ ... ≤ κ)))`.
  The full subcategory contains exactly bounded-size objects, with all morphisms from C;
  its skeleton is the quotient by isomorphism. `Small.{v}` asserts the classes have a model
  in the small-set universe, even when C's objects live in a larger universe. It does not assert
  the objects themselves form a small set, or bound the number of classes by κ.

Dependency used: `def-sp-grothendieck-abelian` is a Mathlib leaf, recorded as
`CategoryTheory.IsGrothendieckAbelian` in
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`. Its full definition and docstring
were read: at `w = v` it means AB5 and a generator, and has small colimits as an instance.
Also read its `hasColimits` and `wellPowered` instances. Supporting Mathlib APIs read and used:
`CategoryTheory.IsSeparator` (Generator.Basic), `Subobject`, `Shrink`, `Cardinal.mk`,
`ObjectProperty.FullSubcategory` (ObjectProperty.FullSubcategory), `Skeleton` (Skeletal),
and `Small` (the EssentiallySmall import). Each import supplies terms used in the statement.

Edge cases checked before drafting: κ = 0 has no eligible objects because every subobject
lattice contains top, so clause (1) is vacuous and the bounded skeleton is empty. The zero
object has a single subobject, hence is eligible when κ ≥ 1; the empty coproduct maps epi
onto it, and no nonempty-index requirement is imposed. Finite κ and equality with the bound
are included by `≤`; no strict-cardinality surrogate or infinite-cardinal assumption is used.
A zero generator in the zero category is permitted. The object universe is unrestricted,
and `Shrink` removes the accidental large universe of `Subobject`, without restricting objects.
No variables or universes are auto-bound.

Searches (via `/home/ubuntu/weil-launcher/msearch.py`, group E1 and this item):

- LeanFinder: "objects with bounded cardinality of subobjects in Grothendieck category form
  a set of isomorphism classes". Eight hits, including WellPowered, subobject smallness,
  generating monomorphisms, and ObjectProperty.HasCardinalLT; no matching two-clause theorem.
- Loogle: `CategoryTheory.IsSeparator, CategoryTheory.Subobject`. Twelve hits on generating
  monomorphisms and related generator/subobject facts, not this theorem.
- Mathlib grep: `bounded.*size|cardinal.*Subobject|Subobject.*cardinal`, CategoryTheory.
  Eighteen hits: Subobject.HasCardinalLT and Grothendieck subobject cardinality results;
  none classify bounded-size objects or give the whole statement.
- LeanSearch: "Grothendieck category objects with bounded number of subobjects have a set
  of isomorphism classes". Service unavailable, Internal Server Error; no result assessed.
- Local `rg` across WeilConjectures, Mathlib, lean/Sheaf and dag/lean_names_upstream.json:
  this item's blueprint id and the proposed full declaration name have no hits.
- Local `rg` for `subobject.*[Cc]ardinal|[Cc]ardinal.*subobject|bounded.*[Ss]ize` found upstream
  `isCardinalGenerated_of_hasCardinalLT_subobject` and related covering statements. Read its
  signature and docstring: it proves a strict bound `< κ` and uses `isCardinalGenerated`,
  and does not include the isomorphism-class conclusion. Our statement uses the existing
  coproduct and cardinal APIs directly, without defining another generated-object notion.
- `rg` in lean/Sheaf for `Small.*Skeleton|Shrink.*Subobject|Cardinal.mk.*Subobject` found no
  matching theorem; searches for the candidate declaration name found no collision.

Validation: server single-file compile succeeded in 1.2 s, exit 0, no warnings. The final
Unicode-lambda formatting is checked again by the delivery dry run. The independent second
reading is left to the designated second reader; nothing is pushed by this worker.


## Second reading by E1

I independently read the node copy, its complete Lean module, the statement dependency
`def-sp-grothendieck-abelian`, and the Mathlib declarations used in the signature.
I read Stacks `injectives.tex`, section `section-grothendieck-categories`, through
`definition-size` and `lemma-set-iso-classes-bounded-size`, including its proof, from
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex.
The surrounding section introduces no additional hypotheses. Both source conclusions
agree with the node. No statement correction is present or needed.

Object/hypothesis/conclusion inventory and verdicts (H3):

1. An arbitrary category A: `{C : Type u} [Category.{v} C]`. Correct; independent
   object and morphism universes, with no restriction to small object collections.
2. A is Grothendieck abelian: `[Abelian C] [IsGrothendieckAbelian.{v} C]`. Correct.
   I opened the dependency node's recorded Mathlib match and read the class in
   `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`: at its prescribed
   `w = v`, local smallness is automatic, and its fields are exact filtered colimits
   (AB5) and a separator. Its `hasColimits` and `wellPowered` instances provide small
   coproducts and small subobject lattices. No additional instances are assumed.
3. A specified generator U: `(U : C) (_hU : IsSeparator U)`. Correct. I read
   `IsSeparator` in `Generator.Basic`: it says `Hom(U, -)` is faithful, the generator
   notion used here in an abelian category. The underscore has no logical effect.
4. An arbitrary cardinal kappa: `(κ : Cardinal.{v})`. Correct relative to the
   dependency's small-set universe v. There is no regularity, infinitude, positivity,
   or characteristic hypothesis; v itself is arbitrary.
5. For each object M, size is its number of subobjects:
   `Cardinal.mk (Shrink.{v} (Subobject M))`. Correct. I read `Subobject` as
   isomorphism classes of monomorphisms over M, and `Shrink` with `equivShrink`:
   this changes the universe of the model, not the subobjects or their cardinality.
6. Clause (1) quantifies all eligible M: `∀ M : C, ... ≤ κ → ...`. Correct,
   including equality; no strict-bound replacement.
7. Clause (1) permits at most kappa copies of this U:
   `∃ (I : Type v), Cardinal.mk I ≤ κ ∧ ...` and `(∐ fun _ : I ↦ U)`.
   Correct: arbitrary small index sets, including the empty set, and the categorical
   coproduct (the direct sum in this abelian category).
8. Clause (1) says M is a quotient: `∃ p : (∐ fun _ : I ↦ U) ⟶ M, Epi p`.
   Correct: in an abelian category an epimorphism presents its target as the
   quotient by its kernel; no chosen quotient presentation is an extra hypothesis.
9. Clause (2) says exactly the bounded-size isomorphism classes form a set:
   `Small.{v} (Skeleton (ObjectProperty.FullSubcategory
   (fun M : C ↦ Cardinal.mk (Shrink.{v} (Subobject M)) ≤ κ)))`.
   Correct. I read `FullSubcategory` (objects satisfying the predicate and all
   original morphisms), `Skeleton` (quotient by isomorphism), and `Small` (equivalence
   with a type in the indicated small universe). Thus it bounds neither the classes
   by kappa nor the actual objects by a small type. The conjunction includes both
   clauses for every kappa with the same fixed category and generator.

Edge cases: at kappa = 0, every subobject lattice has its identity/top subobject,
so the bounded predicate is empty; clause (1) is vacuous and clause (2) concerns
an empty skeleton. The zero object has one subobject and is included for kappa >= 1;
an empty coproduct may surject onto it. A zero generator is permitted for the zero
category. Finite bounds and equality are included. An empty category cannot satisfy
these hypotheses (U and an abelian zero object exist), as in the source. Schemes,
characteristic and an integer n do not occur, so no corresponding cases are excluded.
The object universe u is independent of v; well-poweredness supplies `Small.{v}`
without an extra binder. All variables and universes are explicitly bound.

Independent searches (H4), using different phrases from the first worker:

- LeanFinder via `msearch.py`: "A generator presents objects with few subobjects as
  epimorphic images of small coproducts". Eight hits on generating monomorphisms
  and regular-cardinal filtered generators; none states these two clauses.
- Loogle via `msearch.py`: `CategoryTheory.Skeleton, Small`. Five hits, including
  `small_skeleton_of_essentiallySmall` and `essentiallySmall_iff`. These describe
  the existing skeleton/smallness APIs, but do not establish essential smallness
  of this bounded subcategory. No duplicate of the theorem.
- Grep via `msearch.py`: `essentiallySmall.*[Ss]ubobject|[Ss]ubobject.*essentiallySmall|
  [Ss]mall.*[Qq]uotient`. Twenty-one hits, including the mono-over/subobject
  smallness equivalence and general quotient smallness; no two-clause theorem.
- LeanSearch: "The full subcategory of objects having a bounded number of subobjects
  is essentially small". Service unavailable (Internal Server Error); no verdict
  inferred from that failed search.
- Local `rg` across Mathlib, WeilConjectures and repository `lean/Sheaf` for
  bounded subobjects, generator quotients, small skeletons, and the proposed full
  declaration name: no exact statement or name collision. I opened upstream
  `CategoryTheory.isCardinalGenerated_of_hasCardinalLT_subobject` and its definition:
  they use strict bounds and do not state clause (2), so they are not this node.

Delivery audit: there is one theorem and no new definitions, new nodes, dependency
modules, hollow data, private copies, or proved lemmas. The theorem proof is solely
`sorry`. The module and theorem docstrings name the source and blueprint id, and
all three node proof steps are carried by the theorem docstring. Imports supply
used declarations; lines meet the 100-character convention. The recorded
`lean.statement` is verbatim the file signature, excluding `:= by`. No mismatches
were found; no Lean or node changes were necessary. This section is the only change.

Validation: the independent server single-file compile succeeded in 1.2 seconds,
exit 0 with no warnings. `deliver2.py --no-push` printed OK: preflight and compile
both passed. The final delivery repeats these checks before pushing.
