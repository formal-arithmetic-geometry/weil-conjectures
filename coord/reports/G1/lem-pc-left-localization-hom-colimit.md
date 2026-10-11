## Worker report

`CategoryTheory.localization_hom_colimit` states that the canonical colimit map for a
left localization is a bijection. Its proof is `sorry`.

- The category and its Hom universe are `{C : Type u} [Category.{v} C]`.
- The left multiplicative system is `(S : MorphismProperty C)
  [S.HasLeftCalculusOfFractions]`; this is Mathlib's formulation of the Stacks
  left multiplicative system (LMS1--LMS3).
- The localization is `(Q : C ⥤ D) [Q.IsLocalization S]`, with arbitrary target
  category `{D : Type u'} [Category.{v'} D]`.
- The two objects are `(X Y : C)`; denominators out of `X` are objects of
  `S.Under ⊤ X`. The `⊤` permits every commuting triangle as a transition.
- The diagram is the composite of the two forgetful functors with
  `(uliftCoyoneda.{u} (C := C)).obj (Opposite.op Y)`. Thus its value at a
  denominator `s : X ⟶ I` is `ULift (Y ⟶ I)`, and its maps postcompose.
  `ULift` only places the ordinary Hom set in a universe large enough for the
  colimit; it does not change its elements or identifications.
- `∃ e : colimit ... ≃ (Q.obj Y ⟶ Q.obj X)` asserts bijectivity. The following
  universal equation identifies `e` as the canonical map: for every `s` and
  `f : Y ⟶ s.right`, it sends `colimit.ι ... s (ULift.up f)` to the image of
  `LeftFraction.mk f s.hom s.prop`, namely `Q.map f ≫ inv (Q.map s.hom)`.
  The colimit transitions identify representatives after later denominators.

Dependency: `def-weil-abstract-derived-category` is the Mathlib leaf
`Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`; the item
uses its underlying general localization interface through
`Mathlib.CategoryTheory.Localization.CalculusOfFractions`,
`Functor.IsLocalization`, `Localization.inverts`, and
`MorphismProperty.LeftFraction.map`. The denominator category comes from
`Mathlib.CategoryTheory.MorphismProperty.Comma`, `MorphismProperty.Under`.

Edge cases: the identity denominator exists by LMS1, so the index is never
empty for an object `X`; an identity-only system reduces to the ordinary
Hom bijection. Empty Hom sets and empty categories are allowed; no nonempty
object or Hom hypothesis appears. The chosen `Type (max u v)` contains the
index and Hom universes, and the result permits any target Hom universe.

Searches: `msearch.py leanfinder` for "morphisms in a left localization are a
colimit of Hom sets over denominators" found `Localization.exists_leftFraction`
and fraction results, no colimit theorem. `msearch.py loogle` for
`CategoryTheory.Localization, LeftFraction, HasLocalization` returned no hit
(unknown `CategoryTheory.Localization`). `msearch.py grep` for
`leftFraction|left.localization|Hom.*colimit` found fraction and unrelated
colimit declarations, no exact match. `rg` over Mathlib's
`CategoryTheory/Localization`, the source's `WeilConjectures`, and the
project's `lean/Sheaf` found no Hom-colimit declaration. Literal `grep -rn`
for the item id in the source found no occurrence.

Stacks Categories Tag 05Q0, Remark 4.27.7, was checked: it uses arbitrary
arrows between denominators and states the same filtered colimit formula.

## Earlier second reading (a previous round; superseded)

Pending independent second worker review.

## Second reading by G1

- Category: `{C : Type u} [Category.{v} C]` is the arbitrary category of
  Stacks Tag 05Q0. Verdict: exact; no abelian, additive, or size restriction.
- Left multiplicative system: `(S : MorphismProperty C)
  [S.HasLeftCalculusOfFractions]` supplies LMS1, LMS2, and LMS3 of the
  source's definition. Verdict: exact.
- Localization: `{D : Type u'} [Category.{v'} D] (Q : C ⥤ D)
  [Q.IsLocalization S]` presents the source localization by an arbitrary
  equivalent target. The Hom set is `(Q.obj Y ⟶ Q.obj X)`.
  Verdict: exact up to the canonical equivalence of localizations.
- Objects: `(X Y : C)` are the source denominator object and the source
  numerator object, respectively. Verdict: exact, including their order.
- Denominators and transitions: `s : S.Under ⊤ X` is an arrow `X ⟶ I` in
  `S`; `⊤` allows every commuting triangle as in the source's `X/S`.
  Verdict: exact. The identity denominator makes the index nonempty.
- Diagram: `MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X` takes a
  denominator to `I`; composing with `(uliftCoyoneda.{u} (C := C)).obj
  (Opposite.op Y)` gives `ULift (Y ⟶ I)` and postcomposition on arrows.
  `ULift` changes only the universe, not the represented morphisms or
  their colimit identifications. Verdict: exact.
- Bijection: `∃ e : colimit ... ≃ (Q.obj Y ⟶ Q.obj X)` asserts both
  injectivity and surjectivity. The following `∀ s f` equation fixes it as
  the canonical map: `colimit.ι ... s (ULift.up f)` goes to
  `(MorphismProperty.LeftFraction.mk f s.hom s.prop).map Q
  (Localization.inverts Q S)`, namely `Q(f) ≫ (Q(s))⁻¹`.
  Verdict: exact; quantifiers and fraction orientation agree with Tag 05Q0.

Edge cases: an empty category has no `X Y`, and the statement is vacuous;
for any `X`, LMS1 supplies the identity denominator, so its index is not
empty. Empty ordinary Hom sets remain valid type values, and an
identity-only system gives the usual Hom bijection. Zero objects, schemes,
integers `n`, and field characteristic are not parameters here. The four
independent universes `u v u' v'` allow arbitrary category and target Hom
sizes; `uliftCoyoneda.{u}` makes the type-valued colimit large enough for
the denominator index.

Independent searches: `msearch.py leanfinder` with "filtered colimit of
representable Hom sets localization calculus of fractions" found
`LeftFraction.Localization.instIsLocalizationQ` and general localization
results, but no Hom-colimit identification. `msearch.py loogle` with
"MorphismProperty.LeftFraction colimit" found no result (the query was
not recognized). `msearch.py grep` with "localization hom colimit" found
no result. `rg` over Mathlib's CategoryTheory/Localization, the source
repository's WeilConjectures, and this project's lean/Sheaf found no exact
statement. I read Mathlib's `MorphismProperty.Under` and
`HasLeftCalculusOfFractions` signatures directly; the latter's fields
match Stacks LMS1--LMS3. The only `stmt_deps` node,
`def-weil-abstract-derived-category`, is a Mathlib leaf for derived
localization; this general lemma uses Mathlib's localization interface
directly and needs no private dependency module.

Mismatch found: none. The module and node were left unchanged. The
source formula in Categories Tag 05Q0 and the fifth equality in Derived
Categories Tag 0FND agree with the Lean statement. The declaration's
docstring follows the node's construction, surjectivity, injectivity, and
bijection steps. Its only proof is `sorry`, and the single-file compile
completed with no errors or warnings.
