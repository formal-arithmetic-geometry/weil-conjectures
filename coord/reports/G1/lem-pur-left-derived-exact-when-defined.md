## Worker report

`Sheaf.CategoryTheory.LeftDerivedExactWhenDefined` states
`CategoryTheory.Functor.leftDerived_exact_when_defined`, with a single `sorry`.
No definition node or dependency module is needed; the node is unchanged outside `lean`.

Hypothesis and clause correspondence:
- `D` and `D'` have explicit category, zero object, additive integer shift,
  preadditive, pretriangulated, and `CategoryTheory.IsTriangulated` binders.
  These are exactly the triangulated categories of `def-weil-triangulated-category`.
- `F : D ⥤ D'` with `F.CommShift ℤ` and `F.IsTriangulated` is the exact functor.
  Mathlib obtains its additivity from its triangulated instance.
- `S : MorphismProperty D` with `hS : S.IsSaturatedTriangulatedMultiplicativeSystem`
  is precisely the recorded MS1--MS6 notion.
- `L` is the abstract localization category, with its induced triangulation;
  `Q : D ⥤ L`, `Q.CommShift ℤ`, and `Q.IsTriangulated` specify that induced structure
  rather than an unrelated triangulation on the localized underlying category.
  This is the localization triangulation of Proposition 05R6 used in proof step 5.
- `hQ : Q.IsStrictLocalizationAt S` is the dependency's universal property on
  functors and natural transformations. The derived-category specialization
  requires no separate abelian-category binder in this general theorem.
- `hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X` is exactly
  essential constancy of the pro-diagram at every object, as Definition 05S9 says.
- `LF : L ⥤ D'`, `α : Q ⋙ LF ⟶ F`, and `hLF : LF.IsRightKanExtension α`
  characterize the candidate by the universal equation: every transformation
  `Q ⋙ G ⟶ F` factors uniquely through `α`.
- `∃ (_ : LF.CommShift ℤ), LF.IsTriangulated` supplies both shift compatibility
  and preservation of distinguished triangles, hence exactness. No shift
  structure on `LF` is assumed.

Dependencies read and used: the recorded declarations
`CategoryTheory.MorphismProperty.IsSaturatedTriangulatedMultiplicativeSystem`,
`CategoryTheory.Functor.IsStrictLocalizationAt`, and
`CategoryTheory.Functor.IsTriangulatedLeftDerivedDefinedAt` in
`Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` (read its full
module, including the underlying value definition). Mathlib predicates from
`CategoryTheory/Triangulated/Pretriangulated.lean`, `Triangulated.lean`, and
`Functor.lean` render the triangulated-category leaf. The full signature and
reference docstrings of `DerivedCategory`, `DerivedCategory.Q`, and
`HasDerivedCategory` in `Algebra/Homology/DerivedCategory/Basic.lean` were read:
this theorem applies to that specialization but is not limited to it.
`Functor.IsRightKanExtension` in `Functor/KanExtension/Basic.lean` is the existing
universal notion, imported directly (terminal right-extension object).

Edge cases: independent object and morphism universes are explicit for all three
categories; the zero category and zero functor are included. A literally empty
category cannot be triangulated because a zero object is part of that notion.
No restriction on denominators or on objects is added. Integer shifts include
zero and negative shifts. `LF` gets its shift structure in the conclusion.

Searches made:
- `msearch.py G1 lem-pur-left-derived-exact-when-defined leanfinder
  "everywhere defined left derived functor exact triangulated"`: eight hits,
  including `Functor.IsLeftDerivedFunctor` and exact-abelian-functor derived
  category instances; none states arbitrary triangulated-localization exactness.
- `msearch.py ... loogle "Functor.IsLeftDerivedFunctor, Functor.IsTriangulated"`:
  zero hits, unknown identifier `Functor.IsLeftDerivedFunctor`.
- `msearch.py ... grep "IsTriangulated|LeftDerived" CategoryTheory/Functor/Derived`:
  17 hits, derived predicates and Kan-extension infrastructure, no exactness theorem.
- `rg` on `WeilConjectures`, Mathlib, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `leftDerived_exact_when_defined`, the item id, and
  `IsTriangulatedLeftDerivedDefinedAt`: no duplicate statement or name; the landed
  resolving-class theorem cites this item in its docstring and does not state it.
  The recorded dependency supplies the pointwise definition without duplication.

Source checked online because the local Stacks checkout is absent:
[Definition 05S9](https://stacks.math.columbia.edu/tag/05S9) and
[Proposition 05SE](https://stacks.math.columbia.edu/tag/05SE). The latter's
left-derived analogue gives exactness on the localization of its defined locus;
with everywhere-defined values the locus is all of `D`.
The declaration docstring carries all five proof steps and their DAG ids.

Validation: server single-file compilation succeeds with no errors or warnings.
The second reading is left to the separate reader as requested; no second-reading
section has been written by this worker.

## Second reading by G1

I read the node, its source place (Stacks Tags 05S9 and 05SE), the worker module, and all recorded statement dependencies. The correspondence is as follows.

- The node's triangulated categories `D` and `D'` render as the explicit category, zero object, integer shifts, preadditivity, additive shifts, `Pretriangulated`, and `CategoryTheory.IsTriangulated` binders for `D` and `D'`. No extra finiteness, Noetherian, characteristic, or universe restriction is imposed.
- The exact functor `F : D ⥤ D'` renders as `F` with `[F.CommShift ℤ] [F.IsTriangulated]`; these are the shift compatibility and distinguished-triangle preservation required by the node.
- The saturated triangulated multiplicative system renders as `S : MorphismProperty D` and `hS : S.IsSaturatedTriangulatedMultiplicativeSystem`, using the recorded declaration in `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`.
- The abstract localization renders as the triangulated category `L` with its full structure, `Q : D ⥤ L` with `[Q.CommShift ℤ] [Q.IsTriangulated]`, and `hQ : Q.IsStrictLocalizationAt S`. This supplies the node's induced localization triangulation and universal property; it adds no unrelated hypothesis.
- The everywhere-defined hypothesis renders as `hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X`, exactly the recorded Definition 05S9 notion (essential constancy at every object).
- The candidate derived functor and its universal characterization render as `LF : L ⥤ D'`, `α : Q ⋙ LF ⟶ F`, and `hLF : LF.IsRightKanExtension α`, matching the right Kan universal equation for a transformation from `Q ⋙ G` to `F`.
- The conclusion renders as `∃ (_ : LF.CommShift ℤ), LF.IsTriangulated`, giving shift compatibility and exactness of `LF` as required.

The quantifier order is preserved, and the explicit universes cover all cases. Edge cases checked include zero categories and zero functors, `n = 0` and negative integer shifts, empty denominator systems (subject to the stated localization hypotheses), and arbitrary object and morphism universes. A literally empty category is correctly excluded by the required zero-object and category structures. No hollow definition or additional hypothesis occurs; the sole proof is the named `sorry` required for a statement node, and all declaration docstrings cite the Stacks source and `(blueprint: lem-pur-left-derived-exact-when-defined)`.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` with `msearch.py` (LeanFinder, Loogle, and grep queries for everywhere-defined left-derived exactness, `leftDerived_exact_when_defined`, and `IsTriangulatedLeftDerivedDefinedAt`). The hits are derived-functor infrastructure and exact-functor instances, not this general theorem; no duplicate declaration exists.

No mismatch was found, so no Lean or node statement change was required. The module compiles cleanly with `scompile.py` (no errors or warnings).
