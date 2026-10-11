## Worker report

The module states `AlgebraicGeometry.singleComplexInheritedTensorCondition` for a cartesian
square of schemes. Its hypotheses render the common derived-category universe and derived
category instances, the four morphisms and `IsPullback` square, quasi-coherent derived objects
`K` and `K'`, a map `φ : L(g')^*K ⟶ K'`, and the stalkwise hypothesis
`SingleComplexBaseChange.StalkCondition ... K.obj K'.obj φ`. The conclusion quantifies over a
monoidal structure on `derivedPullback g'` and every quasi-coherent `E`; it applies the stalk
condition to `E.obj ⊗ K.obj`, `L(g')^*E.obj ⊗ K'.obj`, and the induced map
`(Functor.Monoidal.μIso ...).inv ≫ (L(g')^*E.obj ◁ φ)`. The inverse tensorator is the canonical
comparison from the tensor of pullbacks to the pullback of a tensor, and whiskering applies the
given map on the second factor.

The dependency declarations used are `Sheaf.AlgebraicGeometry.DerivedCategory`'s
`AlgebraicGeometry.schemeDerivedCategory` and `schemeDerivedQCohCategory`,
`Sheaf.AlgebraicGeometry.DerivedPullback`'s `AlgebraicGeometry.derivedPullback`,
`Sheaf.AlgebraicGeometry.BaseChangeConventions`'s base-change conventions, and
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`'s
`AlgebraicGeometry.SingleComplexBaseChange.StalkCondition`; the latter is the direct recorded
statement dependency for the stalkwise condition. The monoidal notation and tensorator are
Mathlib/WeilConjectures `CategoryTheory.Functor.Monoidal` declarations, with the project
`schemeDerivedTensorMonoidal` instance imported from `DerivedTensorStructure`.

Edge cases checked: the index `i : ℤ` and every point are retained by `StalkCondition`; `E` may
be the zero object; no nonemptiness, boundedness, perfectness, or quasi-compactness hypothesis
is added; arbitrary scheme universes are represented by one explicit `u`; the monoidal
structure is an explicit typeclass parameter because the chosen derived pullback carries no
canonical structure declaration in the current library.

Searches for an existing declaration: `msearch.py leanfinder` query “derived base change stalk
condition inherited tensor arbitrary complex” (generic base-change hits only, no match);
`msearch.py loogle` query “DerivedCategory, tensorObj” (0 hits); `msearch.py grep` query
“base.change.*tensor|tensor.*baseChange” (0 matches); `msearch.py leansearch` query
“canonical derived pullback tensor comparison sheaves modules” (service unavailable); `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this theorem. The source was checked
at Stacks Tag 0DJA, Lemma 36.26.3(1), whose conclusion is exactly inheritance under tensoring
by `E`.

STATEMENT-DISPUTED: E1 (15:46) "corrected node drops arbitrary K' and the morphism required by
Stacks 0DJA(1)". That reason describes a correction E1 considered, not the node: the node as written
keeps K' arbitrary with a map L(g')^*K → K' and is Stacks 0DJA(1) (perfect.tex 6607-6624;
coord/HUMAN.md item 2, proposed correction none). Delivered as written, no correction.

## Second reading by C1

I read the node statement against Stacks Tag 0DJA, Lemma 36.26.3(1), and then matched
it with `Sheaf/AlgebraicGeometry/SingleComplexInheritedTensorCondition.lean`.

* The cartesian square and its four objects and arrows are rendered by
  `X X' S S' : Scheme.{u}`, `f : X ⟶ S`, `f' : X' ⟶ S'`, `g : S' ⟶ S`,
  `g' : X' ⟶ X`, and `sq : IsPullback g' f' f g`.  Verdict: exact, including the
  cartesian hypothesis.
* The common derived-category universe and the derived-category instances are
  rendered by `universe u w` and
  `[∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]`.  Verdict: this is the
  shared carrier and instance required by `schemeDerivedQCohCategory`; no
  Noetherian, boundedness, perfectness, or quasi-compactness assumptions are
  added, and the same scheme universe is used throughout.
* `K ∈ D_QCoh(O_X)` and `K' ∈ D_QCoh(O_X')` are rendered by
  `K : schemeDerivedQCohCategory X` and `K' : schemeDerivedQCohCategory X'`;
  their underlying derived objects are explicitly `K.obj` and `K'.obj`.
  Verdict: exact full-subcategory objects, including the zero object.
* The given map `L(g')^*K ⟶ K'` is rendered by
  `φ : (derivedPullback g').obj K.obj ⟶ K'.obj`.  Verdict: exact derived
  pullback map with no extra property.
* The hypothesis that for every `x'` and `i : ℤ` the canonical stalk
  comparison is an isomorphism is rendered by
  `h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq
  K.obj K'.obj φ`.  Verdict: this dependency expands to all coordinates,
  points, and integer degrees and is the recorded canonical comparison, so no
  point or degree is omitted and no stronger hypothesis is imposed.
* The conclusion's arbitrary `E ∈ D_QCoh(O_X)` is rendered by
  `∀ [m : Functor.Monoidal (derivedPullback g')] (E :
  schemeDerivedQCohCategory X)`.  Verdict: arbitrary `E`, including zero;
  the explicit monoidal structure supplies the tensor comparison used by the
  induced map and does not restrict `E`.
* The target objects are rendered as
  `(E.obj ⊗ K.obj)` and
  `((derivedPullback g').obj E.obj) ⊗ K'.obj`.  Verdict: these are exactly
  `E ⊗^L K` and `L(g')^*E ⊗^L K'` in the project's derived tensor structure.
* The induced arrow is rendered as
  `(Functor.Monoidal.μIso (derivedPullback g') E.obj K.obj).inv ≫
  ((derivedPullback g').obj E.obj ◁ φ)`.  Verdict: the inverse tensorator
  identifies `L(g')^*(E ⊗^L K)` with `L(g')^*E ⊗^L L(g')^*K`, followed by
  whiskering with the given `φ`; this is the canonical arrow in Tag 0DJA(1).
* The conclusion applies the same condition with
  `SingleComplexBaseChange.StalkCondition ...`; verdict: it quantifies over
  every point and every integer degree through the dependency, exactly as the
  node requires.

Edge cases were checked explicitly: the index of degrees is all `ℤ` (including
zero and negative degrees), `E` and `K` may be zero, no point-set nonemptiness is
assumed, and arbitrary scheme universes are represented by the explicit `u`.
The empty scheme and empty open sets are not excluded by any hypothesis.  The
characteristic is unrestricted.

I searched the source checkout, project `lean/Sheaf`, Mathlib search tools, and
`msearch.py` using derived base-change/tensor/stalk-condition queries.  No
existing declaration states this theorem; the only relevant declaration is the
recorded dependency `SingleComplexBaseChange.StalkCondition`.  I also checked
that `schemeDerivedQCohCategory`, `derivedPullback`, and the base-change
conventions used here are precisely the declarations recorded by their
statement dependencies.

No mismatch was found, so no Lean or node correction was needed.  The module
compiled cleanly with `lcompile.py`; its sole proof remains `sorry`, as required
for a stage-2 statement.

## Reviewer R-itc (stage 2)

Statement checked against the node as written (0DJA(1)); no group alteration. Fix: the
conclusion quantified over every `Functor.Monoidal (derivedPullback g')` with nothing asserting
one exists, so it was vacuous until a monoidal structure is constructed; added
`Nonempty (Functor.Monoidal (derivedPullback g')) ∧`, as in the landed siblings
SmoothProperTensorPerfectCase and SmoothProperDiagonalTensorFormula (Stacks 079U). Added the
STATEMENT-DISPUTED line required for the unparked disputed items.
