## Worker report

The module `Sheaf.CategoryTheory.DerivedFunctorShift` states
`CategoryTheory.Functor.isTriangulatedLeftDerivedDefinedAt_shift_iff`. It uses the
existing Situation 05S8 notions from
`Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`:
`Functor.IsTriangulatedLeftDerivedDefinedAt` and
`Functor.IsTriangulatedLeftDerivedValue`.

The binders `C`, `D` and their category, zero-object, shift, preadditive,
additivity, pretriangulated, and triangulated instances express the two
triangulated categories in Situation 05S8. `F`, `[F.CommShift ℤ]`, and
`[F.IsTriangulated]` express the exact functor. `S` and `hS` express the
saturated triangulated multiplicative system; `X` and `n : ℤ` are the object and
integer shift. The first conjunct is the iff between definedness at `X` and at
`(shiftFunctor C n).obj X`. The second conjunct says that whenever the value at
`X` is defined, for any values `Y` and `Y'` at `X` and its shift and any limit
cones `u`, `u'` on the denominator diagrams with these vertices, there is a unique
`e : (shiftFunctor D n).obj Y ≅ Y'` with `e.hom ≫ u'_(s[n]) = u_s[n] ≫
(F.commShiftIso n).inv.app s.left` for every denominator `s`: the canonical
shifted-value isomorphism (reviewer fix of a stale description of the earlier
`Nonempty` form).

The dependency declarations used (module
`Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`) are
`CategoryTheory.MorphismProperty.IsSaturatedTriangulatedMultiplicativeSystem`,
`CategoryTheory.Functor.IsTriangulatedLeftDerivedDefinedAt` and
`CategoryTheory.Functor.IsTriangulatedLeftDerivedValue`.

Edge cases checked: `n` is an arbitrary integer, including zero and negative
integers; no nonemptiness assumption is imposed on the denominator system or
objects; arbitrary universe levels are bound explicitly; zero objects and
the zero functor are permitted; the denominator category is never empty (MS1).

Searches for an existing statement or definition: `msearch.py leanfinder`
(query “left derived functor defined at X iff defined at shifted object and
canonical shift isomorphism”) found only generic shift instances and no
05SU statement; `msearch.py loogle` (query “CommShift, DerivedCategory.shiftIso,
leftDerivedFunctor”) was unavailable with zero hits; grep of Mathlib
`CategoryTheory` for `shiftIso|CommShift|derived.*shift` found no matching
left-derived shift theorem; `rg` over `lean/Sheaf` and the source
`WeilConjectures` found no existing 05SU statement. The dependency notion is
provided by the recorded declaration above.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: Situation 05S8 hypotheses are all bound,
and the statement has exactly the two requested clauses. Definedness is stated
in both directions for `X` and `X[n]`; under definedness, each pair of values is
related by an isomorphism from the shifted value to the shifted-object value.
The integer shift is arbitrary and the same `n` is used on source and target.
No hypotheses or conclusion clauses were added or omitted.

## Second reading by F1

Independent second reading against the node, the source, and the dependency
signatures. I read `derived.tex` on the server (local literature is not populated):
Situation `situation-derived-functor` (05S8), Definition
`definition-right-derived-functor-defined` (05S9), and Lemma
`lemma-derived-shift` (05SU), especially its second clause. The source assumes
only an exact functor of triangulated categories and a saturated compatible
multiplicative system. It states definedness in both directions and a canonical
isomorphism of the values. The node agrees with the source; no statement
correction, new definition node, or dependency module is needed.

Object/hypothesis/conclusion inventory and match:

1. The source category is a triangulated category. Lean's `C : Type u`,
   `[Category.{v} C]`, `[HasZeroObject C]`, `[HasShift C ℤ]`,
   `[Preadditive C]`, additive integer shifts, `[Pretriangulated C]`, and
   `[CategoryTheory.IsTriangulated C]` express exactly this structure. Pass.
2. The target category is another triangulated category, independently sized.
   The parallel binders for `D : Type uD` and `Category.{vD} D` give the same
   structure, with no abelian, smallness, finiteness, or enough-injectives
   hypothesis. Pass.
3. The exact functor is `F : C ⥤ D`, with `[F.CommShift ℤ]` and
   `[F.IsTriangulated]`. I read the Mathlib shift-isomorphism signature and
   triangulated-functor definition: the former provides the natural comparison
   from `F(X[n])` to `F(X)[n]`, and the latter preservation of distinguished
   triangles. No unrelated derived-functor notion is substituted. Pass.
4. The system is `S : MorphismProperty C` and
   `hS : S.IsSaturatedTriangulatedMultiplicativeSystem`. I opened
   `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` and its
   node `def-pur-saturated-triangulated-localization`. Its definition is the
   two calculi of fractions, the MS4 saturation implication, and Mathlib's
   `IsCompatibleWithTriangulation`, which extends integer-shift compatibility
   and has the MS6 triangle-completion field. These are the recorded
   Situation 05S8 notions, not a private multiplicative-system predicate. Pass.
5. The object and shift are `(X : C) (n : ℤ)`. The source's category is called
   D there; Lean's C is just a binder rename. The same integer is used in
   source and target shifts. Pass.
6. Definedness at X is equivalent to definedness at X[n]. The first conjunct
   is precisely `F.IsTriangulatedLeftDerivedDefinedAt S hS X ↔` the same
   predicate at `(shiftFunctor C n).obj X`. I opened that definition: it is
   existence of a value of the cofiltered denominator pro-diagram. Its value
   predicate uses `S.Over ⊤ X`, all commuting triangles, and the composite
   `MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F`. I also read
   `IsEssentiallyConstantProDiagram`: cofilteredness, natural cone legs,
   a retraction, and common-stage factorization. This is the source's
   essential constancy, not merely existence of a limit. Pass.
7. When defined, the values are canonically isomorphic from LF(X)[n] to
   LF(X[n]). The old second conjunct ended in bare `Nonempty (... ≅ ...)`;
   it did not characterize a canonical comparison and could be satisfied by
   any unrelated isomorphism of the underlying objects. H3 mismatch repaired.
   The corrected clause still quantifies over any two objects satisfying the
   recorded value predicates. It then quantifies over their supplied limit
   cones `u` and `u'` and asserts `∃! e : (shiftFunctor D n).obj Y ≅ Y'`
   with the equation
   `e.hom ≫ u'_(s[n]) = (shiftFunctor D n).map (u_s) ≫
   (F.commShiftIso n).inv.app s.left` for every denominator s. Thus the
   isomorphism identifies exactly the transported pro-object value maps.
   The inverse commutation isomorphism has the required direction
   F(X')[n] → F(X'[n]). The explicit shifted denominator is Mathlib's
   `MorphismProperty.Over.mk ⊤`, not a new denominator construction. Pass.

The supplied-cone formulation adds no ambient hypothesis. Essential constancy
already supplies a limit cone: another cone v factors by v at the retracting
stage followed by r; the common-stage equation gives all its legs, and the
retraction gives uniqueness. Every other limit cone at the same vertex is
uniquely isomorphic to that cone, hence also represents the same pro-object
value with its own structure maps. Conversely, quantifying over these cones
is nonvacuous and recovers existence of the value isomorphism. MS5 implies
`S ((shiftFunctor C n).map s.hom)` for every s, so quantifying over its proof
`hs` does not omit any denominator. The leg equations determine e uniquely,
because shifting denominators gives an equivalence and u' is a limit cone.
No naturality-in-X clause beyond the node is imposed.

Edge cases: zero and negative n are included in ℤ; at n = 0 the equation uses
the supplied coherent zero-shift comparison, with no choice of identification
silently asserted to be equality. Zero objects and the zero functor are
allowed. An empty denominator category cannot arise: MS1 supplies the
identity denominator for every X. Likewise an empty triangulated category
is excluded already by the source's zero-object axiom; the earlier report's
claim that empty categories are permitted was inaccurate. There are no
scheme, characteristic, or index-set restrictions in this lemma. Object
and morphism universes for C and D are independent and explicitly bound;
no quantified test-category universe or size restriction was introduced.

Independent searches, using words other than the worker's query:

- `msearch.py leanfinder "essentially constant pro diagram shift equivalence
  canonical comparison isomorphism"`: eight hits, including
  `Functor.ShiftSequence.induced.shiftIso`, `Functor.isoShift`, and
  `Functor.commShiftIso_eq_ofInduced`; generic shift comparisons, no
  essentially-constant Stacks LF theorem.
- `msearch.py leansearch "left derived functor defined at shifted object
  triangulated category"`: service unavailable (Internal Server Error),
  recorded as unavailable, not evidence of absence.
- `msearch.py loogle "CategoryTheory.Functor.CommShift.iso"`: unknown
  identifier. Repeated with
  `CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt`: seven hits in
  the pointwise-left-derived API. I read the definition and iff-of-mem
  signatures in `Functor/Derived/PointwiseLeftDerived.lean`; these concern
  right Kan extensions and invariance along a denominator, not the
  essential-constancy shift statement or canonical cone-leg comparison.
- `rg` of Mathlib's `Functor/Derived/*.lean` for shift/Shift, and of project
  `lean/Sheaf/CategoryTheory` and upstream `WeilConjectures/CategoryTheory`
  for leftDerived/LeftDerived, derived shifts, and 05SU: no duplicate.
  Existing project `ShiftIdentification` concerns spectral-sequence
  cohomology; upstream `RightDerivedFunctor/Triangulated` concerns abelian
  right-derived functors. Neither states this result. Broader `rg` for
  `IsEssentiallyConstantProDiagram` and the proposed declaration name over
  all Mathlib, upstream, and project confirms only the recorded project
  definition and its users; no existing theorem to reuse. I also checked
  `dag/lean_names_upstream.json` for the proposed name.

Only the canonical-comparison clause and its explanatory docstring changed;
the node's `lean.statement` was synchronized verbatim. The docstring retains
the source place, blueprint tag, and all three proof steps: the shifted
fraction-category equivalence via MS5 and inverse shift; transport of
essential constancy and F's shift comparison; uniqueness of values via
`lem-pc-essentially-constant-pro-hom-colimit`, then the inverse shift for the
reverse implication. There are no definitions or proved helper results in
the delivery; the one theorem has only `sorry`. The sole import supplies the
notions used. All binders and universes are explicit; lines are at most 100
characters. Server compilation with the prescribed `scompile.py F1
lem-pur-derived-functor-shift-05su` succeeded cleanly in 1.3 seconds.
