## Worker report

The module `Sheaf.CategoryTheory.StrictRoosShiftLocalization` states
`CategoryTheory.strictRoosShiftLocalization`, with its sole theorem proof `sorry`.
There are no new definitions, dependency repairs, statement corrections, or new nodes.
The natural-language statement and its six proof steps are unchanged. The module's
docstring carries those six steps and their sources. The earlier reported refusal
concerned the completed stage-1 split; this is the requested stage-2 statement.

Hypothesis and clause correspondence:

- Abelian category A: `{A : Type u} [Category.{v} A] [Abelian A]`.
- Countable products and inverse limits of strict towers:
  `[HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]`. A natural index n represents
  the positive index n+1, by the order isomorphism between these index sets.
  Towers are the actual functor category `ℕᵒᵖ ⥤ A`, whose levelwise abelian
  structure is the dependency's Mathlib instance; no separate tower structure is assumed.
- Fixed unbounded derived localizations with integer shifts: the arbitrary categories
  `DT`, `DA`, their `HasShift` instances, functors `QT`, `QA`, their `IsLocalization`
  instances at `HomologicalComplex.quasiIso ... (.up ℤ)`, and their `CommShift ℤ`
  structures. This is the localization definition of the recorded abstract derived
  category, not a restriction to one construction. All six object and morphism
  universes are explicit and independent; no equality of localization universes is
  imposed. The source is unbounded `CochainComplex ... ℤ` throughout.
- Product P, h=1-s, shifted cone F and inclusion j: the dependency's actual `roosF`,
  `roosU`, `roosProj`, `roosι`, and `roosLimitFunctor`; all are imported directly.
  `roosF` is the shifted cone functor with its specified diagonal product maps,
  not a functor supplied as a hypothesis. `roosι` is the specified (0,z) inclusion.
- G and the specified factorization: `(G : DT ⥤ DA)` and
  `(κ : roosF ⋙ QA ≅ QT ⋙ G)`. No exactness of products, K-injectivity, or
  quasi-isomorphism preservation of ordinary inverse limit is assumed.
- Coherent natural chain isomorphisms c: the witness
  `cF : (roosF (A := A)).CommShift ℤ`. The first conjunct has two component
  equations for every complex X, integers r,q and tower index n. Projection
  `roosProj` gives the unchanged x coordinate; `mappingCocone.snd` gives the
  y coordinate with scalar `r.negOnePow`, i.e. (-1)^r. Both equations include
  `shiftFunctorObjXIso` and every product projection to specify the canonical
  reindexing without treating objects of an arbitrary abelian category as sets.
- Same inverse formula: the second conjunct gives the corresponding TWO equations
  for `(Functor.commShiftIso roosF (self := cF) r).inv.app X`. The x coordinate
  is unchanged and the y coordinate is multiplied by `r.negOnePow` again.
- Naturality and zero/addition coherence: built into Mathlib's `Functor.CommShift`
  structure via its natural isomorphisms, `commShiftIso_zero`, and
  `commShiftIso_add`. These include the canonical shift-addition identifications.
- Limit shift identity on compatible tuples: witness
  `cL : (roosLimitFunctor (A := A)).CommShift ℤ` and the third conjunct, equating
  every `limit.π` after reindexing. By the universal property this specifies exactly
  the identity on tuples, rather than choosing an arbitrary limit shift.
- Strict inclusion square: the fourth conjunct is
  `roosι (X⟦r⟧) ≫ cF_r = cL_r ≫ (roosι X)⟦r⟧'` for EVERY X and r.
- Existence and uniqueness of the coherent derived comparison: the final conjunct
  is `∃! cG : G.CommShift ℤ, ...`. Its first equation is precisely the prescribed
  factorization square, with the `QT.commShiftIso` and `QA.commShiftIso`
  identifications written explicitly. Thus uniqueness is for the comparison on
  the given G with the given kappa, not just up to an unspecified isomorphism.
- Naturality on every derived morphism, including inverse quasi-isomorphisms:
  `cG` contains natural isomorphisms of functors ON DT. This quantifies over
  all its morphisms, not only maps in the image of QT.
- Localized inclusion square: the second equation within `∃! cG` explicitly
  composes `QA.map (roosι (X⟦r⟧))`, kappa and the derived shift on the left,
  and the localized limit shift followed by the shifted unshifted inclusion
  on the right. Ordinary limit is used only as a functor on complexes.

Dependencies read and used:

- `lem-weil-tower-category-levelwise-abelian`: recorded Mathlib match
  `CategoryTheory.Abelian.functorCategoryAbelian`,
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`, with levelwise structure.
- `def-weil-abstract-derived-category`: recorded `DerivedCategory` and
  `HasDerivedCategory` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Its defining localization property and compatible shifts are expressed by
  `IsLocalization` and `CommShift` for the prescribed choices, including the
  recorded canonical `DerivedCategory.Q` as a special case. This module is already
  publicly imported by `StrictRoosModel`.
- `def-weil-strict-roos-model`: `CategoryTheory.roosF` in
  `Sheaf.CategoryTheory.StrictRoosModel`; the full signatures and constructions of
  `roosU`, `roosProj`, `roosι`, `roosLimitFunctor` and `roosDerivedUnit` were read.
  No copy of any construction is introduced.
- Proof dependency `lem-weil-pbc-localization-universal-property`: recorded Mathlib
  `CategoryTheory.Localization.lift`, `liftNatTrans`, `liftNatIso`, and
  `natTrans_ext`, in `Mathlib.CategoryTheory.Localization.Predicate`, imported
  without `public`. Their full signatures and docstrings were inspected.
- `Mathlib.CategoryTheory.Shift.CommShift` supplies the existing coherent natural
  shift structure; its definition and zero/addition axioms were read.

Edge cases checked before writing: zero category and zero complex; r=0; negative
r including -1; two odd successive shifts; arbitrary unbounded degrees; characteristic
2, where the sign becomes the identity; positive tower index 1 (encoded by n=0);
nonexact countable products. In each case the signed coordinate map and inverse
have the stated formula, preserve (0,z), and have no additional restriction.
The descent hypothesis kappa itself ensures the necessary localization factorization;
ordinary limit never needs to preserve quasi-isomorphisms.

Searches for an existing statement (2026-10-22):

- msearch.py, leanfinder: "The signed strict Roos cone functor commutes coherently
  with integer shifts and descends uniquely through a prescribed derived
  localization factorization". Eight hits, including generic derived-functor
  CommShift instances and `Functor.mapDerivedCategoryFactors`; none states the
  strict Roos coordinate and inclusion clauses with the prescribed G and kappa.
- msearch.py, loogle: `CategoryTheory.Functor.commShiftOfLocalization`. Four hits:
  the generic descent construction and its hom/inv component lemmas. They supply
  machinery but do not state this strict Roos result.
- msearch.py, grep: `commShiftOfLocalization|roosCommShift|roosShift`, in
  Mathlib CategoryTheory. Five hits in Shift/Localization.lean, all generic.
- rg on project `WeilConjectures` and `Sheaf` for
  `lem-a1-strict-roos-shift-localization|roosCommShift|strictRoosShiftLocalization`:
  no exact existing declaration. The Roos shift constructions in
  InjectiveTowerRoosShifts and RoosConeCalculus are private and contain no
  theorem for an arbitrary prescribed derived localization factorization.
- Read `Sheaf.CategoryTheory.NormalizedRoosShiftComparison`: it treats the more
  specialized normalized derived-limit comparison on a module-sheaf category;
  it does not state the present arbitrary-abelian-category localization result.
  Its component conventions agree with the strict model used here.

Sources checked directly: Stacks derived.tex, definition-cone (Tag 014E), and
homology.tex, definition-shift-cochain (Tag 011G). No node fault or mathematical
dispute was found. The independent stage-1 review by Q24 confirms the same signs
and localization descent route; it does not supply a Lean statement.

Validation: single-file compilation uses only scompile.py against the live server.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
