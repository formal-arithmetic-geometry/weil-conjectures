## Worker report

The module `Sheaf.AlgebraicGeometry.FlatSpaceSmoothLocus` states
`AlgebraicGeometry.AlgebraicSpace.exists_smooth_open_of_flat_locallyOfFinitePresentation`.
Its only theorem has proof `sorry`. It introduces no definitions and makes no statement
correction. The proof docstring gives all five accepted DAG proof steps with their inputs.

Hypothesis and conclusion correspondence:

- Schemes and algebraic spaces: `{S : Scheme.{u}}`, `X : AlgebraicSpace S`, and
  `T : Over S`. The ambient scheme S records the big site. Every scheme morphism
  h : T' → T is covered: take the ambient scheme S to be T if no other base is fixed.
  The statement also holds for every fixed ambient base and all its scheme morphisms.
- The map f : X → T is the natural transformation
  `f : X.obj.obj ⟶ yoneda.obj T`, as in the project's scheme-target interface.
- Flatness is `hf : MapToSchemeIsLocally (@Flat) X T f`; local finite presentation is
  `hfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`. Both are tests on
  every representable étale scheme chart, exactly as specified in the node.
- The open W is `∃ W : OpenSubspace X`. Smoothness of f restricted to W is the first
  conjunct: for every `a : yoneda.obj U ⟶ W.val.toFunctor` with `IsEtale a`, the scheme
  morphism `(yoneda.preimage (a ≫ W.val.ι ≫ f)).left` is `Smooth`.
  This is the same scheme-target chart test, expanded because W is already given as a
  subfunctor. It does not assume representability of f or a scheme source X.
- Largest means the second conjunct: every `B : OpenSubspace X` satisfying precisely
  the same smoothness chart test obeys `B ≤ W`. No smooth open is omitted, including
  the empty open and the whole space when f is smooth.
- Every scheme base change is quantified by `(T' : Over S) (h : T' ⟶ T)`. There is
  no assumption on h, in particular no flatness, properness or surjectivity.
- `X'`, its projection `p : X' ⟶ X`, and `f' : X'.obj.obj ⟶ yoneda.obj T'` satisfy
  `IsPullback p.hom.hom f' f (yoneda.map h)`. This is the fibre-product universal
  property with both specified projections, rather than an arbitrary comparison map.
  Quantifying over all such squares includes the chosen fibre product and all its
  canonically isomorphic realizations. Algebraic-space pullback existence is the
  imported `fibreProduct_isAlgebraicSpace`; no new existence assumption is imposed.
- The new locus is `∃ W' : OpenSubspace X'`, with the actual subfunctor equality
  `W'.val = W.val.preimage p.hom.hom`. Its next two conjuncts state smoothness of the
  restriction and maximality among every smooth open B of X', respectively. Together
  these identify the smooth locus of f' exactly, not merely one smooth open inside it.
- The final iff is `MapToSchemeIsLocally (@Smooth) X' T' f' ↔
  mapPoint p.hom.hom ⁻¹' (pointImage W.val.ι)ᶜ = ∅`. Thus the inverse image of the
  actual complement on point classes is empty exactly when f' is smooth everywhere.
- There is no properness, relative-dimension, Noetherian, separatedness, nonemptiness,
  finite-type or characteristic hypothesis beyond the two stated chart properties.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` (the
  recorded `IsSmooth` name is a deprecated alias; this uses its current name).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `AlgebraicSpace.OpenSubspace`;
  its order is the inherited order on the underlying subfunctors.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` and their universal property; the theorem uses the
  equivalent `IsPullback` square interface with the two projections explicitly bound.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapToSchemeIsLocally`
  and `AlgebraicSpace.mapPoint`. Added its already landed owning node
  `def-sfb-proper-curve-moduli` to stmt_deps, per the permission to cite landed notions.
  This introduces no second definition and needs no new node or dependency repair.

The plain proof imports follow the accepted plan: `IsZariskiLocalAtSource.iff_of_iSup_eq_top`
(Mathlib morphism Basic); open-immersion étaleness, `Etale.etale_comp` and `Etale.of_comp`
(Mathlib Etale); `etale_open_image` (AlgebraicSpaceEtaleOpenImage);
`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`
(AlgebraicSpaceFibreProductsEtaleCovers); `smooth_iff_of_jointly_surjective_etale` and
`smooth_at_iff_of_etale` (SmoothEtaleLocalSource); `point_open_calculus`
(AlgebraicSpacePointOpenCalculus); and `smooth_at_point_pullback_snd_iff_of_flat`
(FlatSmoothPointBaseChange). Their modules and declarations were read.

Edge cases checked before writing: empty X gives the empty/full open with vacuous
chart tests; empty T' or X' makes the bad-locus inverse image empty and the morphism
smooth; the identity base change recovers W; a smooth f has W = X; a nowhere-smooth
flat family has W empty, and the final iff then requires the new source to be empty.
Nonflat h is expressly included. The field-valued point classes and all schemes use
one common universe u, the existing big-site convention; no independent smaller test
universe or extra universe equality is imposed. The open-subspace chart tests have
actual scheme charts, since open subspaces are algebraic spaces as in their node.

Searches (2026-10-24; raw tool results also captured in searches.jsonl):

- msearch leansearch: "An algebraic space flat and locally of finite presentation over
  a scheme has an open smooth locus preserved by arbitrary base change". Eight hits,
  all scheme/ring smoothness, smooth base-change stability or flat stability; no
  algebraic-space smooth-locus theorem.
- msearch leanfinder: "The smooth locus of a flat locally finitely presented morphism
  of algebraic spaces is open and commutes with arbitrary base change". Eight hits:
  scheme universally-open and smooth predicates and algebra smooth-locus openness;
  no exact result for algebraic spaces.
- msearch loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat`. Three hits:
  smooth implies flat, scheme descent instance, smooth-fibre criterion. No exact match.
- msearch grep: `smoothLocus|smooth_locus` in Mathlib AlgebraicGeometry. Found scheme
  `Scheme.Hom.smoothLocus` and associated results, not algebraic spaces.
- rg of `smoothLocus|smooth_locus|MapIsSmooth` in project Sheaf and WeilConjectures:
  scheme results only; no algebraic-space locus statement. Direct item-id search finds
  only its use in ArithmeticNodalCurveStackSmooth's proof docstring. Full-name search
  for the proposed theorem in Sheaf, WeilConjectures and dag/lean_names_upstream.json
  returned no existing declaration.
- rg/read of `MapToSchemeIsLocally` and `MapIsLocally` found and reused the existing
  scheme-target interface in ProperCurveModuli. No helper definition was necessary.

Source read: local Stacks morphisms.tex, lemma-set-points-where-fibres-smooth case (1)
(Tag 02V4), lemma-smooth-at-point (01V9), and spaces-morphisms.tex lemma-where-smooth
(Tag 0DZI). The last displayed clauses alone do not give arbitrary base change; the
flat-family conclusion uses 02V4(1), exactly as the accepted DAG proof says.

Validation: scompile.py compiled this module both as sandbox and library module with
no errors or unexpected warnings. All binders and universe variables are explicit;
autoImplicit is false. Maximum line length is 87. No node fault or dispute found.

## Second reading by NL

A separate self-review pass reread the complete node and final signature; no second
agent was started, as required by the dispatcher. The maintainer supplies the independent
review. The pass checked both hypothesis binders, the two original-open clauses, all
base-change binders and the cartesian-square orientation, the literal subfunctor
preimage equality, both new-open clauses and the complement iff against the node.
In particular, the chart of W maps into W itself (not merely a scheme chart of X),
and its composite with W's inclusion is the restriction of f. The comparison is the
actual projection p supplied by the pullback square. The maximality of W' makes its
identification with the smooth locus explicit. Empty spaces, identity base change and
nonflat h remain covered. No statement or implementation adjustment was needed in this
pass. The node copy changes only lean and gains the already landed interface owner in
stmt_deps. No new node, dependency module, or statement correction is included.
