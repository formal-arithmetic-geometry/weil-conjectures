# Projective-bundle base change

## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange` states
`AlgebraicGeometry.isProjectiveBundle_pullback_snd`, with its sole proof `sorry`.
It adds no definitions and leaves the accepted stage-1 split unchanged.

The inherited BLOCKED ending concerned reopening a stage-1 split. The live node
is split and stage-1 reviewed, has no Lean record, and is queued at stage 2.
The maintenance handoff at the start of coord/brief-stage2.md explicitly permits
this stage-2 statement delivery. No released repair note for this item exists.

Clause-by-clause correspondence:

- Schemes X, S and S' are the explicitly bound `{X S S' : Scheme.{u}}`.
  The universe u is declared, and both automatic implicit mechanisms are disabled.
- The arbitrary morphisms f : X to S and a : S' to S are exactly the two explicit
  binders `(f : X ⟶ S) (a : S' ⟶ S)`.
- The hypothesis that f is projective in the projective-bundle convention is
  `(hf : IsProjectiveBundle f)`. Opening the recorded dependency declaration,
  this is existence of `E : S.Modules`, `hE : E.IsQuasicoherent`, `E.IsFiniteType`,
  and a closed immersion i into the canonical symmetric graded algebra's relative
  Proj, with `i ≫ relProjHom = f`. Thus it includes exactly the finite-type
  quasi-coherent module, the specified P(E), and the closed embedding over S.
  It does not use the stronger finite-projective-space convention.
- The fibre product is `pullback f a`, with its map to S' given by
  `pullback.snd f a`. `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence
  for arbitrary schemes; no extra `HasPullback` hypothesis is needed.
- The conclusion is `IsProjectiveBundle (pullback.snd f a)`, using exactly the
  same predicate and therefore exactly the same projectivity convention.
- No Noetherianity, flatness, local freeness or ampleness hypothesis appears.
  All assumptions on the witness module occur inside the recorded predicate.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and scheme morphisms, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- def-trf-projective-bundle-morphism: `AlgebraicGeometry.IsProjectiveBundle`, in
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`. This predicate is used
  directly, without a replacement or a second projectivity definition.
- pqf-def-coherent: `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`,
  in `Sheaf.AlgebraicGeometry.CoherentFiniteType`; its two constituent conditions
  are precisely the conditions used inside IsProjectiveBundle. Its module is a
  public statement dependency; there is no separate finite presentation condition.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, used by the predicate.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- def-pc-module-pullback: `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `tensorPullbackSectionAdjunction`, and `tensorPullbackSectionComp`, exposed by
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (plain proof import).
- lem-trf-projective-bundle-quotient-geometry:
  `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry`,
  in `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` (plain import).
  Its signature has arbitrary quasi-coherent E, unique quotient-classifying
  morphisms and arbitrary-pullback compatibility; finite local freeness is absent.
- lem-weil-pbc-closed-immersion-base-change: its mathlib_match is
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange` in the already
  public closed-immersion module, including its pullback.snd instance.
- lem-weil-pbc-module-pullback-finite-type:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback_isFiniteType` in
  `WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType` (plain import).
- lem-weil-pbc-module-pullback-quasi-coherent:
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` (plain import).
  This is the existing ordinary-module-pullback instance; the supplied normalized
  adjunction compares that pullback with the explicit tensor construction.

Source checked: literature/stacks-project/morphisms.tex, the full statement and
proof at lemma-base-change-projective (02V6). It asserts base-change stability
of projectivity and cites projective-bundle base change, module finite-type
pullback and closed-immersion base change. The docstring follows all five steps
of the accepted node proof, including the inverse maps supplied by quotient
classification that fill in the source's omitted details.

Edge cases checked before writing: X or S' empty is allowed and gives an empty
fibre product; the identity and an arbitrary nonflat base change are both
included. E may be zero, finite type but nonfree, or non-locally-free: the
predicate and theorem impose no positive rank or freeness. The zero-module
projective bundle is empty, so a closed immersion into it forces empty X,
and causes no exception. Neither base must be affine or Noetherian.
There are no index-set or rank parameters that discard rank zero. Schemes share
one arbitrary universe as in the recorded projectivity construction; this adds
no geometric restriction on schemes and does not quantify over a smaller test
universe. No new node, dependency repair, or statement correction was needed.

Searches performed with msearch.py:

- leanfinder: "Base change of a projective morphism defined by a closed immersion
  into the projective bundle of a finite type quasi coherent module is projective".
  Eight hits: closed-immersion, properness, immersion, finite morphism and related
  stability results; none states this projective-bundle projectivity statement.
- loogle: `"Projective", "baseChange"`. Twelve hits, all Weierstrass projective
  curve base-change declarations; none is this scheme-morphism statement.
- grep in Mathlib/AlgebraicGeometry:
  `IsProjectiveBundle|projectiveBundle.*baseChange|projective.*base.change`.
  One hit, the Weierstrass curve base-change docstring; no matching declaration.
- leansearch: "Projective morphisms defined by a finite type quasi coherent
  projective bundle are stable under arbitrary base change". Eight hits on
  general morphism-property stability, properness, affine and quasi-compact
  morphisms; none matches projective-bundle projectivity.

Local source searches used rg on both lean/WeilConjectures and lean/Sheaf:
`IsProjectiveBundle|projective_bundle.*base_change|isProjectiveBundle.*(pullback|base)`.
The upstream source has no matching statement. Sheaf has the definition and
consumers, composition, properness, and comparison with H-projectivity, but no
arbitrary-base-change theorem. The node id search in lean/WeilConjectures gives
no hit. The proposed full declaration name is absent from these source searches.

The example Sheaf.CategoryTheory.CompactObject module has been withdrawn;
its node now records WeilConjectures.CategoryTheory.CompactObject. That upstream
module was read for the actual module/public-import/docstring conventions.

Validation: single-file server compilation and delivery preflight are run using
the prescribed scompile.py and deliver2.py wrappers. Only the expected sorry
warning is permitted. The maintainer supplies the independent review.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
