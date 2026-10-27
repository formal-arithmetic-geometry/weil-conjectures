## Worker report

The module `Sheaf.AlgebraicGeometry.LfpSpaceSchemeLimitTest` states
`AlgebraicGeometry.AlgebraicSpace.lfp_space_scheme_limit_test`. Its sole proof is
`sorry`; it introduces no definitions. The item JSON changes only in `lean`.
Sources read: Stacks `spaces-limits.tex`, Proposition 04AK and Lemma 0CP4,
including the finite-cover/equalizer proof. The proof docstring follows all five
steps of the DAG proof, using finite affine covers of overlaps rather than
assuming intersections affine.

Hypothesis and clause correspondence:

- `S : Scheme.{u}` is the arbitrary base scheme; `Z : AlgebraicSpace S` is the
  recorded algebraic space over it, with no compactness or separation assumption.
- `hlfp` tests `LocallyOfFinitePresentation V.hom` for every representable étale
  chart `a : yoneda.obj V ⟶ Z.obj.obj`. This is precisely local finite presentation
  on scheme charts over the identity target chart of S. No surjectivity is needed
  for individual charts: they are the arbitrary étale charts of the usual local
  property. Equivalently one may test a surjective atlas, by the recorded chart
  criterion. The existence of an atlas is already part of `AlgebraicSpace`.
- `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, `[Nonempty I]` render a
  small nonempty directed set; allowing preorders also covers partially ordered sets.
  The index lives in the scheme universe, avoiding an oversized inverse system.
- `D : Iᵒᵖ ⥤ Over S` is the inverse system over S. `CompactSpace` and
  `QuasiSeparatedSpace` on each `(D.obj i).left` assert absolute qcqs, not relative
  finite presentation. The `IsAffineHom (D.map f).left` instance is exactly the
  affine-transition hypothesis. Nothing assumes finite presentation over S.
- `c : Cone D` supplies U and all its projections over S; `hc` states that the
  underlying scheme cone is limiting. This expresses U = lim U_i, without adding
  a condition: the recorded affine-transition theorem constructs such limits.
- The first conclusion is `Function.Bijective (colimit.desc ...)`. The functor
  `D.rightOp ⋙ Z.obj.obj` evaluates the existing space presheaf on stages;
  `Z.obj.obj.mapCocone (coconeRightOpOfCone c)` restricts along the actual
  projections. Thus the comparison is canonical, not an unspecified bijection.
  By Yoneda, evaluation at an S-scheme T is Mor_S(T,Z).
- The second conjunct represents every `g` by `a` at some stage `i`, and requires
  its actual projection restriction to be g.
- The third conjunct quantifies over two arbitrary stages and their maps. It is
  an iff between equality after restriction to U and equality after restriction
  to some k with i ≤ k and j ≤ k. The transition is `D.map (homOfLE hi).op`;
  contravariant space evaluation gives precisely precomposition.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsAlgebraicSpace`; its actual sheaf and atlas
  definitions supply the objects and charts, without a private replacement.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  exposed by `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`.
- That last module: `AlgebraicGeometry.exists_limit_affine_transition`, with
  nonempty directed I in the scheme universe, constructs the limit used here.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`;
  `Types.Colimits` supplies the required colimit existence. The two convention
  nodes (size and scheme conventions) introduce no additional object: explicit
  universes and the recorded scheme predicates implement them.

Proof-only modules imported as plain imports:
`Types.Filtered` (`jointly_surjective`, `FilteredColimit.isColimit_eq_iff`,
`isColimit_eq_iff'`); `QcqsSchemeCofinalFiniteCoverings`
(`qcqs_scheme_cofinal_finite_affine_open_coverings`); `Morphisms.QuasiCompact`
(`isCompact_iff_finite_and_eq_biUnion_affineOpens`); `Sites.Fpqc`
(`Scheme.zariskiPrecoverage_le_fppfPrecoverage`); `SiteCoveringAxioms`
(`Precoverage.IsSiteForCoverings`, with the existing sheaf condition); and
`SpaceLocalPropertiesChartTest` (`local_properties_chart_test`). All these
signatures/docstrings were read. The proof dependency
`lem-sfb-space-relative-affine-limit-criterion` has no recorded module on the
read base, so its proof-only import is omitted; it is not needed to type this
statement. There is no missing statement notion and no new node or dependency
repair is required.

Edge cases checked before drafting: an empty stage or empty limit is allowed;
the empty-cover sheaf condition supplies the unique empty-source map. Singleton
index sets reduce to restriction across a limit isomorphism. No nonemptiness of
Z or the stages is imposed. Nonseparated qcqs stages are allowed, so finite
covers of overlaps, rather than affine whole overlaps, are used in the plan.
Disconnected and non-quasi-compact Z are allowed. No statement dispute or
source correction was found.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: “Maps from inverse limits of quasi compact quasi separated schemes
  to a locally finitely presented algebraic space factor through a stage and
  agree eventually”: 8 hits, all scheme-level affine-transition lemmas, including
  `exists_appTop_π_eq_of_isLimit` and the two
  `Scheme.exists_hom*_of_locallyOfFiniteType` results; none states this theorem.
- Loogle: `"AlgebraicSpace", "IsLimit"`: 0 hits.
- Mathlib grep: `AlgebraicSpace|algebraic space.*limit` in AlgebraicGeometry:
  0 hits.
- Project and upstream rg: the node id and
  `space.*limit.*[Bb]ijective|[Bb]ijective.*space.*limit`: only the downstream
  Artin infinitesimal-smoothness proof docstring cites the item; no declaration.
  Further source searches located the existing algebraic-space chart framework,
  which is reused. The example CompactObject module is now a withdrawn empty
  module; its node binds Mathlib's compact-object declaration. The current
  module header follows the live algebraic-space modules instead.

Validation: scompile.py passed both the sandbox and library module checks, with no
errors or unexpected warnings. deliver2.py --no-push returned OK: commit
9cf000da3e0 passes preflight and compiles; nothing pushed. The final delivery
uses the same Lean source and node record, with this validation note added.

## Second reading by Q08

A second pass reread the node, the source and the complete signature, checking
that the diagram is over S, that evaluation uses the correct opposite direction,
and that the colimit map is induced by the cone rather than supplied as data.
The three conclusion conjuncts match the bijection and both stated elementwise
clauses. Absolute qcqs is imposed only on the stages. The chart assumption uses
all étale source charts over the identity chart of S, the standard specialization
of the universal chart criterion. The underlying-scheme limit hypothesis does
not add any geometric restriction. No mismatch required a statement correction.
This is the worker's second pass; the maintainer performs the independent review.
