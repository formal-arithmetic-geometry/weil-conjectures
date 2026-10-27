## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsSpaceFiniteSchemeCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_finitePresentation_scheme_cover`.
Its only theorem has proof `sorry`; it introduces no definitions or auxiliary theorems.
The statement agrees with Stacks Project, spaces-limits.tex, Tag 09YC,
`proposition-there-is-a-scheme-finite-over`, clause (1), read at lines 3568–3597.
This is the arbitrary-base assertion; clause (2)'s prescribed-atlas factorization
is not part of this node.

The hypothesis and conclusion correspondence is as follows.

- A scheme S: `{S : Scheme.{u}}`, with an explicit universe `u` and
  `set_option autoImplicit false`. There are no assumptions on S.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, the existing full
  subcategory of fppf sheaves with representable diagonal and an etale
  surjective scheme atlas.
- Quasi-compactness, specifically a quasi-compact etale scheme atlas:
  `(hqc : IsQuasiCompact X.obj)`. The recorded definition says exactly
  `∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
  CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
- Absolute quasi-separatedness: `(hqs : IsAbsolutelyQuasiSeparated X)`.
  This reuses the landed affine-pair criterion of Stacks 0AHR(3): for every
  affine S-schemes U,V mapping to X, their fibre product over X has compact
  point space. This is the equivalent criterion for the absolute diagonal
  over Spec Z, including for a base S which is not quasi-separated. It is
  not a hypothesis about just the relative diagonal over S.
- An S-scheme Y and map to X: `∃ (Y : Over S) (p : schemeSpace Y ⟶ X)`.
  The existing `schemeSpace` has the actual representable fppf sheaf h_Y
  as data; this is not an arbitrary algebraic-space source with an extra
  representability assumption.
- Surjectivity on field-valued point classes:
  `pointImage p.hom.hom = Set.univ`. By the definition of `pointImage`,
  every point class is represented by the image of a field-valued
  representative of h_Y. This does not require a lift over the original
  residue field or surjectivity of sections on every test scheme.
- Finiteness:
  `IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) p.hom.hom`.
  Unfolding the existing predicate quantifies over every S-scheme T and
  h_T → X and supplies an S-scheme representing the pullback, with its
  projection finite as a scheme morphism. `IsFinite` is Mathlib's
  affine-local finite-ring-map predicate.
- Finite presentation is all three required conditions:
  `MapIsQuasiCompact p.hom.hom`, `MapIsQuasiSeparated p.hom.hom`, and
  `MapIsLocallyOfFinitePresentation p`. The middle predicate is exactly
  quasi-compactness of the canonical relative diagonal. The last predicate
  tests Mathlib's `LocallyOfFinitePresentation` on every compatible pair
  of representable etale scheme charts, without choosing an atlas.
- There is no Noetherian, separatedness, finite-type-over-S, field,
  nonemptiness, reducedness, or connectedness assumption.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, including their full structure signatures
  and docstrings (Scheme.lean:36–47 and 73–75).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
  Read the full declarations, in particular the quantified representing
  pullback square in `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact` and
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointImage` and `pointTopologicalSpace`;
  also read `PointRepresentative` and `Point` in AlgebraicSpacePointClasses.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`:
  `AlgebraicGeometry.IsFinite`, full signature and docstring at lines 35–40.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, full signature and
  docstring at lines 42–48; used through the existing chartwise predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation` and
  its defining `MapIsLocally` chart quantifiers.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiCompact`, read in full,
  obtained through the preceding imports.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` and
  `schemeSheaf_isAlgebraicSpace`, read in full. The latter supplies only
  the Prop-valued algebraic-space property of the actual Yoneda sheaf.
- `def-weil-size-convention` is a metatheoretic convention. Its recorded
  explanation was read; the explicit `u` on Scheme and the existing big-site
  constructions implement the size bound, with no new universe equality.

The three additional statement dependencies are already landed definition
nodes: `def-sfb-space-absolute-quasi-separated`,
`def-sfb-space-morphism-properties`, and `def-trf-scheme-algebraic-space`.
They give names to notions already in the unchanged informal statement.
No node is created, no dependency interface is repaired, and the item's
statement and proof are unchanged.

Proof dependencies: imports retain the available modules
`AlgebraicSpaceEtaleOpenImage` (`points_compactSpace_iff`),
`IntegralSpaceFinitePresentationLimit`
(`exists_finite_finitePresentation_limit_of_integral`), and
`SpaceLimitSchematicStage` (`exists_scheme_stage_of_isLimit`). Their full
signatures and proof docstrings were read. The integral-scheme-cover node
`lem-sfb-qcqs-space-integral-scheme-cover` has no Lean record, Mathlib match,
or audited declaration in the read repository, so no module can yet be
imported for that proof dependency. It is not needed to type this statement.
The theorem docstring retains all four proof steps, including that prerequisite,
the passage from a limit over X to one over S, and surjectivity by factorization
without assuming that a limit projection is surjective.

Edge cases checked before writing: the empty space is allowed and can have
an empty scheme cover; no `Nonempty` binder excludes it. A scheme X satisfies
the conclusion by its identity, including non-Noetherian and non-separated
qcqs schemes. The hypotheses do not force the base S to be quasi-separated:
absolute quasi-separatedness of X is a separate, existing predicate. Finite
presentation includes quasi-separatedness even though finiteness implies it;
this preserves the node's explicit clauses. All test schemes, atlases and
field-valued representatives use the existing universe-u framework, rather
than introducing an independent lower test universe.

Searches run (2026-10-24):

- msearch leanfinder: "Every quasi compact quasi separated algebraic space
  admits a finite surjective finitely presented morphism from a scheme".
  Eight hits: Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource,
  compactSpace_iff_exists, Scheme.exists_hom_isAffine_of_isLocalAtSource,
  quasiCompact_of_compactSpace, quasiCompact_over_affine_iff, QuasiCompact,
  quasiCompact_iff_compactSpace, IsFinite. These concern schemes or their
  quasi-compactness, not finite finitely presented scheme covers of spaces.
- msearch loogle: "AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.LocallyOfFinitePresentation". One hit:
  Scheme.Hom.isLocallyConstant_finrank, a rank theorem for finite flat
  scheme morphisms; it does not state the cover theorem.
- msearch grep: "AlgebraicSpace|finite.*surjective.*scheme|finite.*scheme.*cover"
  in Mathlib/AlgebraicGeometry. Four hits, concerning OpenCover.finiteSubcover,
  noetherian finite open covers and affine-transition scheme limits; no match.
- rg in lean/WeilConjectures and lean/Sheaf for finite scheme covers and
  finite cover existence found scheme-cover and cohomology effacement
  results, not this algebraic-space theorem. The literal node-id search
  in lean/WeilConjectures returned no result. The chosen declaration name
  was absent from both project trees, Mathlib and dag/lean_names_upstream.json.
- Searches for IsAbsolutelyQuasiSeparated, MapIsQuasiCompact,
  MapIsLocallyOfFinitePresentation and schemeSpace located precisely the
  interfaces reused above; the owning DAG nodes and their records were read.

No statement dispute or source fault was found. The module compiled cleanly
through scompile.py in both sandbox and library modes (3.1 seconds each).

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
