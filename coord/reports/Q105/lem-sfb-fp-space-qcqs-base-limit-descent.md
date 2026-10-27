## Worker report

The module `Sheaf.AlgebraicGeometry.FpSpaceQcqsBaseLimitDescent` states
`AlgebraicGeometry.AlgebraicSpace.fp_space_qcqs_base_limit_descent`, with `sorry` as
its entire proof. Its docstring reproduces all twelve proof steps of the node.
The source read is `literature/stacks-project/spaces-limits.tex`, Tag 07SK,
`lemma-descend-finite-presentation`, including the essential-surjectivity and
full-faithfulness paragraphs. This is its specialization to scheme bases.

Hypotheses and conventions, clause by clause:

- Work over Spec Z: every scheme base is an `Over (Spec (CommRingCat.of
  (ULift.{u} ℤ)))`; every space is an `AlgebraicSpace` over that same scheme.
  Spec of the lifted integers is the terminal scheme, so this is exactly the
  requested setting, without an extra choice of base structure. A limit in this
  over-category is equivalently the scheme limit. The small-valued fppf sheaves
  and the explicit universe `u` use the recorded size convention.
- The directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`, matching the standing directed-set convention.
  The index lives in the scheme universe, with no independent smaller universe.
- `D : Iᵒᵖ ⥤ Over ...` is the inverse system.
  `[∀ i, CompactSpace (D.obj i).left]` and
  `[∀ i, QuasiSeparatedSpace (D.obj i).left]` express qcqs stage schemes.
  `[∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]` expresses precisely
  affine transition morphisms, including all transition arrows.
- `c : Cone D` and `hc : IsLimit c` give T and its specified projections.
  There is no `IsAffine` assumption on any stage or on the limit.
- The introductory conventions on quasi-compact spaces, quasi-separated spaces,
  closed immersions and affine space morphisms introduce meanings, rather than
  extra hypotheses or conclusions. None of the last two notions occurs in the
  three conclusions. The bases here are schemes, so their absolute finiteness
  conditions use Mathlib's scheme predicates. A quasi-compact space can
  equivalently be tested by its point topology or a quasi-compact surjective
  etale atlas; no new copy of either notion is defined in this delivery.
- The finite-presentation condition for each map is written as three premises:
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y T f`,
  `MapIsQuasiCompact f`, and
  `MapIsQuasiCompact (pullback.diagonal f)`. The first tests all representable
  etale scheme charts of Y over the scheme T. The second is the existing
  affine-scheme-test definition; the third is precisely the quasi-compact
  relative diagonal. These three conditions are repeated for every stage model
  and for both objects in each Hom assertion, with none dropped or added.
- The products in the formulas are actual presheaf pullbacks of fppf sheaves.
  Limits of sheaves are computed in presheaves, so these are the sheaf fibre
  products specified in the node. The recorded fibre-product theorem guarantees
  that the resulting spaces are algebraic spaces; the full-subcategory maps are
  exactly the same natural transformations used here.

The conclusions, clause by clause:

1. The first conjunct quantifies over every space Y with a finitely presented
   map f to T. It supplies an index i, a space Yi and a finitely presented map
   fi to Ti, and `Nonempty ((Over.pullback ...).obj (Over.mk fi) ≅ Over.mk f)`.
   The isomorphism is in the category over the Yoneda presheaf of T, so it is
   exactly the required isomorphism over T, including its structure-map equation.
2. The second conjunct starts with any finitely presented Y and Z over one Ti
   and every morphism α between their pullbacks over T. It supplies j, `h : i ≤ j`
   and a morphism β over Tj between the stage pullbacks. The equation identifies
   α with the pullback of β, using `Over.pullbackComp` and transport along
   `yoneda.map_comp` and `c.w`. Both identifications are canonical, rather than
   an arbitrarily chosen isomorphism. The direction is direct pullback to
   iterated pullback on the source and its inverse on the target.
3. The third conjunct says that α and β over Ti, if equal after pullback to T,
   have equal pullbacks at some j with `i ≤ j`. Maps initially presented at
   different stages move to a common upper bound by directedness, after which
   this conjunct applies. This is the node's eventual equality at a later common
   stage; it imposes no injectivity condition on transition maps.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  Their structure definitions and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and `IsSurjective`.
  The full signatures and docstrings were read: the atlas maps and every scheme
  base-change square retain actual scheme representatives.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, read with its affine-local
  finite-presentation field and docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, read with its closed-embedding and
  stalk-surjectivity fields; this only supplies the introductory convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`, read in full. Its first assertion is exactly
  closure under the sheaf fibre products used in the statement.
- The size convention has a convention-only record, not a Lean declaration;
  explicit universes render it.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.MapToSchemeIsLocally` and `MapIsQuasiCompact`.
  Their existing definitions and docstrings were read in full and used without
  modification. The already landed node `def-sfb-proper-curve-moduli` is added
  to `stmt_deps` under the standing brief's permission to cite landed notions;
  a transitive DAG traversal confirmed that this adds no dependency cycle.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback` and
  `Over.pullbackComp`, read with the actual functor object/map constructions.
  All already stated proof-dependency modules are imported privately, including
  the spreading-out theorem, etale and monomorphism descent, quotient, atlas,
  finiteness permanence and chart-locality modules. Unstated proof nodes need
  no interface to write this statement and have not been re-created.

Edge cases checked: the empty index set is excluded explicitly, as the node
requires. Singleton directed systems allow j = i and identity pullbacks. Empty
stage schemes, empty Y or Z, empty atlases and the zero ring are not excluded.
No stage or limit point, field characteristic, nonempty geometric fibre,
transition surjectivity, separatedness, affineness of bases, or noetherian
hypothesis is imposed. The diagonal condition is relative to the map in
question, rather than separatedness of its source over the integers. `Preorder`
allows the directed-set convention without unnecessarily assuming antisymmetry.

Searches actually run with `msearch.py`, group Q105 and this item:

- LeanFinder: "Finitely presented algebraic spaces descend along inverse limits
  of quasi compact quasi separated schemes with affine transition maps".
  Eight hits, all on scheme affine-transition limits or affine spaces; none
  states algebraic-space descent.
- Loogle: "AlgebraicGeometry.AlgebraicSpace, CategoryTheory.Over.pullback,
  AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit". Zero hits; it
  reported unknown identifier `AlgebraicGeometry.AlgebraicSpace`.
- Mathlib grep: `AlgebraicSpace|exists_pullback_hom_of_isLimit`, restricted to
  AlgebraicGeometry. The wrapper returned zero hits.
- LeanSearch: "Finitely presented algebraic spaces descend to a finite stage of
  an inverse limit of qcqs schemes". Eight hits on smoothness, scheme sections,
  flat descent and finitely presented algebras/modules; none states this result.
- Local `rg` searched `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `fp_space.*limit`, and `space.*limit.*descent`, and the available algebraic-space
  modules for `MapIsQuasiCompact`, `MapIsLocallyOfFinitePresentation`,
  `schemeSpace`, `baseChange`, and `pullback`. It found the reusable notions
  listed above and `SpaceFpOverSpaceLimitDescent`, a more general theorem whose
  proof explicitly depends on this item; importing it would be circular.
  Its generic comparison `spaceLimitPullbackIso` is not copied: the statement
  writes the canonical Mathlib operations directly.
- `rg` for `fp_space_qcqs_base_limit_descent` in Mathlib, `WeilConjectures`,
  `Sheaf`, and `dag/lean_names_upstream.json` returned no preexisting declaration.

No statement dispute, missing dependency interface, or source correction was
found. No new definitions or definition nodes are delivered. The node's original
statement, proof and proof dependencies are preserved.

Validation: `scompile.py Q105 lem-sfb-fp-space-qcqs-base-limit-descent` compiled
the module both as the sandbox module and at its final library module path,
with no errors or non-sorry warnings. Automatic implicit variables are disabled.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
