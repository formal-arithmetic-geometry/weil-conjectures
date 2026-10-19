## Worker report

The module states exactly the injectivity, image and uniqueness assertions of
prop-pur-affine-line-orientation-uniqueness. Its four helpers only package the existing
support charts, the product index, the actual supported pullback and its normalized
unit family. The only postponed theorem is affineLine_orientation_uniqueness; its proof
is `sorry` and its docstring contains all six steps of the node's proof. Definitions
have explicit data; no arbitrary map or object is selected from an existence assertion.

Hypotheses and clauses, matched individually:

- The chapter's fixed finite-field and finite-coefficient setting is the recorded
  `P : PurityFiniteSetting.{u}`. Thus A is the actual quotient O_E/(varpi_E^n), with
  the recorded standard size lift `P.Coefficient`, and n is positive by `P.level_pos`.
- The affine-line datum used to define kappa(t) includes
  `h : P.ramificationIndex ∣ P.level`, exactly as in the recorded orientation theorem.
  This is inherited from “Y and kappa(t) as in thm-pur-affine-line-orientation”.
- The separated finite-type k-scheme is `Y`, with structure morphism `a` and
  `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`, the same interface as
  the dependency. There is no smoothness, connectedness, reducedness or nonemptiness
  assumption on Y.
- The displayed source Hom is exactly
  `P.derivedSheaf h Y false ⟶ P.gysinValue h Y`. These are the recorded degree-zero
  constant coefficient unit and Rs^! A(1)[2], with the actual transported finite-level
  exceptional functor of PurityGysinStructure. Hom is in the ambient derived category,
  as in this node's display. The dependency places both objects in the full finite-Tor
  constructible category.
- `OrientationGeometricFamily` is the product over `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] [Algebra P.field.k Ω]`, every map `y : Spec Ω ⟶ Y`, and its
  over-k equality `hy`. Each factor is the recorded `P.gysinSupport h (Spec Ω)`,
  i.e. actual degree-two supported hypercohomology on the fibre with root-line twist.
  The point need not be finite type over k. The field universe agrees with Scheme.{u}
  and with the dependency's geometric-point convention, rather than an independent
  smaller universe. Repeated equivalent field presentations do not change injectivity.
- The restriction is `orientationGeometricRestriction`: `gysinHomToSections`, then
  the published normalized `chart.support.hom`, then `orientationSupportRestriction`.
  The latter is the existing right-derived kernel map with the actual canonical
  root-line coefficient pullback. Transport and chart fields have the published
  normalization equations, so no arbitrary map can stand for restriction.
- The injectivity clause is `Function.Injective (P.orientationGeometricRestriction h D)`.
- The normalized family is `orientationNormalizedFamily`: at a point it is
  `(D.residue Ω y hy).inv 1`. Each residue is an A-linear ModuleCat isomorphism;
  `residue_normalized` fixes its value on the actual fibre coordinate boundary to 1,
  independently of the morphism on Y. This is precisely the normalization of the
  recorded rank-one local calculation, also used in affineLine_orientation.
- `∃ m, ... ∧ orientationGeometricRestriction ... m = orientationNormalizedFamily ...`
  says the all-ones family lies in the image. The preceding equality
  `D.chart.support.hom (P.gysinHomToSections ... m) = D.chart.coordinateBoundary ...`
  identifies this preimage with the actual global Kummer-boundary orientation pur_s,
  rather than an arbitrary normalized morphism.
- The final universally quantified implication says every other morphism with the
  same normalized geometric restrictions equals this m. Thus the coordinate
  orientation is the unique such global morphism.
- `∃ D : OrientationRestrictionData ...` produces all normalized charts, transports,
  and fibre residues. None is an added hypothesis. Existential packaging matches
  the dependency's interface for these canonical maps.

Statement dependencies used (read the declarations and docstrings in the shared sources):

- Sheaf.Paper.PurityFiniteSetting: `WeilConjectures.PurityFiniteSetting`, its
  `Coefficient`, `constant`, `twist`, and `derivedSheaf` constructions.
- Sheaf.Paper.PurityAffineLineOrientation: `OrientationSupportData`,
  `OrientationSupportData.coordinateBoundary`, `orientationSupportRestriction`, and
  `affineLine_orientation`, all in `WeilConjectures.PurityFiniteSetting`.
- Sheaf.Paper.PurityRankOneLocalCalculation:
  `WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation`, including
  the pro-etale supported class, A-linear residue and coordinate normalization.
- Via the orientation import, Sheaf.Paper.PurityGysinStructure supplies `gysinValue`,
  `gysinSupport` and `gysinHomToSections`; Sheaf.Paper.SupportedHomPullback supplies
  `AlgebraicGeometry.proEtaleSupportHomTransport`. These are reused, never copied.

All recorded modules of the stated proof dependencies are imported non-publicly,
including the etale stalk-conservative theorem's upstream module. The Mathlib-only
proof leaves use DerivedCategory.FullyFaithful, HomologySequence, Sites.Point.Basic,
Sites.Point.Skyscraper and ShortComplex.ShortExact. No import cycle was needed.

Edge cases checked before writing: empty Y has no geometric points, so the target
product and source Hom are both singletons; disconnected Y permits independent
scalars on different components and all points are still tested; nonreduced Y is
allowed; ramified coefficient extensions are retained with precisely the recorded
finite Kummer-level convention; no primitive root is chosen by the statement; no
exceptional comparison is assumed invertible; algebraically closed point fields are
not required to be finite over k; the coefficient level cannot be zero because the
setting already requires n >= 1. A geometric family uses a dependent function type,
so the empty-product case requires no nonempty index instance.

Searches performed for this statement and its map packaging:

- msearch.py LeanFinder: “A morphism from the constant finite etale sheaf to the
  zero-section support complex on the affine line is determined by its geometric
  restrictions”. Eight hits, including AffineSpace.homOverEquiv and affine-limit
  structure-sheaf section lemmas; none concerns these support classes.
- msearch.py Loogle: `"gysinSupport"`: zero hits.
- msearch.py Mathlib grep, AlgebraicGeometry:
  `affineLine.*uniqu|orientation.*uniqu|gysinSupport`: zero hits.
- msearch.py LeanSearch: “The supported Kummer orientation of the affine line is
  uniquely determined by normalized restrictions at geometric points”. Eight hits
  concerning Kummer-Dedekind factorization or ordered real-linear orientations;
  none is the desired statement.
- rg of the upstream WeilConjectures tree and shared lean/Sheaf for
  `affineLine.*uniqu|orientation.*uniqu|prop-pur-affine-line-orientation-uniqueness`
  found the upstream EtaleCohomology/Purity/Smooth/Orientation.lean. I read
  `affineLineOrientation_hom_ext`,
  `affineLineOrientation_hom_ext_of_restrictAffineLineZeroLocusHom`, and
  `eq_affineLineOrientation_iff`, their full signatures and docstrings. They require
  `[HasKummerClass.IsNormalized Λ]` and concern a different etale zero-locus and
  coefficient interface. They do not state this concrete finite pro-etale theorem;
  adding that normalization hypothesis would lose the point of the current node.
- Upstream id search also found the corresponding AffineLine and Derived/GeometricPoint
  documentation. Shared Sheaf hits on orientation uniqueness were about oriented
  nearby-cycle topoi, not the affine-line supported orientation. There is no existing
  declaration of these helper names or this exact statement.

The maintenance repair note has stage 1, released: it concerns the previous proof split,
not a withdrawn Lean interface. This delivery keeps the current six-step proof route
and all node fields other than lean unchanged. No statement dispute, correction,
new independent notion or dependency-interface repair was necessary.

## Second reading by Q154

Worker self-check under the dispatcher's single-worker instructions; the maintainer's
independent review follows delivery. Reopened the node, the main-20261015 source
statement, the recorded orientation theorem and this module. The source Hom, all
geometric fibre groups, coordinate-boundary normalization, injectivity, existence of
the all-ones preimage and its uniqueness match clause by clause as listed above.
Checked particularly that residue_normalized refers to the fibre coordinate boundary,
not the restricted global m (which would permit an arbitrary rescaling), and that
charts/transports are produced rather than assumed. The source's finite-Tor category
causes no extra constraint on the Hom because it is full and both objects are already
in it by the dependency. No mismatch or node edit found; one 101-column signature
line was wrapped. All definitions are explicit composites or data packaging. Exactly
one theorem with a sorry remains, owned by this node.

## Validation and infrastructure repair

The retained packet initially failed because `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology`
was imported through `Sheaf.Paper.PurityRelativeKummer`; its legacy pro-etale
`LowerShriek` declaration collided with the finite-coefficient declaration already
imported by the rank-one calculation. I removed that unused proof-only import. The
repaired module now compiles through `scompile.py` in both sandbox and library-overlay
checks, with no errors or warnings. No upstream or shared Lean file was edited.

## Repair of returned split

The returned stage-1 review required the localization/Kummer paragraph and the
geometric restriction paragraph to expose their hidden arguments through cited
lemmas. I rewrote those two proof steps while retaining their route and all other
steps: the former is now 907 characters and cites the constructibility-origin,
localization-comparison, long-exact, relative-Kummer, Gysin, and orientation nodes;
the latter is now 1183 characters and cites supported-Hom naturality, support
pullback exactness, site comparison, geometric-point stalk, and rank-one normalization.
No statement or Lean declaration changed. The direct `Sheaf.Paper.PurityRelativeKummer`
import was removed because it imported the legacy pro-etale `LowerShriek` module and
collided with the finite-coefficient `LowerShriek` already supplied by the rank-one
calculation; the postponed theorem proof does not require that import to elaborate.
The repaired module compiles cleanly through `scompile.py`.
