## Worker report

The module Sheaf.AlgebraicGeometry.FlatSpaceDerivedPushforwardBaseChange states the
five clauses of lem-sfb-flat-space-derived-pushforward-base-change. Every theorem
has precisely `by sorry`; it introduces no definitions and proves nothing.

Hypothesis and conclusion correspondence:

- The scheme is `{S : Scheme.{u}}`; all spaces are `AlgebraicSpace S` and all maps
  are their actual category morphisms. `HasDerivedCategory.{w}` binds the selected
  localizations for each participating SmallModules category, in an arbitrary
  common morphism universe w. This is the already recorded equivalent small
  ringed model, not a derived category of the abelian category QCoh.
- Flat f is `MapIsFlat f`, which tests Flat on compatible etale scheme charts.
  Quasi-compact f is `MapIsQuasiCompact f.hom.hom`; quasi-separated f is
  `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. No properness, finite
  presentation, separatedness, Noetherian, boundedness or flatness of g is required
  for the main result.
- Arbitrary g, the fibre product and its projections are rendered by f', g, h
  and `sq : IsPullback h f' f g`. Using any cartesian square includes the chosen
  fibre product and avoids an arbitrary identification of it.
- E is `E : X.DerivedModules` with `hE : X.derivedQCohProperty E`. This tests
  quasi-coherence in every integer cohomological degree after the inverse
  small-module equivalence.
- `flat_space_derived_baseChange_isIso` asserts
  `IsIso (moduleDerivedExchange f f' g h sq.w E)`. This existing definition is
  exactly the adjoint under the fixed derived adjunction for f' of the normalized
  pullback comparison followed by h-star of the f-counit. No exchange map is
  quantified as additional data.
- `flat_space_derived_baseChange_preservesQCoh` gives four quantified implications,
  one for Rf_*, Lg*, Lh*, Rf'_*, on their respective D_QCoh objects. Consequently
  both sides of the displayed comparison have quasi-coherent cohomology.
- `flat_space_derived_baseChange_id` says that exchange for g=id_Y, h=id_X,
  followed by Rf_* of the X pullback-identity comparison, equals the Y
  pullback-identity comparison at Rf_*E. Thus it is the identity after precisely
  the canonical identifications.
- `flat_space_derived_baseChange_comp` uses an arbitrary second cartesian square
  with f'', a, b. `sq'.paste_horiz sq` is the outer square. The outer exchange
  followed by Rf''_* of the h,b compositor equals the g,a compositor followed by
  La* of the first exchange and the second exchange at Lh*E. This is equality
  of the specified maps, with the source and target comparison directions read
  directly from `spaceDerivedPullbackComp`.
- `flat_space_derived_baseChange_proper_fp` assumes `MapIsProper f`, `MapIsFlat f`,
  local finite presentation, qc and qs. It concludes the same five predicates
  for f'. The last three jointly mean finite presentation, as in the dependency
  flat_proper_fp_locality. Proper means separated, finite type and universally
  closed in MapIsProper, exactly the node's convention.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, category morphisms.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, small etale structure
  sheaf and Modules (the full declarations and docstrings were read).
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently the Mathlib SheafOfModules category.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and
  HasDerivedCategory, localization of all Z-indexed complexes.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh, with Mathlib's
  SheafOfModules.IsQuasicoherent, and the slice sheafification instances.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: DerivedModules,
  derivedQCohProperty, derivedDirectImage; the latter is the K-injective right
  derived compatible-chart direct image conjugated by the small equivalences.
- Sheaf.AlgebraicGeometry.SpaceDerivedPullback: spaceDerivedPullback,
  spaceDerivedPullbackComp and spaceDerivedPullbackId, normalized on the ordinary
  tensor formulas and the universal derived counits.
- Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange: moduleDerivedExchange,
  the existing actual adjunction mate.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsFlat,
  MapIsProper, MapIsLocallyOfFinitePresentation.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: MapIsQuasiCompact and the explicit
  presheaf relative diagonal for quasi-separatedness.

The latter five landed definition owners are added to stmt_deps so the new
statement explicitly cites the existing constructions. No node is recreated.
Proof imports are SpaceFlatComplexBaseChange, SpaceDerivedEtaleChartCalculus,
AlgebraicSpaceFlatProperFpLocality, SpaceStrictLocalFlatness,
KFlatIndependentCoefficients and Mathlib.CategoryTheory.Adjunction.Mates. The
proof prerequisite lem-sfb-qcqs-space-pushforward-right-adjoint has no usable
Lean record/mathlib_match in this snapshot, so there is no recorded module to
import for it; its application is still spelled out in the preservation proof
docstring. It is only a future proof dependency, not needed to type this statement.

Sources inspected: spaces-perfect.tex lemma-compare-base-change (08IR), including
its canonical arrow and QCoh checks, and lemma-base-change-tensor (0A1K), including
its ordinary coefficient pullback. sites-cohomology.tex remarks compose-base-change
(0E46) and compose-base-change-horizontal (0E47) give the pasting equations.
The stability interface flat_proper_fp_locality was read against its source tags
03MO, 04WP, 03XR and the definitions in AlgebraicSpaceMorphismProperties.

Edge cases checked before writing: E=0; empty source and empty fibre product;
identity g and successive identity maps; unbounded E in both directions; arbitrary
nonflat g (including nilpotent closed immersions); f flat but neither proper nor
finitely presented; arbitrary characteristic; non-qc target; and arbitrary common
localization morphism universe w. The preservation claim is on relative qcqs
morphisms, so no global qcqs hypotheses are silently imposed on X or Y. The
proper/fp clause does not impose dimension-one fibres or any curve condition.
There is no statement dispute or correction.

Searches:

- msearch.py leanfinder, query "Flat algebraic space derived pushforward quasi
  coherent unbounded complexes arbitrary derived base change": eight hits,
  only scheme Flat and ordinary scheme module adjunction facts; no match.
- msearch.py loogle, query "AlgebraicGeometry.Scheme.Modules.pushforward,
  CategoryTheory.mateEquiv_vcomp": zero hits.
- msearch.py leansearch, query "Flat quasi compact quasi separated algebraic
  space derived pushforward base change": eight hits on stability under base
  change of ordinary scheme/ring properties; no match.
- msearch.py grep, query `derived.*[Bb]ase[Cc]hange|base[Cc]hange.*derived`,
  Mathlib AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures for the item id and derived/base-change variants:
  generic coefficient base change, scheme theorems and etale sheaf theorems;
  none is this algebraic-space statement.
- rg in lean/Sheaf/AlgebraicGeometry for derived/base-change variants: the
  existing SpaceModuleDerivedExchange, relatively flat complex theorem, chart
  calculus and flat ordinary direct-image theorem are reused. None states all
  five clauses of this node. New declaration names are prefixed
  flat_space_derived_baseChange and were checked for collisions.

## Second reading by Q25

Author's second reading (no independent worker was started, as the dispatcher
requires): reopened the node, each dependency signature, and the delivered file.
The invertibility theorem uses flat f rather than flat g. The preservation
statement covers all four functors, not just the two resulting composite objects.
The identity equation uses the source and target unit isomorphisms in their
correct directions. For composition, the outer square is sq'.paste_horiz sq;
the source compositor is for g,a and the target compositor is for h,b. All three
exchanges are the existing normalized mate, and equality is at E, not merely
existence of isomorphic objects. The final statement returns all three properties,
with finite presentation expanded to local finite presentation, qc and qs.
All variable and universe binders are explicit; no extra all-spaces localization
family is assumed. No discrepancy or change to the informal statement was found.
Independent review is left to the maintainer's delivery review as the brief says.

Validation: scompile.py compiled both the module-mode sandbox probe and the exact
library module without errors or unexpected warnings (library compile 9.6 seconds).
deliver2.py --no-push passed the server preflight and per-file compile. No local
Lean compile, global build, direct shared-tree edit or direct git operation was run.
