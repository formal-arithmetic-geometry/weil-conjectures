## Worker report

Q73 states `lem-sfb-proper-flat-space-derived-base-change` in
`Sheaf.AlgebraicGeometry.ProperFlatSpaceDerivedBaseChange`, declaration
`AlgebraicGeometry.AlgebraicSpace.properFlatSpace_derivedBaseChange`.
The proof is `sorry`; no definition contains a postponed proof. The signature asserts
`Nonempty (ProperFlatSpaceDerivedBaseChangeSystem (S := S))`. This packages simultaneous
presentations of canonical epsilon adjunctions together with all the node's conclusions;
it does not assume existence of these presentations as a hypothesis. Every comparison
used in the conclusions is normalized by actual sections or universal derived units.
The source statement, proof and proof dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Schemes and spaces: `S : Scheme.{u}`, `Y : Over S`, `X : AlgebraicSpace S`, and
  `f : X ⟶ schemeSpace Y`. The represented object is the existing algebraic space of
  the scheme. Every scheme map `g : Y' ⟶ Y` is allowed. A diagram over any scheme can
  be viewed over its target; the use of a fixed ambient base adds no restriction.
* Flat proper finitely presented: `MapIsProper f`, `MapIsFlat f`, and
  `MapIsLocallyOfFinitePresentation f`. Properness already includes quasi-compactness,
  so local finite presentation gives finite presentation. The recorded definitions
  test flatness and local finite presentation on scheme charts, and properness is
  separatedness, finite type, and universal closedness. No replacement predicate is used.
* Coefficients: `M : X.Modules`, `M.IsQuasicoherent`, `M.IsFinitePresentation`, and
  `ModuleIsFlatOver f M`. These are the existing module, local-presentation, and
  compatible-chart stalk-flatness definitions, including arbitrary etale target charts.
* Degree zero: `properFlatSpaceCoefficient X M` uses actual small-model restriction
  followed by `DerivedCategory.singleFunctor ... 0`; the coefficient is not a freely
  chosen derived object. Derived categories are the recorded unbounded localizations.
* The displayed K: `properFlatSpaceImage f M` is exactly the value of
  `X.smallModuleRestriction ⋙ singleFunctor _ 0 ⋙ derivedDirectImage f ⋙
  (spaceZariskiRestriction Y).rightDerivedFunctor`. Here Zariski restriction is the
  recorded restriction to all opens through the actual small affine basis equivalence.
* Perfectness: `ProperFlatSpaceDerivedBaseChangeSystem.perfect` concludes
  `Scheme.IsPerfect Y.left (properFlatSpaceImage f M)` under precisely the listed
  morphism and coefficient hypotheses. It uses the existing local strict-perfect notion.
* Epsilon exactness: `data Y` has `context.extension`, its canonical adjunction to
  restriction, additivity, `PreservesFiniteLimits`, and `PreservesFiniteColimits`.
  This is exactness on the abelian module categories. Its derived extension is
  induced by termwise extension, with an explicit localization factorization.
* Canonical epsilon counit: `counit` asserts `IsIso` of `data Y`'s derived adjunction
  counit at `derivedDirectImage f` of the degree-zero coefficient. The adjunction is
  normalized by the ordinary homotopy adjunction and the universal right-derived unit.
* Arbitrary base change: `baseChange` quantifies all `Y,Y',X,X',f,f',g,p` and an
  `IsPullback p f' f (traceSchemeMap g)`. There is no flatness hypothesis on `g` or `p`.
  The target coefficient is the ordinary `(moduleTensorPullback p).obj M`, not a
  derived coefficient and not a replacement supplied as additional input.
* Canonical morphism: `properFlatSpaceCoefficientMap` is the fixed derived-pullback
  comparison on the single complex, followed by termwise single-complex and actual
  restriction comparisons. `properFlatSpaceEtaleBaseChange` is the existing
  `moduleDerivedExchange` followed by this coefficient map. `properFlatSpaceBaseChange`
  is its epsilon adjoint after the canonical pullback comparison and pulled counit.
  The field `baseChange` asserts `IsIso` of this actual morphism.
* Small-etale identification: `etaleIdentification` writes the exact morphism equality
  between epsilon extension of the Zariski map followed by the target counit, and the
  pullback comparison followed by the pulled source counit and etale exchange map.
  Thus identifying source and target by their counits gives the asserted usual map.
* Identity: `identity` explicitly compares the identity-base-change map followed by
  the recorded ordinary pullback identity with the recorded derived pullback identity.
  The latter is selected from the same canonical compositor construction as upstream.
* Composition: `composition` quantifies two Cartesian squares and writes equality
  of the iterated base-change map, followed by `moduleTensorComposition q p`, with
  the composite-base-change map preceded by `canonicalDerivedPullbackComposition`.
  The commutativity proof for the composite square is universally quantified; it
  supplies no extra mathematical assumption and avoids silently choosing transports.
* Scalar unit: `scalar` specializes to `SheafOfModules.unit X.structureSheaf` and
  asserts equality after `properFlatSpaceOrdinaryStructure p` with
  `properFlatSpaceZariskiStructure g ≫ properFlatSpaceScalar f'`. The scalar maps
  are constructed from regular-function pullback, the actual basis restriction unit,
  and universal right-derived units; the structure pullbacks are adjunction transposes.
* No dimension bound, reducedness, or Noetherianness occurs. Universes `u,w` are
  explicit and independent. The common `HasDerivedCategory.{w}` assumptions are
  localization existence/size infrastructure on all participating module categories,
  including open over-sites needed by the existing `Scheme.IsPerfect` definition.

Dependency declarations used (all in namespace `AlgebraicGeometry.AlgebraicSpace`
unless qualified below):

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  genuine etale site, structure sheaf and scheme representation; Mathlib's Scheme.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `smallSchemeRestriction`,
  `smallModuleDirectImage`, `derivedDirectImage`, and `DerivedModules`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeOpens`,
  `schemeOpensRingHom`, `schemeOpens_isContinuous`, and `schemeRestriction`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleDirectImageModel`, `moduleTensorPullback`, and `moduleTensorAdjunction`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsFlat`, and `MapIsLocallyOfFinitePresentation`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`: `ModuleIsFlatOver`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`,
  `spaceDerivedPullbackCounit`, and `moduleTensorPullbackId`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`: `smallRestrictionPullback`;
  the existing small tensor pullback and complex comparison are reused.
* `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `affineIdentityChart`,
  `spaceRightDerivedComplexUnit`, and `spaceDerivedAdjunction`.
* `Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors`: `smallModuleUnitIso`
  and `fullModuleSection`.
* `Sheaf.AlgebraicGeometry.RelativeDualizingTracePair`: `traceSchemeMap`,
  `traceSmallStructureMap`, and `traceDirectImageComparison`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`.
* `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`: `moduleTensorComposition`;
  the recorded module-derived exchange is used, via its public dependency chain.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`;
  `WeilConjectures.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`;
  `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
* `WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation`:
  `canonicalSchemeDerivedAdjunction`, `canonicalDerivedPullbackComposition`;
  its upstream `exists_derivedPullbackComposition` supplies the corresponding identity.
* `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, and its public ringed-space dependency's
  `AlgebraicGeometry.RingedSpace.moduleDirectImage`.
* Mathlib: `DerivedCategory.singleFunctor`, its comparison with `Q`, termwise
  complex comparison, `Adjunction.homEquiv`, `conjugateIsoEquiv`, and `IsPullback`.

Proof-only imports cover the recorded proper-support theorem, derived
etale/Zariski equivalence, flat-complex base change, scheme derived pullback of QCoh,
and Mathlib adjunction mates. The perfectness-detection proof dependency currently
has no additional usable module to import; the complete natural-language proof
identifies its role. No proof is attempted at stage 2.

Edge cases checked before finalizing: the zero module and empty space need no
nonemptiness or nonzero coefficient condition; arbitrary nonflat scheme base changes
remain quantified; identity squares retain both ordinary and derived identity
comparisons; repeated base changes retain the ordinary coefficient compositor;
structure coefficients use the genuine regular-function unit. Unbounded derived
objects and arbitrary common localization universe are retained. In particular,
relative flatness is never used to assert `Lp* M = p* M` for arbitrary `p`.

Source checks: read local `spaces-perfect.tex` at Tags 0CTM, 071Q, 08H8, 08HG,
and 08GH and their stated scheme/space conventions. The theorem follows 0CTM
specialized to base equal to target, with exact epsilon and canonical transport.

Searches: the prescribed msearch LeanFinder query about proper flat perfect derived
images returned eight flat-geometry declarations; Loogle `AlgebraicGeometry.Flat,
CategoryTheory.IsIso` returned six underived flatness/isomorphism declarations;
Mathlib grep `properFlatSpace|proper_flat.*perfect|flat_proper.*perfect` returned zero.
LeanSearch about canonical Zariski/derived restriction returned eight ordinary scheme
restriction comparisons, not this affine-model interface. LeanFinder about the
small-etale/Zariski adjunction returned eight ordinary scheme adjunction declarations.
Mathlib grep `Zariski.*derived|derived.*Zariski` and
`SpaceZariski|spaceZariski|smallSchemeRestriction` returned zero. Raw wrapper records
are reproduced in both new nodes' `mathlib_searches`. Searches of `lean/WeilConjectures`
and `lean/Sheaf` found the reusable ordinary restriction and existing scheme-native
QCoh equivalence; no declaration states this theorem. Searching the item id in
`lean/WeilConjectures` found none. DAG/blueprint searches found no duplicate normalized
small-affine Zariski comparison node. No statement is disputed or corrected.

Validation: all delivered modules are checked individually, in dependency order,
by the prescribed server `scompile.py`. The only postponed theorem is the main
statement, with the node's six-step proof in its docstring. The delivery dry run
and its per-file checks are run before pushing.

## Second reading by Q73

This dispatcher assigned a single worker and explicitly prohibited starting other
agents, so this is a second reading by the same worker, not an independent review.
Independent review remains with the maintainer as specified in the brief. Reopened
the node and all three files and checked the above clause mapping. During this
reading the ordinary square was pinned to the actual preimage-open chart and its
regular-function map; the derived square and adjunction were pinned to universal
right-derived units, avoiding arbitrary comparison choices. The coefficient was
kept as ordinary pullback in the target. Identity, composite coefficient transport,
and scalar normalization are explicit equalities. All hypotheses occur on the
perfectness, counit, and base-change clauses; scalar uses the structure module,
which satisfies the coefficient conditions under the morphism hypotheses. The
new-node statements describe exactly the structures and maps of their own modules.
No mismatch remains in this reading. No independent worker reading is claimed.

## New nodes

`def-sfb-space-zariski-ordinary-comparison`, module
`Sheaf.AlgebraicGeometry.SpaceZariskiOrdinaryComparison`, introduces the ordinary
comparison data on the already fixed small affine model of a represented scheme.
It reuses `smallSchemeRestriction`, ordinary direct images, and the existing basis
equivalence. The ordinary isomorphism is constrained by the direct-image limit
projection on the actual preimage open, including the basis-equivalence unit and
chart-map equation. Sources: Stacks 03FH and 08GH. Mathlib and project/DAG searches
listed above found only constituent definitions. In particular the existing
scheme-native epsilon construction is on another site, and does not supply this
basis-conjugated section-normalized square. This node does not construct a second
module category, direct image, or restriction functor.

`def-sfb-space-zariski-derived-comparison`, module
`Sheaf.AlgebraicGeometry.SpaceZariskiDerivedComparison`, introduces normalized
presentations of exact epsilon extension, its derived adjunction, the derived
right square and its adjunction-conjugate pullback square on those same models.
The derived extension is required to factor the actual termwise extension; the
adjunction and right square satisfy representative equations with the universal
derived units. Sources: Stacks 071Q, 08H8 and 08GH. The same logged LeanSearch,
LeanFinder and Mathlib/project/DAG searches found no such interface. Existing
scheme-native QCoh equivalences do not identify their presentation with the
recorded algebraic-space small affine model. This definition supplies the
necessary canonical transport interface; its simultaneous existence is part of
the delivered main theorem, never an extra hypothesis. Both new definitions have
real structure data and no postponed theorem or hollow definition.
