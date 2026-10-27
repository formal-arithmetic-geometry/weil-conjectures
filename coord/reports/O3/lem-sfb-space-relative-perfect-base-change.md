## Worker report

Stage 2, O3, lem-sfb-space-relative-perfect-base-change. The inherited BLOCKED
ending concerned stage-1 re-splitting. The current coord/brief-stage2.md §0 expressly
permits this stage-2 statement delivery. There is no released repair note for this item.
The accepted statement and proof split are preserved. Only lean and additional
statement dependencies change in the item.

SpaceRelativePerfectBaseChange.lean states three named theorems, all with sorry proofs:
perfectRelativeToSpace_quasiCoherent, perfectRelativeToSpace_etale_local and
perfectRelativeToSpace_baseChange, in AlgebraicGeometry.AlgebraicSpace.

Clause-by-clause correspondence:

- The scheme S and algebraic spaces over S are `{S : Scheme.{u}}` and
  `{X Y : AlgebraicSpace S}`. Morphisms are `f : X ⟶ Y`, in the existing full
  subcategory of fppf sheaves. The small étale structure sheaf and module category
  are those of def-trf-algebraic-space and ringedSiteModules, without replacement.
- Flatness and local finite presentation are `hf : MapIsFlat f` and
  `hfp : MapIsLocallyOfFinitePresentation f`. Both are the recorded universal
  compatible-étale-scheme-chart tests of def-sfb-space-morphism-properties.
  Properness is explained in the node but is not assumed by this theorem; its
  recorded MapIsProper definition has exactly the stated three clauses.
- `K : X.DerivedModules`, under `[HasDerivedCategory.{w} X.SmallModules]`, is the
  unbounded derived category of the specified equivalent small ringed model.
  The new general-space predicate `IsPerfectRelativeToSpace f K` uses the existing
  `IsPerfectRelativeToScheme` on every target chart, pulling back K to the actual
  sheaf fibre product. That existing predicate spells out quasi-coherence,
  bounded-above finite-free local models and the test against ALL inverse-image
  ring-sheaf modules. On each affine chart its interval is finite; no interval is
  required uniformly across charts. Tags 0DKN and 0DKQ identify this chart criterion
  with the node's pseudo-coherent plus locally finite relative Tor dimension.
  Including the implied quasi-coherence in this equivalent criterion is inherited
  from the recorded scheme-target definition, not an extra hypothesis on K.
- `perfectRelativeToSpace_quasiCoherent` concludes `X.derivedQCohProperty K`.
  This is the recorded predicate that every cohomology object, transported by the
  inverse small-model equivalence, is Mathlib-quasi-coherent on the original site.
- In `perfectRelativeToSpace_etale_local`, `a : U ⟶ X`, `b : V ⟶ Y`,
  `h : U ⟶ V`, `ha`, `hb`, and `comm : a ≫ f = h ≫ b` encode the compatible
  étale square. Its first implication is restriction along every such square;
  its second implication detects the property if `IsSurjective a.hom.hom`.
  No target-surjectivity assumption is added. U and V may themselves be spaces,
  including represented scheme charts, so successive covering refinements are
  included. The top flatness and local finite presentation follow from those of f.
- In `perfectRelativeToSpace_baseChange`, `g : Y' ⟶ Y` is completely arbitrary.
  `square : IsPullback g'.hom f'.hom f.hom g.hom` says that X' with its two
  displayed projections is the sheaf fibre product, without choosing a different
  object or excluding an isomorphic realization. Its conclusion is exactly
  `IsPerfectRelativeToSpace f' ((derivedTensorPullback g').obj K)`.
- The new `derivedTensorPullback` is Mathlib's actual totalLeftDerived of the
  degreewise ordinary tensor pullback followed by localization. Its source and
  target localization sizes w and w' are independent. The functor's universal
  property and computation counit are retained by totalLeftDerived, and its
  existence theorem has the K-flat-resolution proof in its docstring. No arbitrary
  comparison map, arbitrary functor choice, or assumed base-change conclusion is used.
  The existing derivedDirectImage is the K-injective right derived functor; this
  theorem does not use direct image in any assertion.

Recorded dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsEtale, IsSurjective,
  EtaleSite, structureSheaf and Modules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, DerivedCategory.Q,
  HasDerivedCategory and HasDerivedCategory.standard.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its slice
  sheafification obligations; the underlying predicate is SheafOfModules.IsQuasicoherent.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: DerivedModules,
  derivedQCohProperty, derivedSchemeRestriction and the specified small-model equivalences.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect: IsPerfectRelativeToScheme.
  Its pseudo-coherence and finite Tor-dimension definitions were read upstream in
  WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex and FiniteTorDimensionOver.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback,
  moduleTensorAdjunction and the canonical compatible-chart moduleDirectImage.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsFlat,
  MapIsLocallyOfFinitePresentation, MapIsLocally and MapIsProper.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, used to bundle each actual chart pullback.
- Mathlib.CategoryTheory.Functor.Derived.LeftDerived: HasLeftDerivedFunctor and
  totalLeftDerived, the right Kan extension along the quasi-isomorphism localization.

The module also imports the available recorded proof modules
SpaceEtalePresentationPropertyCriterion, SchemeEtaleSourceTargetProperties,
BoundedAboveFlatSheafKFlat, RingedSiteRestrictionKFlat and
AlgebraicSpaceFibreProductsEtaleCovers, and the Mathlib finite-presentation and
quasi-separated permanence inputs. The geometric-stalk Tor test, strict-local
flatness, QCoh kernels/colimits, space flat/proper/fp locality, and relative-amplitude
proof dependencies have no recorded Lean declaration at the time of this delivery;
their proofs are not prerequisites for stating this theorem. No placeholder module
or fabricated import was introduced for them.

Edge cases checked before finalizing: the zero complex has interval [0,0] and
zero-rank free terms; the empty source has vacuous chart conditions; empty target
charts give empty fibre products; identity base change satisfies the displayed
pullback condition without any nonidentity assumption; arbitrary nonflat g is
allowed because flatness is imposed only on f; disconnected and non-quasi-compact
sources keep local rather than global bounds. No Noetherian, separated, proper,
quasi-compact or field hypothesis was added. Derived localization sizes w and w'
are independent, and the internal chart categories use their standard constructed
localization of size u+1, not an equality imposed on the ambient size.

Searches: msearch.py leanfinder queried “Relative perfectness of complexes on
algebraic spaces is etale local and preserved by arbitrary derived base change”:
eight scheme-property hits, no match. Loogle queried `"PerfectRelative",
"totalLeftDerived"`: zero hits. Mathlib grep queried
`IsPerfectRelativeToSpace|derivedTensorPullback|RelativePerfect|relativelyPerfect`:
zero hits. LeanSearch queried “canonical unbounded derived tensor pullback and
relative perfect complexes on algebraic spaces”: eight ordinary scheme/module
pullback hits, none the required derived-space construction. The sandbox's
searches.jsonl records the service responses. rg over lean/WeilConjectures and
lean/Sheaf found only the scheme-target predicate and derived direct image as
nearby existing interfaces; rg of the item id in WeilConjectures found no match.
DAG searches found no general-space relative-perfect or derived-space-pullback node;
blueprint_refs.py searches “relative perfect” and “derived tensor pullback” each
returned zero blueprint nodes. The already landed scheme-target and module-calculus
nodes are reused, not restated. New node mathlib_searches retain the returned
service-result records and the local search findings.

Source checked directly: literature/stacks-project/spaces-more-morphisms.tex,
definition-relatively-perfect, lemma-affine-locally-rel-perfect,
lemma-base-change-relatively-perfect; spaces-perfect.tex lemma-pseudo-coherent;
sites-cohomology.tex K-flat resolution and variant-derived-pullback. Citation 08H7
in the inherited draft was an unrelated equation; it is corrected to 08I6.
No STATEMENT-DISPUTED finding or change to the item's mathematical statement.

Validation: all three modules compiled separately in dependency order through
scompile.py against the live published library. The final delivery dry run repeats
per-file compilation. Every proof remains sorry; definitions have real data and
any supporting proof obligations are named theorems recorded with their owning nodes.

## New nodes

`def-sfb-space-derived-tensor-pullback`: SpaceDerivedTensorPullback.lean defines the
conjugate of the already fixed moduleTensorPullback, its complex functor and its
canonical totalLeftDerived. Named additive and derived-existence obligations are
included in lean.declarations and in the node's statement, with full proof docstrings.
Source: Stacks Tags 06YS, 06YY and 08I6. The Mathlib Kan-extension API exists and is reused;
its specialization to these algebraic spaces had no node or declaration, as the
searches above show. No data are chosen from a mere unnormalized existence theorem.

`def-sfb-space-relative-perfect-general`: SpaceRelativePerfectGeneral.lean constructs
the actual chart fibre products and projections and defines the general predicate
by the existing scheme-target one. Source: Stacks Tags 0DKN and 0DKQ. The existing
node def-sfb-space-relative-perfect restricts the target to a scheme, so it is
reused on target charts rather than incorrectly applied to an arbitrary space.
Every helper belongs to this construction, has real data, and is in lean.declarations.
The standard internal HasDerivedCategory instance is a real definition, not a sorry.

## Second reading by O3

A separate rereading was performed by the same dispatched worker; the dispatch
explicitly forbids starting other agents. The maintainer supplies the independent
review. This section does not claim that another agent reviewed this delivery.

With the accepted node and all three files open, I checked that both hf and hfp
occur in every theorem; K ranges over the entire unbounded ambient category;
quasi-coherence is the conclusion of the first theorem; both locality implications
appear and only the converse needs source surjectivity; g has no flatness hypothesis;
and the base-change square uses the actual sheaf maps. The finite-free/Tor clause
is expanded through IsPerfectRelativeToScheme and its two upstream predicates,
with all test modules and chart-dependent bounds retained. The internal fixed
localization size does not restrict either ambient localization universe.

The rereading corrected the inherited source tag 08H7 to 08I6 and added the direct
quasi-coherent statement import and available proof imports. It found no mathematical
statement mismatch. The two new nodes are definition nodes for absent notions;
their named supporting theorem obligations are expressly included in their statements.
The accepted split, source, proof and proof dependencies of the item remain unchanged.

Preflight schema repair: the current server requires import_flags on new nodes;
both new definition nodes therefore carry an empty import_flags list. The first
dry run compiled all modules and returned only these two missing-field errors.
