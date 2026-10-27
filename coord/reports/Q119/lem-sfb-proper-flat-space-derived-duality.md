## Worker report

Item: lem-sfb-proper-flat-space-derived-duality. Group Q119, 2026-10-24 UTC.
The node statement and accepted proof split are unchanged. Its statement dependencies
only gain the new trace-pair definition and already landed definitions used here.
All four theorem proofs are `sorry`; both modules' definitions contain real data.

The delivery consists of RelativeDualizingTracePair.lean and
ProperFlatSpaceDerivedDuality.lean under lean/Sheaf/AlgebraicGeometry, together with
the item record and the new definition record. No dependency record is replaced.

Hypothesis and clause matching:

1. The scheme T is `Y.left`, for `Y : Over S`, with `S : Scheme.{u}` arbitrary.
   `schemeSpace Y` is the existing actual Yoneda-represented algebraic space.
   `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace Y` retain algebraic spaces;
   there is no replacement of X by a scheme. Every morphism over an arbitrary
   scheme T is covered by this presentation (one can take the ambient S=T).
2. Proper, flat and finitely presented are `hproper : MapIsProper f`,
   `hflat : MapIsFlat f` and `hfp : MapIsLocallyOfFinitePresentation f`.
   The first unfolds to separated, finite type and universally closed.
   Flatness and local finite presentation use every compatible étale pair of
   scheme charts. Properness already gives quasi-compactness and
   quasi-separatedness, so local finite presentation is finite presentation here.
3. `X.DerivedModules` is the existing unbounded derived category of module
   sheaves on the equivalent small affine étale ringed model. It uses the
   original module universe u. `X.derivedQCohProperty` tests the existing
   `SheafOfModules.IsQuasicoherent` on every cohomology object after the inverse
   of the actual module restriction equivalence. It is the full D_QCoh subcategory,
   rather than D(QCoh). `derivedDirectImage` is the canonical K-injective right
   derived direct image; `spaceDerivedPullback` is the canonical K-flat tensor
   pullback. No new abelian instance, derived category or functor replaces them.
4. `∃ P : RelativeDualizingTracePair Y f` supplies the complex and actual trace.
   The fields are `P.complex : X.DerivedModules` and
   `P.trace : (derivedDirectImage f).obj P.complex ⟶ (schemeSpace Y).derivedStructure`.
   `IsRelativeDualizingTracePair P` explicitly includes quasi-coherent cohomology.
5. Pseudo-coherence is the landed `IsPseudoCoherent X P.complex`: local
   bounded-above finite-free models, with ranks allowed to vary by degree.
   The next conjunct of `properFlatSpaceDerivedDuality` says that on a covering
   sieve of every small étale basis object, each covering member has integers a,b
   outside which the restrictions of H^n(P.complex) vanish. Exact restriction
   makes this precisely local cohomological boundedness. There is no single
   global bound, no finite lower bound on the free resolution, and no perfectness
   assumption on the fibres.
6. In the defining property, `A : Type u` with `[CommRing A]`,
   `Y' : Over S`, `a : Y'.left ≅ Spec (.of A)` and `g : Y' ⟶ Y`
   range over all affine tests. `X'`, `p`, `f'`, and
   `sq : IsPullback p f' f (traceSchemeMap g)` describe every realization of
   the actual fibre product, rather than assume a particular chosen pullback.
7. The existential `t` is a trace on the actual object
   `(spaceDerivedPullback p).obj P.complex`. `TraceBaseChangeCompatible`
   requires beta followed by this trace to be the original trace pulled back
   and followed by the canonical structure pullback. Here beta is exactly
   `moduleDerivedExchange`, the adjoint of the pulled canonical counit.
   This equation is the pulled-trace formula with beta inverse moved to the
   other side; in the proper-flat situation beta is invertible. No arbitrary
   map or arbitrary structure-sheaf identification stands in for it.
8. `affineDualizingTraceHom A Y' a f' ... t E` first uses
   `affineDerivedSectionsComposition.hom.app E`, then applies derived sections
   to `Rf'_*h ≫ t`, then uses `affineStructureDerivedIso.hom`.
   Thus its target is literally a morphism in `DerivedCategory (ModuleCat A)`
   from the actual RΓ(X',E) to A in degree zero. The defining predicate requires
   `Function.Bijective` on this exact map for every E with quasi-coherent
   cohomology, including unbounded E. Naturality in E follows from this fixed
   composition formula and functoriality; an arbitrary family of equivalences
   is not substituted for the trace-induced maps.
9. Uniqueness is `∀ Q, IsRelativeDualizingTracePair Q → ∃! e, TracePreserving P Q e`.
   The witness e is an isomorphism of the actual ambient derived objects;
   `TracePreserving` is the equation `Rf_*e.hom ≫ Q.trace = P.trace`.
10. Arbitrary scheme base change is the final conjunct. No property is imposed
    on g. It both supplies a dualizing trace on Lp*P.complex and gives the unique
    trace-compatible isomorphism from that object to every relative dualizing
    pair Q on f'. This includes nonflat base change.
11. Identity coherence is `properFlatSpaceDerivedDuality_id`, fixing the unique
    comparison to `(spaceDerivedPullbackId X).app P.complex`.
    Iterated coherence is `properFlatSpaceDerivedDuality_comp`, equating the
    direct comparison with the canonical derived composition followed by the
    pullback of the first comparison and the second comparison. The outer
    commutativity follows from the two supplied cartesian squares; no extra
    outer-square assumption was retained.
12. For schemes and affine target, `properFlatSpaceDerivedDuality_schemeComparison`
    specializes X to `schemeSpace U`, f to `traceSchemeMap f`, and assumes only
    `[IsAffine Y.left]` in addition to the same geometric hypotheses.
    It asserts that a `SchemeDualizingTraceComparison f` exists. Its source and
    target equivalences have underlying functors naturally isomorphic to the
    actual right-derived `smallSchemeRestriction` at the identity scheme chart,
    i.e. R epsilon_*. Its two pushforward presentations are identified with the
    existing étale `derivedDirectImage` and Zariski
    `RingedSpace.derivedModuleDirectImage f.left.toLRSHom.toShHom`.
    The structure object is explicitly identified with O_Y[0]. For every
    presentation of this comparison the Zariski pushforward has a right adjoint.
    For every such adjunction the theorem gives the unique trace-preserving
    isomorphism to the étale image of f!O. `schemeDualizingAdjunctionTrace`
    is the displayed composite of the ambient pushforward presentation,
    comparison square, actual adjunction counit, and structure comparison.
    Quantifying over presentations includes the canonical comparison and avoids
    dependence on a particular presentation or choice of right adjoint. The
    existence clause prevents a conditional comparison with no realization.
13. There is no dimension, smoothness, Gorenstein, connectedness, reducedness,
    Noetherian, or projectivity assumption. The localization morphism sizes w
    (space model) and wZ (Zariski modules) are explicit and independent; the
    module coefficient and test-scheme universe stays u. HasDerivedCategory
    binders select localizations and add no geometric restriction.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`; their exact fppf-sheaf and chart-based definitions.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, and their chosen localization signatures.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`,
  the abbreviation of Mathlib `SheafOfModules` for an arbitrary ringed site.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent`; no substitute quasi-coherence.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`, `derivedStructure`, `derivedDirectImage`,
  `QCohDirectImagePresentation`, `smallSchemeRestriction`.
- Sheaf.AlgebraicGeometry.SpaceDerivedPullback: `spaceDerivedPullback`,
  `spaceDerivedPullbackComp`, `spaceDerivedPullbackId`.
- Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange: `moduleDerivedExchange`.
- Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors:
  `affineDerivedSectionsComposition`, `affineStructureDerivedIso`.
- Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange:
  `relativeClosedKernelDerivedStructureMap`; this is the existing canonical
  derived structure pullback, without any use of the closed-kernel specialization.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsProper`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex: `IsPseudoCoherent`.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage:
  `RingedSpace.derivedModuleDirectImage`.

Already stated proof dependencies are plain imports: AffineAdjointUnitProperties,
AffineEtaleHypercoverRefinement, SpaceNegativeExtHyperdescent,
SpaceRelativePerfectBaseChange, AffineEtaleDerivedModuleRealization.
The other proof-dependency records currently have no usable declaration; no
unstated proof dependency is used as a replacement for a statement's data.
The comparison helpers required to type this item are supplied in its own module.

Edge cases checked: X empty, T empty, zero test ring A, zero test complex,
negative and arbitrarily high shifts of E, non-quasi-compact T (local rather than
uniform bounds), nonreduced/non-Noetherian base, identity base change, nonflat
base change and two successive base changes. Covering-sieve formulations allow
empty objects. Scheme comparison is required only for affine T, as in the node.
The source explicitly permits dropping relative perfectness from the definition
of the dualizing property, since the affine Hom property implies it. Local
boundedness is cohomological boundedness and does not make K perfect over O_X.

Searches:

- msearch.py leanfinder: "Existence uniqueness arbitrary base change relative
  dualizing complex proper flat finitely presented algebraic spaces". Eight
  ordinary morphism-property hits, no duality result.
- msearch.py loogle: "DerivedCategory, AlgebraicGeometry.AlgebraicSpace".
  Zero hits; AlgebraicSpace is not a Mathlib identifier.
- msearch.py grep: "relativeDualizing|RelativeDualizing|dualizingComplex".
  Zero Mathlib hits.
- msearch.py leansearch: "Relative dualizing complex trace for proper flat
  morphisms of algebraic spaces". Eight algebraic trace/ordinary flatness hits,
  no matching theorem. The more specific searches for the new definition,
  with raw outputs, are recorded in its mathlib_searches.
- rg on lean/WeilConjectures and lean/Sheaf by relative-dualizing names and
  the item id: the existing RelativeDualizingPair modules define the diagonal
  fundamental-class notion for separated scheme morphisms. They do not give
  this proper-flat algebraic-space trace pair. The pro-étale coefficient dualizing
  complexes also have different coefficients and sites. No exact declaration
  exists. The morphism, derived, scalar-section, and structure-map APIs found
  in this search are reused.
- rg on dag/nodes for the new id and proposed Lean names: no existing node.
  tools/blueprint_refs.py search "relative dualizing": three blueprint nodes,
  all concerning the six-functor coefficient dualizing complex, not this notion.
  The existing scheme diagonal-pair base-change node was also read and is distinct.

Source reading: spaces-duality.tex definition-relative-dualizing-proper-flat,
its remarks, existence, uniqueness, base-change and scheme comparison; and
spaces-more-morphisms.tex definition-relatively-perfect. The local boundedness
claim follows by testing finite relative Tor dimension against the inverse-image
structure module itself. No statement dispute or correction was necessary.

Validation: scompile.py compiled both files separately in dependency order against
its private server overlay. Both passed with no diagnostics. The main module was
also compiled under its actual library module name, not just as an import probe.
Every statement variable and universe is explicitly bound; autoImplicit is false.

## New nodes

`def-sfb-relative-dualizing-trace-pair` defines the raw complex/trace pair, its
trace-preserving isomorphisms, the canonical base-change trace equation, the
explicit affine Hom map, and the affine-test dualizing property. Its source is
Stacks 0E5X and the first two remarks, with trace preservation from 0E5Z and 0E6C.
LeanSearch, LeanFinder and Mathlib grep raw results are in its mathlib_searches;
DAG/blueprint and project searches distinguish it from diagonal classes and
coefficient duality. All its underlying categories and maps are reused from
landed nodes. It introduces no theorem proof obligation or chosen object.

## Second reading by Q119

This is the dispatch worker's separate rereading of the node and both finished
files. No other agent was started, in accordance with the explicit dispatch
instruction; the maintainer supplies the independent delivery review.

I checked the thirteen clause matches above against the declarations. The first
compile exposed only proof-term elaboration for the identity-square equation;
this was replaced by the explicit Yoneda map_id identification. I also removed
a redundant outer cartesian-square binder from the composition theorem: the
commutativity needed there is derived from the two given squares. No geometric
hypothesis, cohomological degree, base-change case, or trace equation changed.

I separately checked that the new definition's trace Hom has target A[0] in D(A),
that its RGamma compositor points from RGamma(X',E) to RGamma(Y',Rf'_*E),
that beta points from La*Rf_* to Rf'_*Lp*, and that trace compatibility therefore
has the correct direction. In the scheme clause the transported trace starts
at the actual ambient Rf_* of the transported f!O and ends at O, passing through
the chosen adjunction's actual counit. All data definitions were reread for sorry
or arbitrary-map substitutions; none occurs. The four postponed statements all
have the source and the corresponding complete natural-language proof argument.
