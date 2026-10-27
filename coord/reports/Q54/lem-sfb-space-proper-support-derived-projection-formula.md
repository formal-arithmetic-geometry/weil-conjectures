## Worker report

The main module is `Sheaf.AlgebraicGeometry.SpaceProperSupportDerivedProjectionFormula`.
Its theorem `AlgebraicGeometry.AlgebraicSpace.spaceProperSupportDerivedProjectionFormula`
states invertibility in the unbounded derived category of the canonical projection mate
followed by the canonical balanced scalar-restriction identification. The item statement
is unchanged. Every theorem proof in this packet is `sorry`; definitions contain actual
functor, universal-derived-functor, normalized-choice, or adjunction-mate data.

Hypothesis and clause correspondence:

- The scheme S and algebraic spaces X,Y over it are `{S : Scheme.{u}}`
  and `{X Y : AlgebraicSpace S}`. The morphism is `f : X ⟶ Y`.
- The size convention is explicit `universe u w`, using the recorded equivalent
  small affine models `X.SmallModules`, `Y.SmallModules` in coefficient universe u,
  and only their participating `HasDerivedCategory.{w}` instances. No equality of
  site-object and morphism universes is imposed on the original site: the existing
  small model is used through its existing module equivalence.
- Noetherian Y is the conjunction of the three separate hypotheses `hYln`, `hYqc`,
  `hYqs`: local Noetherianity on every etale scheme chart; compactness of the point
  space; absolute quasi-separatedness. This does not assume Y separated over S.
- Locally finite type f is `hflft : MapIsLocally (@LocallyOfFiniteType) f`, tested
  on compatible etale scheme charts. Quasi-separated f is `hfqs`, quasi-compactness
  of its relative diagonal, using the existing affine-test predicate. No compactness
  of X or f occurs.
- E is an arbitrary object of `X.DerivedModules`, not a complex of QCoh objects.
  `hEcoh` says each cohomology module, transported by the existing inverse
  small-model equivalence, satisfies `SheafOfModules.IsFinitePresentation`.
  The local-Noetherian consequence of the hypotheses makes this precisely the
  node's quasi-coherent finite-generation condition. This is the convention already
  used by the closed-coherent and coherent-filtered-union algebraic-space modules.
- `hEb` supplies a finite interval a ≤ b and `IsZero` cohomology outside it.
- `hEsupp` gives in each degree a `ClosedSubspace X` that is reduced, whose point
  image is exactly `moduleSupport` of the cohomology module and whose composite
  with f satisfies `MapIsProper`. Thus it is the reduced induced closed support,
  rather than an arbitrary proper space or an assumption of properness of f.
  `moduleSupport` is the existing locus of nonzero geometric germs.
- Every quasi-coherent module F is covered by `(F : Y.QCoh)` with its original
  `SheafOfModules.IsQuasicoherent` predicate. The expression
  `(DerivedCategory.singleFunctor Y.SmallModules 0).obj
  (Y.smallModuleRestriction.obj F.obj)` is precisely F[0].
- The conclusion is `IsIso (spaceRelativeProjectionComparison f E F[0])`.
  The domain of that actual morphism is the existing derived tensor of Rf_*E and
  F[0]; its codomain is Rf_* of `spaceRelativeDerivedTensor f (E,F[0])`, retaining
  its O_X-action through E. `spaceProjectionComparison` is the adjoint of the
  normalized pullback tensor comparison then counit on E. Its composite with
  Rf_* of `spaceRelativeTensorComparison` is exactly the specified relative map.
  It is not an unspecified isomorphism of these objects.
- `spaceRelativeProjectionComparison_naturality` states bifunctoriality on all
  derived objects and morphisms, so its invertibility on the stated inputs gives
  the requested natural isomorphism. No flatness, relative Tor, or compactness
  hypothesis on f appears, and the tensor output need not be bounded.

Dependency declarations used (all read with their signatures and source docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its actual small etale site, structure sheaf and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the HomologySequence module supplies
  `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with
  Mathlib's `SheafOfModules.IsQuasicoherent`; finite presentation is also Mathlib's.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection` with its scalar-one normalization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedDirectImage`, `derivedDualityModel` and the existing small-model equivalence.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`:
  `smallModuleTensorPullback`, `derivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`,
  `spaceDerivedPullbackCounit`; `SpaceAffineHomComparison`: `spaceDerivedAdjunction`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`:
  `moduleDerivedPullbackTensor` and its complete flat-term K-flat normalization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper`; `ProperCurveModuli` exports the existing `MapIsQuasiCompact`.
- `AlgebraicSpaceAbsoluteQuasiSeparated`: `IsAbsolutelyQuasiSeparated`;
  `AlgebraicSpaceModuleSupport`: `moduleSupport`; `AlgebraicSpaceClosedSubspace`:
  `ClosedSubspace`; `ReducedAlgebraicSpace`: `IsReduced`;
  `ReducedClosedSubspaceSupport`: uniqueness of reduced closed support.

Every recorded proof dependency already stated is imported: etale open image,
derived etale chart calculus, elementary shriek exactness, generic ringed-topos
canonical tensor pullback, and ringed projection tensor composition. The remaining
proof nodes currently have no Lean record, so there is no module to import from them.
The complete six-step item proof is retained in the main theorem's docstring, including
its comparison-mate identification. The new definition's proof obligations each have
source and complete proof docstrings and are covered explicitly by its node statement.

Edge cases checked before writing: E=0, the empty space and empty support, zero F,
a one-degree interval a=b, arbitrary negative endpoints, nonflat structural ring maps,
a non-quasi-compact disjoint union X with E supported on a proper finite part, and
non-quasi-separated base scheme S. The proof uses an empty U for empty support;
no nonemptiness or separatedness over S is encoded. The relative derived tensor resolves
both inputs, so possible unboundedness below of E tensor Lf*F is retained.

Searches performed through msearch.py, with exact receipts in searches.jsonl:

- LeanFinder: "Derived projection formula for bounded coherent complexes with proper
  support on algebraic spaces"; hits were affine-limit results and generic derived
  category fraction/vanishing facts, no match.
- Loogle: `"projectionFormula"`; no hits.
- Mathlib grep: `properSupport|projectionFormula` in AlgebraicGeometry; no hits.
- LeanSearch: "relative derived tensor on module sheaves canonical derived projection
  formula"; projective-resolution, differential and elementary tensor hits, no match.
- LeanFinder: "Balanced relative derived tensor of module sheaves on algebraic spaces
  and its scalar restriction identification"; ordinary presheaf tensor and scheme
  pullback-carrier hits, no relative derived bifunctor.
- Mathlib grep: `relativeDerivedTensor|spaceRelativeTensor|spaceProjectionComparison`;
  no hits. The same rg search in both upstream WeilConjectures and Sheaf found no
  declaration. Broader tensor/projection/support searches did find the interfaces
  listed above, which are reused. The upstream ProperSupportDerivedProjectionFormula
  is a scheme theorem and does not state this algebraic-space result.
- DAG and blueprint_refs.py searches for relative tensor found condensed/pro-etale
  relative module tensors and specialized scheme tensors, not this structure-module
  algebraic-space relative tensor. The item's blueprint ancestor command returned
  `blueprint.from.node = None`; the new node retains that null ancestor and the full via.

Validation: scompile.py compiled each module separately in dependency order. The initial
full helper elaboration timed out; reduced module-mode probes isolated and verified its
prefixes, and the existing tensor-module opacity settings plus synchronous elaboration
made the complete file compile within 60 seconds. No compiler limit was raised. All
probe files are outside lean/ and are excluded from the delivery. Final dry-run results
are recorded below after preflight.

No statement correction, dependency-module repair, or disputed statement.

## New nodes

`def-sfb-space-relative-derived-projection` owns
`Sheaf.AlgebraicGeometry.SpaceRelativeDerivedProjection`. Source: sites-cohomology.tex,
Tag 08I6 and equation-projection-formula-map (0B56), used in the two displayed formulas
of spaces-perfect.tex Tag 08IS. It defines the ordinary relative balanced total tensor
as P tensor f*Q, the product-localization total left derived functor and its counit,
the uniquely representative-normalized scalar-restriction identification, the actual
adjunction-mate projection, its relative composite, and the bifunctoriality equation.
The ordinary balancing formulas are mutually inverse and retain the first-factor action;
thus this is a presentation of the relative tensor, not a definition of a different
object as the desired result. The derived comparison is chosen from an existence-and-
uniqueness theorem with the full representative equation; no bare Nonempty choice or
arbitrary comparison is assumed. Searches above find no node or declaration owning this
notion. Existing tensor, pullback, direct-image and adjunction definitions are reused.
The item directly cites this node and the landed nodes owning the geometric predicates.

## Second reading by Q54

Single-worker rereading of the completed source against the original node; the delivery
still receives the maintainer's independent review. No additional agent was started.

I reopened both node statements and both complete modules. The main result includes
all three Noetherian components, the chartwise local-finite-type condition and relative
diagonal quasi-compactness, all-degree coherence, an ordered finite cohomology interval,
and reduced closed proper support separately in each degree. The coefficient quantifier
is the full QCoh category and its embedding in degree zero. The result is invertibility
of the canonical map, and naturality has an explicit morphism equation. There is no
flatness/Tor/compactness hypothesis or bound on the tensor. The helper's ordinary
balanced presentation and product-localization universal property make its codomain the
relative derived tensor with action through E. Its normalization equation uses the
shared counit and the existing representative tensor isomorphism, fixing the comparison
rather than assuming a chosen isomorphism. The source's proof steps, especially the unit
normalization and projection composition calculation, are present in the theorem docstring.
No mathematical mismatch was found. The rereading added direct public imports for every
recorded statement dependency rather than relying solely on transitive import visibility.

Final validation: `deliver2.py Q54 lem-sfb-space-proper-support-derived-projection-formula
--no-push` returned `OK (dry run)`: preflight passed and both final modules compiled
cleanly. The packet contains only the two Lean modules, the unchanged-statement item
with its Lean record and added declaration dependencies, this new definition node, and
this report. No live source was edited and no global build was run.
