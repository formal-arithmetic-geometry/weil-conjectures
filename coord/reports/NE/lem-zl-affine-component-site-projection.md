## Worker report

The module `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection` states the affine
component-site projection. `componentProfinite T` is the actual quotient
`ConnectedComponents T`, with compact, Hausdorff and totally disconnected instances supplied
by `spectralSpace_connectedComponents_profinite`. `componentObject T W` is the canonical
continuous map of component quotients for a qcqs pro-etale object `W`; `componentObjectMap`
is its map on morphisms. `HasSplitFiniteQcqsCovers` renders the corrected split-cover
condition, including the empty finite family through `Fin 0`. `ComponentSiteEvaluation`
packages a geometric morphism, its direct-image comparison, the component factorization,
and the natural evaluation isomorphisms in a coefficient category. The theorem
`affine_component_site_projection` states all clauses of the node with proof `sorry`.

The Lean rendering of the statement is as follows. `[IsAffine T]` renders that `T` is
an affine scheme. `U : Over (componentProfinite T) ⥤ T.ProEt` is the functor
`E ↦ T_E`, and `r` is the continuous map on underlying spaces. For each `E`, the first
conjunct is affine, the second is ind-etale over `T` via the universe-transported
`RingHom.IndEtaleAcrossUniverses`, and the third says every structural stalk map is an
isomorphism. The displayed homeomorphism has source `(U.obj E).left` and target the
fibre product `{p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2}`; its two
projection equations render the underlying locally ringed-space assertion. The second
homeomorphism identifies the component space with `E.left` and its pointwise equation
fixes the canonical map `r E`. The next clause gives naturality of `r` for every map
`E ⟶ E'`. `PreservesFiniteLimits U` renders finite-limit preservation. The `Fin n`
covering clause renders finite jointly-surjective covering families and includes the
empty-index edge case. Finally `hU` says that `U` is continuous from the coherent
profinite site over `componentProfinite T` to the small pro-etale site of `T`; the three
`ComponentSiteEvaluation` conjuncts use `Type (u+1)`, `AddCommGrpCat.{u+1}`, and
`CommRingCat.{u+1}`, respectively. In each, the evaluation isomorphism is required only
for `W` with `HasSplitFiniteQcqsCovers W`, and the normalization equation is imposed on
every map `W.obj ⟶ U.obj E`; the naturality equation is imposed for sheaf morphisms and
maps of eligible qcqs objects.

Dependency declarations used are: `Mathlib.AlgebraicGeometry.Scheme.AlgebraicGeometry.Scheme`
(and `AlgebraicGeometry.Scheme.Hom`) for schemes; `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite.spectralSpace_connectedComponents_profinite`;
`Mathlib.AlgebraicGeometry.Sites.Proetale.AlgebraicGeometry.Scheme.ProEt`;
`Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite` declarations `qcqsObjects`, `Qcqs`,
`qcqsInclusion`, and `qcqsPrecoverage`; `Sheaf.RingTheory.IndEtaleUniverseTransport.RingHom.IndEtaleAcrossUniverses`;
`Sheaf.CategoryTheory.SiteCoveringAxioms.CategoryTheory.Precoverage.IsSiteForCoverings`;
and `Sheaf.CategoryTheory.Sites.GeometricMorphism.CategoryTheory.GeometricMorphism`
(with `comp`, `inverseMate`, and `inverseIso`). Proof-plan imports are also retained for
`siteInverseImage_tensor`, `indEtale_principalZariski_stability`, the locally constant
prime-spectrum homeomorphism, qcqs finite-family geometry, sheaf algebraic structures,
and sheafification local sections, together with the recorded Mathlib localization,
clopen, affine-morphism, flat-Kan, profinite-basis and stalk declarations.

Edge cases checked: `Fin 0` (the empty covering family), the empty scheme and empty
profinite object (the fibre set and structure map remain well-typed), `E = componentProfinite T`
(the identity component object), a one-point component space, and `W` empty. The split-cover
hypothesis is used only in the evaluation isomorphism; it is not imposed on all qcqs objects.
The target homeomorphism uses the equality fibre, so it does not silently replace the
component pullback by an arbitrary map. Universe parameters remain explicit and the
coefficient category is quantified independently of the scheme universe.

Searches made: `msearch.py ... leanfinder "affine scheme component quotient profinite spaces over pi0 geometric morphism inverse image sheaves"` (8 results, all generic affine-limit or profinite-limit declarations; no match); `msearch.py ... loogle "ConnectedComponents, Profinite, Sheaf"` (0 hits; unknown identifier `Sheaf`); `msearch.py ... grep "ConnectedComponents|componentSite" AlgebraicGeometry/Sites` (5 hits in `Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean`, only constant-sheaf connected-component maps); `rg` over `WeilConjectures` and `lean/Sheaf` for component-site/projection terms (no full declaration; only generic component and point-Lan modules); and `grep -rl` over `dag/nodes` (no node with this item’s statement). The existing point-Lan evaluation module is a related absolute-point specialization and does not define the affine component-site construction.

No statement correction was made. No `STATEMENT-DISPUTED` flag is needed: the split-cover qualification is part of the recorded node statement and follows the cited corrected source formulation.

## Second reading by NE

I reread the node and the module independently. The affine hypothesis is represented by
`[IsAffine T]`; no base field or extra separatedness hypothesis was added. The construction
uses the same `ConnectedComponents` quotient as the node, and the fibre homeomorphism states
both projections and the component identification. The finite-limit and covering clauses
are separate conjuncts, and covering families are finite `Fin n` families with no hidden
nonemptiness assumption. The evaluation formula is restricted exactly to qcqs `W` satisfying
the split-cover condition, while its naturality is stated only for maps between eligible
objects. The three coefficient categories and their operations are retained. Compilation
with `scompile.py` succeeds with no errors or warnings.
