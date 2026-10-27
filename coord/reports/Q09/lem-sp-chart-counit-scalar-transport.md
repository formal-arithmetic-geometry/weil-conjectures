## Worker report

The module `Sheaf.Paper.ChartCounitScalarTransport` states the two equations in
`lem-sp-chart-counit-scalar-transport`. The etale equation is
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport_etale`;
the pro-etale equation on every input is
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport`.
Both proofs are `sorry`. All five helper definitions contain actual compositions
of existing maps. No new DAG nodes or dependency replacement modules are needed.

Source read: main-20261015 blueprint,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
the entire Charts paragraph, together with the node's four retained proof steps.
The proof docstrings retain raw sum/ordered-affine pasting, cancellation of the
graph-normalized left comparison, conjugacy of the two maps separately under
site comparison, essential surjectivity for arbitrary pro-etale inputs, and
canonical refinement/inverse/composite compatibility.

Hypotheses and clauses, matched individually:

* The prime ell is `(ell : ℕ) [Fact ell.Prime]`. Positive characteristic and its
  distinction from ell are `(pchar : ℕ) (_hp : 0 < pchar)` and
  `(_hne : ell ≠ pchar)`, with `(k : Type u) [Field k] [CharP k pchar]`.
* All schemes have `Over (Spec (.of k))`; their structure morphisms are locally
  of finite type, quasi-compact, and separated. These are precisely separated
  finite-type k-schemes. The equation `_he` says the chart composite is over k.
  The ordered affine tower has its canonical k-structure, as in the chart
  dependency, so this also says e is over k. No extra assumption is imposed on
  the compactification middle schemes; their induced structures are provided by
  the recorded compactification interfaces.
* Finite unital commutative coefficient rings are `{A B : Type u}` with
  `CommRing` and `Finite`, and `(φ : A →+* B)`. Fixed-module sheaves use the
  canonical `ULift.{u+1,u}` ring presentation required by the recorded
  `proEtaleCoefficientMap`. This is the existing coefficient transport's size
  convention, not a restriction on the finite rings: the canonical ULift ring
  equivalence transports every finite ring and its homomorphism. The site remains
  the original small etale/pro-etale site, with object universe u+1 and Hom u.
* The common annihilator is `N`, the two equations `hA`, `hB`, and
  `(n : ℕ) (_hN : N = ell ^ n)`. `CA.positive` retains N>=1, including n=0.
  `hY : IsUnit (N : Γ(Y, ⊤))` and the Noetherian instances are precisely the
  derived consequences already supplied by `chartFiniteRingAdjunction`, used
  to type its existing `Datum`. They are not new geometric restrictions.
* `etaleProperty` is the recorded bounded finite-value constructible predicate
  intersected with the full finite Tor test. `proEtaleProperty` uses the
  recorded category from adjunction transfer; `CA.intrinsic` and `CB.intrinsic`
  identify it on all Noetherian schemes with intrinsic fixed-module
  constructibility and the universal test against every degree-zero sheaf.
  No etale-origin assumption on an input is added: K is quantified over the
  entire pro-etale full subcategory in the second theorem.
* The chart is `(d : ℕ) (e : U ⟶ affineTraceTower Y d)` with `Etale e`,
  `IsSeparated e`, `LocallyOfFiniteType e`, `QuasiCompact e`. This is the
  dependency's ordered affine-space model, including its identity stage d=0.
  `cp` and `cg` are arbitrary specified compactifications of the affine
  projection and chart composite, respectively.
* `MA`, `MB`, `tA`, `tB`, `PA`, `PB`, `CA`, and `CB` are the EXISTING fully
  normalized chart data of `lem-sp-chart-finite-ring-adjunction`, not arbitrary
  right adjoints or an assumed scalar counit equation. In particular,
  `CA.etaleCounit` and `CB.etaleCounit` literally prescribe sum evaluation then
  the ordered affine counit, with the inverse graph-normalized left comparison;
  `fixedComparison`, `proCounit` and `geometric_normalization` prescribe every
  site and geometric endpoint. Their existence is the dependency theorem.
* T on etale modules is `Etale.scalarExtension (uliftRingHom φ) T`; T on
  pro-etale modules is the existing `liftedScalarExtension φ T`. Both are the
  actual derived extension, with target-ring action, not an arbitrary functor.
* The Tate line uses the dependency's `ordinaryFiniteLine`, namely the
  existing finite etale root line in degree zero. The conclusion existentially
  supplies `L`, a family of the existing `CoefficientLineComparison` records
  with N=M. Its `roots_power` fixes the root map to the identity when N>0;
  `generators` fixes the map on every scalar/root generator; and
  `derived_normalization` fixes the derived comparison by the genuine
  scalar/single counit followed by the ordinary balanced map. Thus the line
  map is exactly `(z tensor a) tensor b ↦ z tensor φ(a)b`, in the library's
  symmetric tensor convention. L is concluded, not assumed, and is not a
  bare Nonempty isomorphism choice.
* `coordinateLineScalarIso` assembles the actual scalar tensorator, canonical
  scalar/pullback map, scalar/shift map, and this normalized line comparison.
  `coordinateAffineScalarIso` iterates in the specified order, starting at
  the literal identity for d=0. `coordinateChartScalarIso` first commutes
  scalars through e*, then pulls back the ordered affine comparison. These
  definitions specialize/generalize the existing coordinate formulas without
  importing the downstream exceptional theorem or assuming its comparison
  invertible. They introduce no alternative Tate line or tensor product.
* The etale beta in the first equation is precisely `etaleCoefficientMap`
  at `cg` and `H_A K`. Its next map is compact support over B applied to
  `coordinateChartScalarIso.hom`. Its last map is the actual
  `CB.adjEt.counit`, evaluated on the actual scalar-extended K. The right
  side is scalar extension of `CA.adjEt.counit`. These are exactly the three
  factors and the right side of the first displayed equation, in Lean's
  left-to-right composition notation. The existential `hScalar` only proves
  membership of the actual scalar-extended object in the existing full category.
* `geometricCounit` is compact support of `CA.geometric.inv`, followed by
  `CA.adjPro.counit`; it is the actual transported counit on the explicit
  geometric right functor, not a chosen isomorphic map.
* `geometricScalarIso` conjugates the canonical etale scalar comparison using
  `CA.geometric`, `CA.heU`, the genuine `pbcComparisonReduction` on U,
  `CB`'s `chartGeometryComponent`, inverse scalar/site comparison on Y,
  and the ACTUAL `CA.eY.counitIso`. It is defined on all K by `CA.eY.inverse`.
  Thus it retains the endpoint identifications rather than assuming K is
  literally a comparison object. `CA.geometric_normalization` ensures this
  is the canonical tensor/pullback, shift and Tate comparison in geometric
  coordinates, with no sign or orientation freedom.
* The pro-etale b is precisely `(proEtaleCoefficientMap φ cg).app` on the
  geometric H_A K. Next is compact support over B of `geometricScalarIso.hom`,
  then `geometricCounit` for CB at T_Y K. The right side is T_Y applied to
  `geometricCounit` for CA at K. This is exactly the second displayed equation.
* Both theorems quantify over arbitrary cp, cg and their fully normalized data.
  Consequently the equations hold again for every canonical refinement or
  common refinement, with the prescribed comparisons and counits. The
  docstrings specify the coefficient square and left-comparison pair argument
  giving that invariance. No flatness or finite projective dimension of B/A,
  invertibility of an exceptional coefficient map, or smooth orientation appears.

Dependency declarations used (full namespaces as in their modules):

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  Over/finite-type setting (read the source signature and setting docstring).
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`, its
  bounded subcategories, `homologyFunctor`, and `torsionCohomology`.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
* `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
* `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty`,
  `proEtaleProperty`, `etaleLowerShriek`, `proEtaleLowerShriek`, `comparison`.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  the recorded intrinsic `scalarExtensionFunctor`; its fixed-module transport
  is the imported coefficient compatibility's `liftedScalarExtension`.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` and its public
  `DerivedChangeOfRingsCochainModel`: the genuine K-flat change-of-rings interface;
  the specialization used is `AlgebraicGeometry.Etale.scalarExtension`.
* `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateLine` and `finiteEtaleTateTwist`.
* `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction`:
  `AlgebraicGeometry.ProEtale.ChartFiniteRing.Datum`, `etaleRight`,
  `geometricRight`, `chartGeometryComponent`, `chartFiniteRingAdjunction`.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  used through its normalized fixed-module tensor/pullback specializations.
* `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleCoefficientMap`,
  `proEtaleCoefficientMap`, `uliftRingHom`, `liftedScalarExtension`, and its
  specified scalar/site comparison `pbcComparisonReduction`.
* `Sheaf.Paper.FiniteSmoothCoefficientArrows`:
  `AlgebraicGeometry.Etale.FiniteSmoothPurity.CoefficientLineComparison` and
  `scalarShiftIso`. Its already recorded definition node is added to stmt_deps.
* `Sheaf.Paper.PurEtaleScalarMateProjection`:
  `AlgebraicGeometry.Etale.scalarPullbackIso`. Its already recorded definition
  node is also added to stmt_deps.
* The proof import `Sheaf.Paper.EtaleCtfChartDomain` supplies the recorded chart
  preservation and site/scalar comparison interfaces.

The raw-pasting, left-comparison-pair and site-conjugacy proof nodes currently
have no Lean record. Their mathematical roles remain in the proof docstrings.
The recorded `Sheaf.Paper.ChartLeftScalarNormalization` source is absent both
locally and in the live server (`scompile.py --source` returned
`Module source unavailable`); its proof-only import is therefore not available.
The item has no dependency wait. Its statement uses the already published
chart-normalization data, and the theorem is delivered with the required sorry.

Edge cases checked before writing: d=0 uses identity in the existing tower and
in `coordinateAffineScalarIso`; the empty scheme imposes no nonemptiness;
zero objects are included in both full categories; the zero coefficient ring
and n=0 (N=1) remain allowed. The only root identity simplification needed is
N/N=1 for N>0, already retained by Datum.positive. A nonflat map such as
Z/ell² -> Z/ell is not excluded. No bound uniform over all input complexes or
over the chosen root comparison family is imposed. All Tor tests remain against
all module sheaves, including arbitrary pro-etale module sheaves.

Searches actually run (the wrapper records their exact outputs in searches.jsonl):

* msearch leanfinder, "Scalar extension commutes with the counit of an etale
  affine space composite chart after etale proetale transport": eight results
  about etale algebra and affine-space maps; no matching chart-counit theorem.
* msearch loogle, "CategoryTheory.Adjunction.counit, CategoryTheory.NatTrans":
  only `TopCat.adj₁_counit`; not a match.
* msearch grep, `chart.*[Cc]ounit|[Cc]ounit.*[Ss]calar`: nine results about
  affine group rings, bialgebras and ordinary change of rings; not a match.
* msearch leansearch, "Canonical scalar extension isomorphism for inverse image
  Tate twist shift on an etale affine chart": eight results about elementary
  module scalar extension and intermediate fields; not a match.
* msearch loogle, `reductionEtaleChartScalarIso`: unknown identifier, zero hits.
* msearch grep, `reductionEtaleChartScalarIso|reductionEtaleAffineScalarIso`:
  no Mathlib hits.
* rg of `lean/WeilConjectures` and `lean/Sheaf` for chart/scalar/counit patterns
  and the item id: no theorem states these two counit equations. The item id has
  no upstream declaration. The upstream concrete formula in the downstream
  `ReductionExceptional` module was read, including its Tate generator map,
  but that module is not imported: doing so would obstruct later proof imports.
  Instead the already recorded fully normalized CoefficientLineComparison is
  used as a concluded witness, and the elementary coordinate assembly is given
  as helpers of this node. This keeps the dependency direction bottom-up.
* `tools/blueprint_refs.py search 'chart scalar'`: zero blueprint matches.
  DAG rg for `reductionEtaleChartScalarIso|Canonical chart reassociation` found
  only the downstream reduction-exceptional record. Existing finite-smooth
  coefficient-arrow and scalar/pullback definition nodes were used directly.

No STATEMENT-DISPUTED finding, source correction, or new definition node.
The item JSON changes only lean and adds the two existing definition dependencies.
Each source line is at most 100 characters; autoImplicit and relaxedAutoImplicit
are disabled. The final file compiles in both wrapper modes against the live
published library (8.5 seconds each), with no errors or warnings.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
