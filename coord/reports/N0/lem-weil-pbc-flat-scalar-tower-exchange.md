## Worker report

The module `Sheaf.CategoryTheory.FlatScalarTowerExchange` states
`CategoryTheory.FlatScalarTowerExchange.flatScalarTowerExchange` with one `sorry`.
All auxiliary records and constructions are helpers spelling out this node's given
data, and are listed in `lean.declarations`. There are no new independent notions,
new DAG nodes, or dependency repairs. The original node statement is unchanged.

Hypothesis and clause correspondence:

- Four small ringed sites: `X Y X' Y' : Corner`, with `site`, `category`, `topology`.
  `Corner.R`, `.S`, `.a` are commutative ring sheaves and their map; `.flat` is the
  dependency's `IsFlatOnSite` of S restricted along a. This retains the zero ring.
- Each edge is `EdgeData U V`. Its R and S fields use the recorded
  `FlatRingedModuleImage`, hence `RingedToposMorphism`, its geometric adjunction,
  invertible structural ring map, algebraic module inverse image and its specified
  module adjunction. `sameInverse`, `sameDirect`, `sameAdjunction`, `coherent`
  say both coefficient systems use the same geometric morphism and commute with a.
  `EdgeData.input` is the original `FlatRingedDiagramInput` assembled from shared
  corner data, not a new definition of a geometric or ringed morphism.
- The specified commutative geometric square and the two coherent coefficient
  identifications are `Square.R.geometry`, `.S.geometry`, `.sameGeometry`, and
  both `ModuleSquare.coefficient` equations. No cartesian-square hypothesis occurs.
- J is exactly positive integers opposite, up to the standard universe lift:
  `Index := ULiftHom (ULift ℕ+ᵒᵖ)`. Both object and hom universes are lifted to u;
  the category is equivalent to the original ordered index category. The chosen
  derived Hom universe w is explicit and independent of u.
- `Corner.modulesR` and `.modulesS` are actual full functor categories of strict
  diagrams of the dependency's `ringedSiteModules`, with their inherited abelian
  structures. `Corner.derivedR` and `.derivedS` name the chosen localization
  instances without altering the abelian structure. `DerivedCategory` is Mathlib's unbounded localization. No tuple of
  separate derived evaluation objects replaces a derived strict tower.
- `Corner.Restriction.functor` has the exact localization factor `.factor` for
  the actual termwise `SheafOfModules.restrictScalars`. `DerivedImage` packages
  specified L, F, localization comparison q, universal right-derived unit eta,
  computation on K-injectives, and the representative adjunction transpose
  formula. This is the prescribed derived termwise adjunction, not an arbitrary
  adjunction on the derived categories.
- `DerivedEdge.p` and `.d` are required by `EdgeNormalized` to equal the b
  and d of the dependency's `DerivedRestrictionComparison`. The witness includes
  ordinary underlying-sheaf equations, inverse-localization normalization,
  right-derived-unit normalization and the adjunct equation. Its corner functors
  and factors equal the shared ones. Thus an arbitrary pair of natural
  isomorphisms cannot instantiate the theorem. The `DerivedImage` records for
  the eight operations are separate explicit parameters, shared by every use.
- `ModuleSquare.modules` is fixed by its `.normalized` equation after applying
  the faithful underlying-set-sheaf functor. Thus it is the comparison induced
  by the given geometric square, including its module actions. `.diagrams`
  applies that same natural isomorphism termwise. `θR`, `θS` are
  fixed by `hθ : SquareNormalized s θR θS`, whose two equations on complexes
  and localization are expressed through `LocalizationSquareNormalized`. These equations specify the canonical maps mentioned in the
  node; the theorem does not assume their compatibility with scalar restriction.
- The first conjunct is equation (C) for every `M : DerivedCategory Y.modulesS`.
  All arrows are module morphisms; it therefore includes the coefficient actions.
- `sourceComparison df dg` is exactly b: p_g followed by L_g(d_f).
  `targetComparison dfp dgp` is exactly d: d_f' followed by F_f'(p_g').
  They are natural isomorphisms constructed by whiskering and composition, with
  the source and target types displayed in their definitions.
- `mateEquiv fS.adj fpS.adj` and its R counterpart define exactly E_S and E_R
  from the specified pullback squares. The second conjunct is equality of
  natural transformations `rY'(E_S);d = b;E_R(rX -)`. Its component is the
  node's displayed d_Z rY'(E_Z^S) = E^R_(rX Z) b_Z.
- The third conjunct is the inverse Hom equivalence under the R adjunction on
  f', applied to b inverse; rY'(E_S); d. Its value is thetaR at F_f(rX Z)
  followed by L_g'(epsilon_f at rX Z), exactly the explicit transpose formula.
  Quantification over all Z and the natural-transformation equality retain full
  naturality in actual derived strict towers, with no completeness, reduction,
  cartesianness, or boundedness condition.

Dependency declarations read and reused:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  `SheafOfModules.restrictScalars`, changing only the scalar action.
- Mathlib.Algebra.Homology.DerivedCategory.Basic:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- Mathlib.CategoryTheory.Adjunction.Mates: `mateEquiv` and its transpose formulas;
  this is the `mathlib_match` of def-weil-pbc-adjunction-mate.
- Sheaf.CategoryTheory.RingedToposMorphism: `RingedToposMorphism`.
- Sheaf.CategoryTheory.FlatRingedDiagramRestriction (and its public interface
  modules): `FlatRingedModuleImage`, `FlatRingedDiagramInput`,
  `FlatRingedDiagramInput.DerivedRestrictionComparison`,
  `FlatRingedDiagramInput.flatRingedDiagramRestriction`. The comparison type
  carries the normalized input referred to in the node.
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral:
  `preDerivedAdjunctionGeneral`, read with its representative Hom normalization
  and naturality clauses; imported as part of the stage-3 proof plan.
- Sheaf.CategoryTheory.DiagramSiteRealization:
  `exists_diagramSite_realization`, read including the module-equivalence and
  transition-map normalization; imported for the product-site realization step.
- Mathlib.CategoryTheory.Localization.Predicate: `Localization.liftNatTrans`,
  `liftNatIso`, `natTrans_ext`, supporting descent and detection of the first
  square equality in the node's proof.

Source read: the current blueprint's completed-exchange-coherence proof (second
paragraph), the full item's seven-step coefficient supplement, and Stacks
sites-cohomology.tex, Tag 07A7 `remark-base-change` (lines 4033 onwards).
The source defines the mate by theta followed by the pulled-back counit; the
Lean expression uses exactly that orientation. The module docstring records
all seven proof steps, grouped only where the same construction is described.

Searches actually run (msearch.py, N0 / this item):

- leanfinder: "Flat scalar restriction transports the adjunction exchange mate
  for a commutative square of ringed topoi on derived strict towers". Eight
  ordinary sheaf pullback/adjunction hits, no normalized derived tower theorem.
- loogle: "CategoryTheory.mateEquiv, CategoryTheory.Adjunction". Twelve generic
  mate calculus declarations, including mateEquiv_counit and mateEquiv_hcomp;
  none states coefficient compatibility of this geometric strict-tower square.
- grep: "restrictScalars.*(exchange|mate)|flatScalarTowerExchange|scalar.*[Mm]ate".
  Zero hits in Mathlib.
- leansearch: "Flat restriction of scalars commutes with adjunction exchange
  mates on derived sheaves of module diagrams". Eight scalar-restriction and
  ordinary module-adjunction hits; no statement of this node.
- Direct rg over lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for flatScalarTowerExchange, FlatScalarTowerExchange, the node id and related
  flat/scalar exchange patterns. No exact declaration. FlatScalarTowerCoherence
  concerns associative extension of coefficients, a different statement; its
  signature was read. The existing flat restriction interface was reused.

Edge cases checked mathematically: identity geometric square and identity
coefficient map give the identity mate normalization, rather than a free scalar
multiple of the adjunction; the zero tower and zero ring are admitted; arbitrary
noncartesian towers and unbounded complexes are included; the level 1 is retained
by the positive indexing category; empty presented sites are admitted. Restriction
flatness is the actual cornerwise hypothesis, with no exact-products assumption.
No statement dispute or source correction was needed.

## Second reading by N0

A second in-thread pass compared the original node and the complete module;
no separate agent was started, as required by the dispatcher. The maintainer
provides the independent review. The checks specifically tracked the two
orientations of p and d, the order of b and d, the inverse Hom equivalence in the
transpose clause, and the ordinary and complex normalization of the square.
The draft's repeated concrete derived-adjunction record was replaced by a
parametric record to avoid repeated category-instance expansion; this changes
no hypotheses. Every helper is listed in lean.declarations and has a source and
blueprint docstring. All theorem proof work is postponed to the single matching
DAG theorem.

Validation: the complete module passed the prescribed scompile.py sandbox and
library compilations (37.4 s and 38.4 s), with no errors or unexpected warnings.
The generic localization-square formula avoids expensive repeated unfolding of
concrete sheaf categories; it is the same representative equation. No compile
limit was changed. The dry-run and delivery results are recorded by deliver2.py.
