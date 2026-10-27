## Worker report

Module: `Sheaf.AlgebraicGeometry.GraphDerivedMateFactorization`.
Main declaration: `AlgebraicGeometry.ProEtale.graph_derived_mate_factorization`.
Only its proof is postponed (`sorry`). All helper definitions have actual data and
are recorded in `lean.declarations`; each is an expression belonging to this node.
No node statement, dependency statement, or mathematical assumption was changed.

The final theorem has two clauses: the general representative compatibility, and
its compactified graph specialization. The categorical helper definitions keep the
large geometric functors out of repeated elaboration. Their parameters are filled
by the canonical dependency declarations in the final theorem, so users do not
supply arbitrary comparisons or extra normalization assumptions.

Hypotheses and objects, clause by clause:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`. Every scheme is `Scheme.{u}`. This is the existing fixed-coefficient
  universe convention; no equality of the object and morphism universes of a site
  is imposed. The small etale and pro-etale coefficient categories are respectively
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)` and
  `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u+1} A)`.
- The first clause binds `p : Z ⟶ T`, `[QuasiCompact p] [QuasiSeparated p]`.
  Its six functor arguments are exactly `Etale.upperStar`, `Etale.lowerStar`,
  `ProEtale.upperStar`, `ProEtale.lowerStar`, and `comparisonUpperStar` at Z and T.
  These are the constant-module presentations of the ringed-site inverse images,
  with their existing adjunctions, rather than copies of sheaf/module categories.
- The localization and derived operations are `DerivedCategory.Plus.Qh`,
  `mapDerivedCategoryPlus`, and `rightDerivedFunctorPlus`. They are ordinary
  derived categories restricted to the strictly full bounded-below subcategories,
  not constructible or completed categories. A bounded-below complex is sent
  through `HomotopyCategory.Plus.quotient` to the `P : HomotopyCategory.Plus` used
  in the predicate. Equality of the natural transformations there implies equality
  naturally for all bounded-below complexes and maps. Conversely the quotient
  identifies no additional obstruction to these already functorial equalities.
- The pullback comparison `a` is the existing `fixedComparisonPullbackPlus A p`.
  The ordinary mate `d` is exactly `graphComparisonDirectImageMate A p`, whose data
  is the `mateEquiv` of the inverse canonical pullback comparison, as in the graph
  sheaf-square dependency. The derived mate `b` is the existing
  `fixedComparisonDirectImageMatePlus A p` (not a choice of an isomorphism).
- `gamma` is `rightDerivedFunctorPlusUnit` on the homotopy representative.
  `mapDerivedCategoryPlusFactorsh` identifies termwise exact functors and their
  localizations. `graphMateHomotopyComparison` includes the two ordinary composite
  identifications `mapHomotopyCategoryPlusCompIso` around the termwise map `d`.
- The principal equation is the first conjunct of
  `GraphMateRepresentativeCompatibility`: `graphMateLeft = graphMateRight`.
  `graphMateLeft` is `W(gamma_et) ≫ b`, and `graphMateRight` is
  `Q(d) ≫ gamma_proet`, with all exact-functor identifications inserted.
  Both are natural transformations with the required representative-level source;
  no descent of underived `p_*` is claimed.
- The transpose is the inverse of the existing derived adjunction's `homEquiv`.
  For every representative P, the next conjuncts identify the left transpose with
  `graphMateEtaleCounitExpression`, the right transpose with
  `graphMateProEtaleCounitExpression`, and these two expressions with each other.
  The etale expression is `a.inv ≫ V.map(Q(epsilon_et^0))` with the l-localization
  comparison. The pro-etale expression applies L to the localized `d`, follows
  by the localized ordinary pro-etale counit, and uses the V-localization inverse
  to reach `V(QP)`. Functoriality moves L inside Q to give exactly
  `Q(L(d) ≫ epsilon_proet^0)`, the expression printed in the node.
- The second theorem clause binds separated etale finite-type e with
  `[Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]` and the
  existing `c : Compactification e`. Its `c.i`, `c.g`, and `c.comm` are the given
  open j, proper p, and factorization; quasi-compactness of j is equivalent to
  quasi-compactness of e by `Compactification.quasiCompact_openImmersion_iff`.
  Thus the compactification hypotheses neither require a qcqs base scheme nor
  silently omit the stipulated quasi-compact open.
- `GraphMateGeometricGraphCompatibility` supplies the graph functors and maps to
  `GraphMateGraphCompatibility`: `Etale.etaleCompactificationGraphMap`,
  `compactifiedProEtaleGraphMap`, `etaleSumComparisonIso`,
  `openImmersionLowerShriekComparisonUpperStarIso`, and the same named ordinary
  and derived mates for `c.g`. The pro-etale graph map is the graph-square node's
  unique specified map; no free graph witness is supplied.
- `graphMateRepresentativeGraph` is `gamma QG`, using exact source and j_!
  factors. `graphMateDerivedGraph` is its actual descent via
  `Localization.fullyFaithfulWhiskeringLeft ... .preimage`. This construction is
  defined on all D+ objects by the localization universal property; it is not a
  choice from a bare existence statement.
- In `GraphMateGraphCompatibility`, sigmaD and oD are universally quantified
  aliases constrained by equality to `mapDerivedCategoryPlusNatIso` conjugated
  by the exact composite isomorphisms. Similarly left, right, and middle are
  universally quantified aliases constrained by equality to explicit expressions.
  Each required value is provided by its displayed right-hand side, so these
  implications introduce no extra assumption and are nonvacuous. No `let` or
  `show ... from` occurs in the theorem signature.
- The left expression is `sigmaD.hom ≫ nu_U*(Theta_proet)`.
  The middle expression is `nu_T*Q(G_et) ≫ Q(d) ≫ gamma_proet ≫ Rp_*(oD)`.
  The right expression is `nu_T*(Theta_et) ≫ b ≫ Rp_*(oD)`.
  The final three conjuncts are left whiskered by Qh = middle, middle = right
  whiskered by Qh, and left = right on D+. This renders both equalities of the
  representative graph chain and its equality of natural transformations on D+.
- No instance or binder assumes preservation of injectives by comparison, and no
  inverse of a right-derived unit/gamma occurs. `EnoughInjectives` in the generic
  expression helpers is provided by the existing Grothendieck sheaf categories.
  Exactness/additivity of the sum extension is taken from the graph-square node
  and its actual restriction adjunction, inside a data-filled helper definition.

Dependency declarations read and reused:

- Mathlib: `AlgebraicGeometry.Scheme` / `.Hom`, `IsProper`, `IsOpenImmersion`,
  `Etale`, `LocallyOfFiniteType`, `QuasiCompact`, `Scheme.ProEt`,
  `CategoryTheory.constantSheaf`, `CochainComplex`, and `CategoryTheory.mateEquiv`,
  in the recorded modules. `ringedSiteModules` is the transparent general-site
  abbreviation from `Sheaf.CategoryTheory.RingedSiteModules`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the `DerivedCategory`/`Plus` construction.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`/`Plus`. The node
  explicitly uses constant-A module sheaves, so the fixed coefficient sheaf
  presentation already used by both map dependencies is retained throughout.
- `Sheaf.Paper.ComparisonPullbackExact`: `comparisonPullbackExact` (exactness of
  comparison); `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`. Its support comparison is the existing
  canonical comparison, as explained in the dependency's record and source.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `fixedComparisonDirectImageMatePlus_counit`.
- `Sheaf.AlgebraicGeometry.EtaleProEtaleGraphSheafSquare`: `etaleSumExtension`,
  `etaleSumAdjunction`, `etaleSumComparisonIso`, `graphComparisonDirectImageMate`,
  `compactifiedProEtaleGraphMap`, and `etale_proEtale_graph_sheaf_square`.
  The imported canonical open comparison and etale graph construction are reused.
- Proof imports: `CategoryTheory.preDerivedAdjunctionGeneral` from
  `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`,
  `CategoryTheory.Functor.exactFunctor_derivedFunctor` from
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
  `CategoryTheory.sitePullback_abelian_exact` from
  `Sheaf.CategoryTheory.SitePullbackAbelianExact`, and the recorded constant-ring
  operations module. The other stated proof dependencies are reached through the
  public geometric imports (ordinary inverse/direct images, termwise adjunctions,
  comparison exactness, exact localization factors and extension by zero).
  The Mathlib localization-universal-property dependency is used directly in the
  data-filled graph descent. There are no deliberately omitted cycle imports.

Edge cases checked: zero coefficient ring and zero/acyclic complexes are allowed;
empty schemes and empty U are allowed; no lower bound is fixed to degree zero;
identity p and identity/open-only compactifications are included. Noninjective
complexes remain in the representative quantifier. No `IsIso gamma` assumption is
introduced. The graph statement concerns the specified graph map, not an arbitrary
map with matching endpoints. Ordinary sheaf-category universes are those of the
canonical dependency API (scheme universe u, coefficient universe u+1).

Searches before writing (raw service replies are in `searches.jsonl`):

1. `msearch.py ... leanfinder "Derived direct image comparison counit mate commutes
   with localization of the underived direct image comparison on bounded below
   complexes"`: eight general results, including `Adjunction.derivedε_fac_app`
   and `LocalizerMorphism.rightDerivedFunctorComparison_fac_app`; none includes
   the specified geometric mate and compactified graph identity.
2. `msearch.py ... loogle "CategoryTheory.Adjunction.derivedε_fac_app,
   CategoryTheory.mateEquiv"`: zero results.
3. `msearch.py ... grep "rightDerivedFunctorPlus.*(Unit|NatTrans|BaseChange)|
   mapDerivedCategoryPlusFactors" CategoryTheory`: zero hits from that service.
   Direct `rg` in Mathlib and both project roots found the generic APIs in
   `ExactFunctor`, `RightDerivedFunctor/PlusComp`, `Adjunction`, and the recorded
   canonical-mate/graph-square modules. Those APIs were read and reused.
4. `msearch.py ... leansearch "The derived counit mate of an etale proetale
   pullback comparison agrees with the underived mate after the canonical right
   derived functor comparison"`: eight generic results including derived counit,
   `mateEquiv`, and right-derived comparison; no exact match for this node.
5. Direct `rg` and item-id searches in `lean/WeilConjectures` and `lean/Sheaf`
   found no existing declaration for this item. The general
   `CategoryTheory.derivedMate_comparison` concerns a different mate orientation
   with invertible representative right factors; its signature is not this node's.

No STATEMENT-DISPUTED flag, dependency-module repair, statement correction, or new
DAG node is needed. The only added notions are names for this very node's displayed
composites and predicate, with all canonical data supplied by existing declarations.

## Second reading by Q106

A separate self-review pass compared the final theorem, every helper body, and the
node. No second agent was started (the dispatcher explicitly prohibits that); the
maintainer's independent review remains the independent reading of this delivery.
The pass checked composition direction, exact localization factors, both ordinary
counit expressions, and both graph equalities, including descent. An intermediate
attempt to use abstract map assumptions was discarded: the final theorem binds
only the original geometric hypotheses and instantiates all canonical maps itself.
An intermediate full geometric expansion was replaced by reusable categorical
expressions to avoid expensive unfolding. This changed only the expression of the
same maps. Universal aliases in the graph predicate are fixed by equalities to
actual terms, and can always be instantiated, so no clause is assumed or vacuous.
All universe and category variables are explicit and autoImplicit is disabled.

Validation: the prescribed server compiler accepted the module both under the
sandbox name and its actual library name, with no errors or non-sorry warnings.
The actual library compile reported 24.6 seconds. A separate consumer probe,
compiled through scompile.py together with the module, checked the full geometric
theorem signature and `#print axioms`; it reported `sorryAx` (expected in stage 2)
and only `propext`, `Classical.choice`, `Quot.sound` otherwise. Its actual library
compile reported 23.6 seconds. The first delivery dry run passed preflight and
compilation at 53ae1a604c9. The final audit then explicitly named the derived-category
universe levels in all categorical helper binders; the final compiler and dry run
are rerun for that textual adjustment. Diagnostic probes are only in scratchpad
and are not included in the delivery.
Final universe-explicit module: clean server library compile, 31.8 seconds; exactly
one postponed named theorem. The theorem signature remains verbatim in lean.statement.
