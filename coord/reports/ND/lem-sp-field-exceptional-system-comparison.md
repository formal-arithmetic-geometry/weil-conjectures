## Worker report

The final module `Sheaf.Paper.FieldExceptionalSystemComparison` states
`AlgebraicGeometry.ProEtale.FieldExceptionalSystem.field_exceptional_system_comparison`.
It constructs the comparison component by the actual whole-system adjunction Hom
bijection. The theorem has exactly one postponed proof; every definition has real data.
No statement correction or dependency replacement is needed. The definition interfaces
are split into modules owned by new definition nodes, to keep each compile within 60 s.

Hypothesis and clause correspondence:

- The global finite field, algebraic closure, characteristic, prime ell different
  from the characteristic, and fixed coefficient closure are `P : PurityFiniteSetting`.
  Its `field` and `coefficients` are the existing global datum. No arbitrary field or
  prime has been substituted. `Index P` is the existing directed set of finite
  subfields in that closure; `E F` with `h : E ≤ F` express every field inclusion,
  including equality and ramification. The coefficient system maps are exactly
  `D.coefficients`, normalized by `quotient_mk` and `tower_app` in the dependency.
- `X Y : Scheme.{u}`, their `Over` instances, `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` structure maps render separated finite-type k-schemes.
  `f.IsOver` makes f a k-morphism; `d : ℕ`, `SmoothOfRelativeDimension d f`, and
  `IsSeparated f` render smooth separated pure relative dimension d >= 0.
  `c : Compactification f` fixes one compactification for all coefficient fields.
- `SpTowerShriek.R` is O_E/(ell)^(n+1), not O_E/(uniformizer)^(n+1).
  `SpTowerShriek.D`, `SpTowerShriek.Ev`, and `Models.coordinates` are the existing
  ordinary derived strict tower category and its section-preserving sequence-site
  presentation. Natural n means the positive paper exponent n+1.
- `N` is only an abbreviation for the dependency's `normalized` full subcategory,
  which is defined using `spNormalizedConstructibleTorTowers`. It retains uniform
  cohomological AND uniform Tor intervals, canonical derived reductions, and ALL
  ambient derived morphisms. No separate category of diagrams in derived objects
  is introduced. Twists are inherited unchanged through the dependency imports;
  this comparison has no new twist argument or twist conclusion.
- `scalar` is the full-subcategory restriction of `(D.scalars E F h T).T`, namely
  ordinary-derived extension along the actual whole-system coefficient map.
  `support` similarly restricts the actual `SpTowerShriek.F` proper/open composite.
  The preservation witnesses in `Domains` are conclusions, not extra assumptions.
- `Adjoints.right`, `Adjoints.adj` supply G_A, G_B and the tower adjunctions on N.
  The full-subcategory functors retain ambient morphisms. `FiniteAdjoint.realization`
  uses the existing `ReductionExceptionalRealization` with its actual ordinary-etale
  counit, so the finite right adjoints cannot carry independent orientation scalars.
  `Adjoints.evaluation`, `leftEvaluation`, `leftNormalized` and `Adjoints.counit`
  (the existing adjunction-mate evaluation predicate) fix tower/finite coordinates by the
  actual support evaluation and actual counits, as required by tower gluing (3).
- The comparison b is literally `FieldShriekSystem.iso`, whose hom is the actual
  proper adjunction mate followed by open extension tensor comparison. Its full
  `FieldShriekSystem.Laws` are part of the conclusion.
- `component` is `(A.adj F).homEquiv` applied to the full-subcategory lift of
  `b.inv.app (G_A K)` followed by C_Y of the A-counit. This is exactly the stated
  definition c_K; no arbitrary arrow, isomorphism, or lift from evaluations is chosen.
- `Laws.invertible` and `Laws.naturality` assert it is a natural isomorphism of whole
  systems. `iso` packages exactly these components with `NatIso.ofComponents`.
- `sourceEvaluation` and `targetEvaluation` are explicit composites of the existing
  scalar evaluation, right-adjoint evaluation, and functorial images. `Laws.evaluation`
  conjugates evaluated component by these maps and identifies it with `finiteComponent`,
  the finite adjunction transpose of the SAME reductionDirectImageComparison inverse
  and scalar-extended finite counit. This is the definition of the finite c in
  det-sp-reduction-exceptional, not a generic finite isomorphism.
- `Laws.rightReduction` is the specified quotient mate followed by G_m of the input
  reduction, with the precise finite evaluation coordinates. `Laws.transition` is
  the actual commutative reduction square for component between its two whole systems.
  `Laws.mixed` identifies BOTH finite paths E_n -> F_n -> F_m and
  E_n -> E_m -> F_m with the direct finite exceptional transpose for E_n -> F_m.
  `finiteComposite` includes the canonical `scalarExtensionFunctor_composition`
  at both source and target; `HEq` transports only the equal composite ring maps.
  The ring-square equality is inherited from `b.coefficientSquare`.
- `Laws.counit` is exactly P_B(c_K) followed by epsilon_B = b inverse followed
  by C_Y(epsilon_A). `Laws.unit` is C_X(eta_A) followed by c_(P_A M) and G_B(b_M)
  = eta_B. Both are equalities in full subcategories of the actual tower derived
  categories, not equalities inferred from evaluations.
- `Laws.composition` is D_X(c_EF) followed by c_FL and G_L of the canonical scalar
  associator at K = the source scalar associator followed by c_EL.
  The associators are `FieldShriekSystem.scalarAssoc`, fixed by actual restriction
  composition and the normalized scalar adjunctions, so these are balanced tensor
  associators. `Laws.identity` states exactly the identity after the corresponding
  normalized scalar unitors. Both are equalities of ordinary-derived system maps.
- No faithfulness of derived evaluation is present anywhere. Isomorphism detection
  is used only in the proof docstring for invertibility of an already constructed map.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and the imported coefficientExtensionIntegers.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth and
  SmoothOfRelativeDimension (read their full class signatures and docstrings).
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule and boundedConstructibleFiniteTor;
  these finite-etale categories occur through ReductionExceptionalRealization.
- Sheaf.Paper.SmoothPurityCoefficientTowers: spCoefficientTowers, spCoefficientRings.
- Sheaf.Paper.SmoothPurityCoefficientTowersAbelian: SpCoefficientTowersAbelian,
  sp_coefficient_towers_abelian, with its actual evaluation and reduction interface.
- Sheaf.Paper.SmoothPurityNormalizedTowers: spNormalizedConstructibleTorTowerCategory,
  spNormalizedConstructibleTorTowers, spFiniteConstructibleTorCategory.
- Sheaf.Paper.SemilinearDerivedSections: WeilConjectures.SemilinearSections.
  semilinearDerivedSections and AdjunctionEvaluation; the actual scalar/strict-transition
  calculus is used through Models and the published systemReduction.
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted: sfQbarTwistingFunctor and
  the existing signed coefficient lines, inherited without redefinition.
- Sheaf.Paper.SmoothPurityTowerGluing: SpTowerGluing.tower_gluing, Levels,
  support, coefficientMate; its units/counits and coefficient-mate reduction equations
  give the adjunction/evaluation interface asserted here in sequence-site coordinates.
- Sheaf.Paper.SmoothPurityTowerShriekLevels: SpTowerShriek.tower_shriek_levels,
  D, R, Ev, F, support evaluation and isomorphism detection.
- Sheaf.Paper.FieldShriekSystemComparison: FieldShriekSystem.Models, Laws, iso,
  comparison, normalized, scalarAssoc, scalarUnit, systemReduction.
  The local read clone lacks this newly landed module; all source modules were read
  from the live server with prescribed scompile.py --source.
- Sheaf.SecSmoothPurity.ReductionExceptional: reductionExceptional_isIso,
  reductionCtfScalar, reductionCtfCompactSupport, ReductionExceptionalRealization.
- Proof imports include FieldScalarNormalizedSystems, SmoothPurityTowerGamma,
  ReductionCompatibilities and Mathlib.CategoryTheory.Adjunction.Mates.

Edge cases checked before writing: d=0 is retained; empty schemes and zero objects
remain in the full subcategories; n=0 is exponent one, m=n is included throughout;
identity field extensions and repeated fields are explicitly included; ramified
extensions use ell powers and no unramified or flat-quotient hypothesis; the source
and target retain site object universe u+1, morphism universe u and coefficient
universe u+1 via the dependency's lifts. The theorem assumes no finite evaluation
faithfulness. No disputed statement or node fault was found.

Searches:

- msearch leansearch "scalar extension exceptional inverse image adjunction mate on
  derived towers": 8 hits, ordinary ModuleCat extension/restriction Hom bijections,
  not the normalized derived tower exceptional comparison.
- msearch leanfinder "scalar extension exceptional inverse image comparison as
  adjunction mate on derived coefficient towers": 8 hits, ordinary ModuleCat scalar
  adjunction/composition/unit results, no exact statement.
- msearch loogle "CategoryTheory.mateEquiv": 12 hits, generic mates, counit/unit,
  vertical/horizontal composition; reusable categorical calculus only.
- msearch grep "exceptional.*(system|comparison)|field.*exceptional": 0 hits.
- rg over lean/WeilConjectures and lean/Sheaf for the item id,
  FieldExceptionalSystem, exceptional system/comparison and field_exceptional:
  generic ExceptionalSystemInterfaces/Transport and gamma hits only; these concern
  etale-origin transport rather than field scalar extension and are not duplicates.
- blueprint_refs.py search "exceptional system": 11 broad blueprint matches, no
  duplicate interface for this particular counit transpose and its field cocycle.

## Second reading by ND

Read the node and module again hypothesis by hypothesis and clause by clause. The
orientation is b : C_Y P_A -> P_B C_X, hence component must transpose b inverse
followed by C_Y epsilon_A; the file does exactly that. Checked Lean's diagrammatic
composition order in both unit and counit equations and in the field cocycle.
The source/target evaluation maps use inverse source coordinates and forward target
coordinates; their endpoints are the finite transpose endpoints. Added explicit
rightReduction and mixed fields after the second reading to retain both quotient
paths and the specified right-adjoint quotient transition, beyond mere commutation
of an arbitrary system map. All these are conclusions and the normalized full
subcategory still has the ambient Hom sets. No mathematical statement changed.

## Validation

All nine delivered modules compiled with the prescribed scompile.py wrapper, in
canonical library and sandbox namespaces. The final run had no errors or warnings
other than the permitted theorem sorry. The deliver2.py --no-push dry run passed the maintainer preflight and per-file
compilation (dry-run commit 109f87c5b9f).

## New nodes

All eight new definitions serve clause (2), counit transpose, of the current source
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/`
`sk-lem-sp-field-extension-towers.proof.md`. Their individual source records name
that place. The common searches below and each node's mathlib_searches checked
these interfaces before introduction; existing declarations supply their components
but none packages these domains, adjunction normalizations, actual transposes or laws.

- `def-sp-field-exceptional-system-domains`: `Sheaf.Paper.FieldExceptionalSystemDomains`. Fix the global datum $P$ of [def-pur-conventions], the actual coefficient and proper/open model family $D$ of [def-sp-field-shriek-system-models], and a compactification $c$ of $f:X\to Y$. Write $N_E(T)$ for the transported normalized constructible finite-Tor full subcategory of [sk-def-sp-normalized-towers]. Domain data mean preservation of $N$ by each whole-system scalar extension and by the fixed compact-support functor, membership of all evaluated levels in finite $D_{ctf}$, and preservation of finite $D_{ctf}$ by finite scalar extension [det-sp-reduction-exceptional]. Define the restricted scalar, compact-support and evaluation functors by full-subcategory restriction of the actual ambient functors. This is a predicate on those functors, not an existence assertion.
- `def-sp-field-exceptional-system-finite-adjoint`: `Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint`. Fix the finite-field datum $P$ of [def-pur-conventions], a compactification $c=(j,p)$ of $f:X\to Y$, a finite coefficient field $E$ and a positive ell-power level $n+1$. Finite exceptional adjunction data consist of preservation of finite $D_{ctf}$ by the actual compact-support functor of [det-sp-reduction-exceptional], a right adjoint $G_{E,n}$ on those full subcategories, its adjunction, and its ordinary-etale counit-preserving realization [det-sp-reduction-exceptional]. No existence assertion is part of this definition.
- `def-sp-field-exceptional-system-adjoints`: `Sheaf.Paper.FieldExceptionalSystemAdjoints`. Use the actual whole-system model family and compact-support comparison laws of [lem-sp-field-shriek-system-comparison] and the domain restrictions of [def-sp-field-exceptional-system-domains] for a fixed compactification. An exceptional adjunction family consists of right adjoints $G_E$ to the restricted actual compact-support functors, their adjunctions, finite exceptional adjunction data [def-sp-field-exceptional-system-finite-adjoint] at every level, and natural isomorphisms evaluating the right and left adjoints. The left comparison is required componentwise to equal the published compact-support evaluation, and its adjunction mate must equal the right comparison. For every finite coefficient-ring homomorphism between two levels, the specified finite compact-support comparison at $G_{E,n}K$ is invertible. This packages normalization data only and asserts no existence.
- `def-sp-field-exceptional-system-components`: `Sheaf.Paper.FieldExceptionalSystemComponents`. In an exceptional system adjunction family [def-sp-field-exceptional-system-adjoints], for $E\le F$ and $K\in N_E(Y)$ define the exceptional whole-system component to be the $P_F\dashv G_F$ transpose of the inverse specified proper/open scalar comparison followed by scalar extension of the $E$-counit. For a homomorphism between arbitrary finite coefficient levels define its finite component by the same finite adjunction transpose using the actual finite compact-support comparison of [det-sp-reduction-exceptional]. Both maps are defined by the existing Hom bijection, not by choosing lifts of evaluated maps.
- `def-sp-field-exceptional-system-finite-composite`: `Sheaf.Paper.FieldExceptionalSystemFiniteComposite`. In the system and finite exceptional comparison data [def-sp-field-exceptional-system-components], for composable finite coefficient maps $A\xrightarrow\phi B\xrightarrow\psi C$, define the pasted finite exceptional component as the inverse source balanced scalar associator, followed by $\psi$-scalar extension of $c_\phi$, followed by $c_\psi$ at $K_B$, followed by $G_C$ of the target balanced scalar associator. Use precisely the canonical associators of [det-sp-scalar-extension-functor]. This defines a map with the same endpoints as the direct finite transpose for $\psi\phi$.
- `def-sp-field-exceptional-system-evaluation`: `Sheaf.Paper.FieldExceptionalSystemEvaluation`. For the actual system exceptional component [def-sp-field-exceptional-system-components], define its source evaluation comparison by the specified scalar evaluation followed by scalar extension of the right-adjoint evaluation. Define its target evaluation comparison by right-adjoint evaluation followed by the finite right adjoint of scalar evaluation. These are natural derived isomorphisms with exactly the endpoints of the specified finite exceptional transpose, using the adjunction-normalized comparisons of [def-sp-field-exceptional-system-adjoints] and [lem-sp-field-shriek-system-comparison].
- `def-sp-field-exceptional-system-laws`: `Sheaf.Paper.FieldExceptionalSystemLaws`. Fix the actual exceptional components and finite evaluation comparisons [def-sp-field-exceptional-system-evaluation] and the pasted finite components [def-sp-field-exceptional-system-finite-composite]. The exceptional comparison laws are: invertibility and naturality of the actual whole-system components; their defining tower counit and unit equations; equality of their finite evaluations with the specified finite transpose; right-adjoint quotient reduction equal to the finite quotient mate followed by the right adjoint of the actual input reduction; equality of both mixed finite coefficient paths with the direct transpose; commutation with actual system reductions; composition under the canonical balanced whole-system scalar associators of [lem-sp-field-shriek-system-comparison]; and identity under the canonical scalar unitors. These are a predicate on specified maps, not assertions of their truth.
- `def-sp-field-exceptional-system-iso`: `Sheaf.Paper.FieldExceptionalSystemIso`. Given the exceptional comparison laws [def-sp-field-exceptional-system-laws], define the natural isomorphism $C_XG_E\cong G_FC_Y$ by taking as its forward components precisely the actual counit transpose components of [def-sp-field-exceptional-system-components], and the inverses supplied by their invertibility. Naturality is the naturality clause of the given laws. This introduces no independently chosen isomorphism.

All new nodes have empty proof lists and real definitions. Searches for each
interface use the shared four-entry search log in their mathlib_searches; queries
cover domains, adjunction evaluation, transpose, mixed paths and scalar laws.
The full main statement is unchanged.

The final Adjoints storage is a dependent tuple, with explicit projections, rather
than a generated record. The left support comparison is included as data, fixed
componentwise by leftNormalized to the published support evaluation; counit is
the existing AdjunctionEvaluationNormalized predicate, with all functors explicit.
This is exactly the same counit-preserving evaluation assertion. Domains and Laws
are Prop-valued. Compilation diagnostics drove only these representation changes
and explicit full-subcategory endpoint annotations, not mathematical changes.

Each Laws clause is a named, definitionally explicit Prop predicate; Laws packages
those same ten predicates. This limits elaboration without changing any clause.
The iso definition unfolds only its invertibility and naturality predicates.
