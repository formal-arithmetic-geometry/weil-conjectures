## Worker report

Item: lem-sp-field-purity-system-transpose. The module
`Sheaf.Paper.FieldPuritySystemTranspose` states
`AlgebraicGeometry.ProEtale.FieldPuritySystem.field_purity_system_transpose`.
It defines the tensor mate by the actual tower adjunction Hom equivalence. There
is exactly one postponed proof, the named item theorem. Every definition has real
data; auxiliary structures describe canonically normalized coordinates, whose
existence is part of the conclusion, rather than an extra assumption.

Source read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md`,
paragraph (2), together with the item's five proof steps. The source node and all
its statement dependencies were read. No statement correction or dependency
repair is made.

### Hypotheses and clauses

- The global field and prime datum is `P : PurityFiniteSetting.{u}`. This retains
  the algebraic closure, characteristic, prime and inequality in the recorded
  convention, without an additional coefficient characteristic assumption.
- Finite coefficient fields are `E F : FieldShriekSystem.Index P`, and their
  specified inclusion is `h : E ≤ F`. The recorded Padic finite-extension rings
  and quotient ring maps are used through `Models P`; no unramified hypothesis
  is imposed. A level `n : ℕ` always means exponent `n + 1`.
- `X`, `Y`, and `f : X ⟶ Y` are explicitly bound section variables.
  The `Over`, `IsOver`, `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`
  instances on the structure morphisms state separated finite type over `k`.
  `d : ℕ`, `SmoothOfRelativeDimension d f` and `IsSeparated f` state smooth
  separated of pure nonnegative relative dimension. The displayed Noetherian
  instances follow from finite type over the field. `QuasiCompact f` follows
  from finite type over this base; `HasCompactification f` is already witnessed
  by the fixed `c : Compactification f`. These are explicit instance plumbing
  for the recorded finite purity and right-adjoint APIs, with no restriction
  beyond the node's hypotheses.
- Strict systems, their ordinary derived categories and their uniform normalized
  constructible finite-Tor full subcategories are the recorded
  `SpTowerShriek.D` and `FieldExceptionalSystem.N`. The latter is defined using
  the specified realization of `spNormalizedConstructibleTorTowerCategory`.
  Thus the section-coordinate presentation is the existing site's actual
  equivalence, rather than a replacement by a family of finite derived objects.
- Whole-system scalar extension is `(D.scalars E F h T).T`; it is the recorded
  semilinear derived tensor functor. The ordinary coefficient map in `ScalarUnit`
  is normalized on sections by `FieldShriekSystem.coefficientMap`, and its
  derived map is constrained by the specified resolving counit and single
  complex comparison. It is not an arbitrary isomorphism of units.
- The same `c` is used by both supports. `b : FieldShriekSystem.Laws P D c`
  gives the canonical proper/open comparison. `a : Domains P D c` retains its
  normalized domain, and `A : Adjoints P D c b a` supplies the stated supports,
  rights, adjunctions, finite adjunctions and actual evaluation comparisons.
  `exceptionalLaws` is their recorded counit-normalized exceptional comparison
  law. In particular the morphism called `component` is the dependency's actual
  transpose of the inverse support comparison followed by scalar counit.
- `unit`, `omega` and `tensorSource` introduce only the full-subcategory packaging
  of the existing coefficient unit, its specified exceptional image, and the
  actual pullback/tensor source. `Coordinates.unit_mem` and `tensor_mem` record
  their required memberships; the theorem asserts these coordinates exist.
- Each of the three witness pairs in the node is a separate `PairDomain`
  argument: `(K, omega E)`, `(C K, omega F)` and `(C K, C omega E)`.
  `inputOrigin`, `outputOrigin`, `inputTor`, `outputTor` retain precisely the
  two `SpTowerShriek.Origin` and two `GoodLevel` families of shriek-levels (2a).
  They impose no compatibility between different finite-level origins.
- `leftProjection` is imported from `FieldProjectionSystemSquare` and is the
  actual projection map with its required symmetries. `projectionCounit` is
  its inverse, then tensor of the identity with `(A.adj E).counit.app J`, then
  the right unit constraint. `tau` applies `(A.adj E).homEquiv` to that exact
  morphism. The theorem asserts the needed `IsIso` proofs exist on the given
  domain; it does not assume invertibility as an extra hypothesis.
- `unitConstraint` is tensor of the recorded geometric coefficient pullback
  comparison with the identity, followed by the specified left unit. The first
  equality in the theorem says `tau` at the coefficient unit equals that map,
  which is precisely identity after applying the unit constraint.
- `omegaComparison` is the dependency's `component` at `J_A`, followed by the
  right adjoint applied to the canonical scalar unit identification. Thus it
  is the node's `c_JA` with `C_Y J_A = J_B`, including its actual normalization.
- `TensorCompatibility` is the first displayed equality, in Lean composition
  order: `C_X.map tau_A ≫ component K = projectionTarget.hom ≫
  tensor.map (id, omegaComparison) ≫ tau_B`. The target comparison is the
  dependency's scalar tensorator and canonical pullback compositor, not an
  arbitrary source isomorphism. This is an equality in the ordinary system
  derived category, before evaluation or inverse limit.
- `FiniteTensorIdentification` records every positive level, the fixed
  coefficient, tensor and site word constructors, and the ordinary unit origin
  equation. Its `WordComparison` identifies the actual `tau` with
  `finiteTheta`. The latter uses exactly `smoothPurityEtaleTheta`, transported
  by the counit-preserving `rightAdjointUniq` for the same compactification and
  the normalized input-unit comparison. This explicitly includes the clause
  that the tensor maps are those of def-pur-co-smoothness, at each level.
- Twists and shifted lines use the recorded `SpChartAdmissibility.Twists` and
  `SpTowerGamma.orderedLine`. `DiagonalOrientation` uses the recorded finite
  diagonal `OrientationNormalized`, the actual `coefficientWord`, root maps,
  tensor maps, unit map and exceptional evaluation. Its finite orientation
  arrow is the inverse diagonal isomorphism, transported through the canonical
  coefficient unit and counit-preserving right-adjoint comparisons.
- `gamma` is literally `tensor.map (id, orientation.hom) ≫ tau.hom` in the
  normalized section coordinates. This is the formula of
  `SpTowerGamma.gamma`/`tensorMate`, with the full-subcategory and realization
  identifications already applied by the exceptional comparison interface.
  `FinitePurityIdentification` explicitly asserts that every finite evaluation
  is `Etale.FiniteSmoothPurity.gamma` with the normalized diagonal orientation,
  followed by the counit-preserving finite right-adjoint comparison. The
  theorem includes this assertion for every coefficient field and diagonal
  orientation, independently of the subsequent scalar-orientation hypothesis. This retains
  actual root, pullback and tensor comparison arrows and does not infer
  equality of system arrows from finite evaluations.
- `DiagonalPurityCompatibility` states the second displayed equality for the
  diagonal orientations. Its hypothesis is exactly
  `C_X.map aE.hom ≫ omegaComparison = line.hom ≫ aF.hom`.
  `puritySourceComparison` is the canonical scalar/pullback tensor comparison
  followed by tensor of the identity with the given twist-line comparison.
  The assertion applies in particular to the canonical twist comparison named
  in the node. Lean's left-to-right composition displays the same square as
  the node's right-to-left mathematical composition.

### Dependency declarations

These are the existing declarations used, including their full signatures and
source docstrings read in the repository. Imports are public for statement
interfaces, and plain imports are used for proof-only inputs.

| Node | Module and declaration/interface |
| --- | --- |
| def-pur-conventions | `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`, `Padic.FiniteCoefficientFields` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.SmoothOfRelativeDimension` |
| def-sf-setting | `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, `Etale.DerivedCategoryModule`, `Etale.boundedConstructibleFiniteTor` |
| sk-def-sp-coefficient-towers | `Sheaf.Paper.SmoothPurityCoefficientTowers`, `AlgebraicGeometry.ProEtale.spCoefficientTowers` |
| det-sp-coefficient-towers-abelian | `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`, `sp_coefficient_towers_abelian` |
| sk-def-sp-normalized-towers | `Sheaf.Paper.SmoothPurityNormalizedTowers`, `spNormalizedConstructibleTorTowerCategory` |
| lem-coef-semilinear-derived-sections | `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`, `ScalarData.T` |
| def-coefficient-twists-detailed | `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor`; its tower presentation is the recorded `SpChartAdmissibility.Twists` |
| det-sp-tower-gluing | `Sheaf.Paper.SmoothPurityTowerGluing`, `SpTowerGluing.tower_gluing` and its adjunction/level interfaces |
| det-sp-tower-shriek-levels | `Sheaf.Paper.SmoothPurityTowerShriekLevels`, `SpTowerShriek.tower_shriek_levels`, `Origin`, `GoodLevel`, `projection` |
| lem-sp-field-shriek-system-comparison | `Sheaf.Paper.FieldShriekSystemComparison`, `FieldShriekSystem.Models`, `Laws`, `comparison`, `iso`, `normalized` |
| lem-sp-field-exceptional-system-comparison | `Sheaf.Paper.FieldExceptionalSystemComparison`, `FieldExceptionalSystem.Domains`, `N`, `Adjoints`, `Laws`, `component`, `scalar`, `support`, `level` |
| def-exchange-projection | `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`; the tower specialization is the recorded `leftProjection` |
| def-pur-co-smoothness | `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `WeilConjectures.IsCohomologicallySmoothFiniteCompared`, `Etale.dualizingComplexTensorMap` |
| det-sp-tower-gamma | `Sheaf.Paper.SmoothPurityTowerGamma`, `SpTowerGamma.tower_gamma`, `orderedLine`, `tensorMate`, `gamma`, `coefficientWord`, `FiniteLevels` |
| def-pur-smooth-purity-map | `Sheaf.Paper.SmoothPurityMap`, `WeilConjectures.PurityFiniteSetting.smoothPurityMap`, `smoothPurityEtaleTheta`, `smoothPurityUnitIso` |

Proof-only interfaces read: `Sheaf.Paper.FieldScalarNormalizedSystems`,
`field_scalar_normalized_systems`; `Sheaf.Paper.FieldProjectionSystemSquare`,
`ProjectionTensorComparisons`, `leftProjection`, `projectionTarget` and the
projection square; `Sheaf.SixFunctors.OpenTensorNormalization`,
`SheafOfModules.openTensorNormalization`. The coefficient, tensor and site word
constructors are reused from `Sheaf.Paper.TowerP1LevelWords` (`SpTowerP1`), and
`SpTowerClasses.CoefficientPullback` from the recorded tower class interface.

### Edge cases and searches

Checked against the definitions: `E = F` permits the identity coefficient map;
`d = 0` uses the actual unit branch of `orderedLine`; `K = 0` has the same
adjunction-transpose definition; empty `X` introduces no sections/nonemptiness
hypothesis; ramified extensions remain allowed because all quotients are by
ell-powers and the coefficient extension interface retains ramification. The
first quotient is included at index zero. No evaluation faithfulness assumption,
choice of a system lift, or inverse-limit equality is used.

Searches executed using the prescribed msearch wrapper (raw output retained in
`sandbox/searches.jsonl` while working):

- LeanFinder: `The counit transpose tensor map defining smooth purity commutes
  with scalar extension of derived coefficient towers`. Eight hits, concerning
  cotangent maps or ordinary scalar adjunctions; no exact system statement.
- Loogle: `CategoryTheory.Adjunction.homEquiv, CategoryTheory.NatTrans`.
  No hits.
- Mathlib grep: `purity.*transpose|transpose.*purity|field_purity_system`.
  No hits.
- LeanSearch: `counit transpose tensor map smooth purity compatible with
  coefficient extension on derived inverse systems`. Eight unrelated ordinary
  counit/coalgebra/smooth algebra results; no exact match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  purity/transpose and the relevant comparison declarations. No existing
  declaration states the item. These searches found the recorded tower gamma,
  exceptional mate and projection square interfaces reused above.

Two definition nodes separate the canonical arrow formulas and their finite
comparison words, reducing per-file compilation costs. The item adds only the
new level-word definition to stmt_deps, which reaches the arrow definition. No
dependency modules or statement changes are delivered.
No STATEMENT-DISPUTED issue was found.

### Verification

Compilation uses only the prescribed server `scompile.py` wrapper. An earlier
version exceeded 60 seconds; profiler output was inspected and composite
proposition/map definitions were marked irreducible to avoid repeated unfolding.
The word constructors whose endpoint reductions are needed remain reducible.
After another 70-second run, the maps, finite words, and theorem were split into
three modules (211, 250 and 101 lines), with new definition nodes for the first
two. Each delivered file is compiled separately in dependency order.
The delivered files have `autoImplicit false`, explicitly declared universes and
variables, no debug commands or profiler options, and only the expected theorem
`sorry` warning is permitted. Final compilation and preflight results are
recorded by the delivery wrapper.


## Second reading by NR

The delivery's original section was the worker's self-audit, written because the
dispatcher prohibits another agent. It is kept verbatim at the end of this section.
The clause-by-clause reading below was done by the maintainer's independent second
reader (cc review service, 2026-10-26) on the immutable head b366575e. That reader
opened the item node, every stmt_dep's Lean declaration, the source paragraph (2) of
`sk-lem-sp-field-extension-towers.proof.md`, and the three delivered modules.

Node clauses and their Lean renderings:

1. Finite field, closure k, char p, prime ell != p (def-pur-conventions):
   `P : PurityFiniteSetting.{u}`. Correct, and no extra characteristic assumption.
2. E in F finite over Q_ell, with R = O_E in S = O_F
   (def-weil-l-adic-coefficient-extension): `E F : Index P` and `h : E ≤ F`. Rings,
   quotients and coefficient maps come through `Models P`. Ramified F/E is allowed.
   Correct.
3. X, Y separated finite type over k; f smooth separated of pure relative dimension
   d ≥ 0: the `Over`/`IsOver`, `LocallyOfFiniteType`, `QuasiCompact` and
   `IsSeparated` instances, plus `d : ℕ`, `SmoothOfRelativeDimension d f` and
   `IsSeparated f`. The extra instances `IsNoetherian X/Y`, `QuasiCompact f` and
   `HasCompactification f` all follow from these hypotheses and from `c`, so they
   restrict nothing. This is the same plumbing as tower_gamma and
   field_exceptional_system_comparison. Correct.
4. Strict towers, their ordinary derived categories and N_A(T), N_B(T): `SpTowerShriek.D`
   and `FieldExceptionalSystem.N`, i.e. `normalized` = spNormalizedConstructibleTorTowers
   through the section realization, with uniform bounds and reduction isos. Correct.
5. C_T is whole-system scalar extension: `(D.scalars E F h T).T`, and `scalar P D a h T`
   on N. Correct.
6. P ⊣ G with η, ε, and the same compactification: `support P D c a E ⊣ A.right E`
   through `A.adj E`, with the single `c` for every coefficient. Correct.
7. b = proper mate followed by open tensor identification: `b : FieldShriekSystem.Laws`,
   via `FieldShriekSystem.iso`/`comparison`. Correct.
8. c_K is the transpose of C_Y ε_A,K ∘ b^{-1}: `FieldExceptionalSystem.component`, which
   is literally `(A.adj F).homEquiv` of `iso.inv ≫ C_Y(ε_A,K)`. Its laws are the
   hypothesis `exceptionalLaws`. Correct.
9. J_A, J_B, ω_A = G_A J_A, ω_B: `unit`, `omega`. Membership of the unit is
   `Coordinates.unit_mem`, a true fact asserted under the ∃. Correct.
10. The three witness pairs: the three `PairDomain` arguments. Each keeps exactly the
    two Origin and two GoodLevel families of shriek-levels (2a). Correct.
11. π_A, π_B: `leftProjection`, the published projection with both symmetries
    (lem-sp-field-projection-system-square, def-exchange-projection). Correct.
12. τ_A,K is the transpose of (1⊗ε_A,J) π_A^{-1}: `projectionCounit` = inv π ≫
    1⊗ε_J ≫ right unitor, and `tau` = `(A.adj E).homEquiv` of it. The unit constraint
    is the node's implicit K⊗J ≅ K. Correct.
13. "These are the specified tensor maps of def-pur-co-smoothness" (at every level):
    `FiniteTensorIdentification`. It gives the WordComparison of τ with `finiteTheta`
    = `smoothPurityEtaleTheta` (dualizingComplexTensorMap with unit and symmetry),
    transported by the counit-preserving `rightAdjointUniq` for the same `c` and by
    the pinned input unit `ui`. Correct.
14. Identity at the coefficient unit, under unit constraints: the second conjunct,
    τ(J) = `unitConstraint`, i.e. pulled-back unit (`CoefficientPullback.derivedIso`)
    followed by the left unitor. Invertibility of π at (J, ω) is asserted, not
    assumed. Correct.
15. First displayed equality, c_K ∘ C_X τ_A = τ_B ∘ (1⊗c_J): `TensorCompatibility`
    reads C_X τ_A ≫ c_K = projectionTarget ≫ 1⊗omegaComparison ≫ τ_B, where
    omegaComparison = c_{J_A} followed by G_B of the pinned scalar unit iso
    C_Y J_A ≅ J_B. Under the three witness pairs, both projection IsIso proofs are
    asserted (∃ hA hB). Correct, and stated before evaluation or limits.
16. τ(1⊗a) are the tower purity maps and evaluate to def-pur-smooth-purity-map:
    `gamma` is the same formula as `SpTowerGamma.gamma` (1⊗a then the transpose) on the
    normalized field-pair adjunction. `FinitePurityIdentification` asserts that each
    level is `FiniteSmoothPurity.gamma` with the normalized α. It holds for every
    orientation satisfying `DiagonalOrientation`, the inverse normalized diagonal
    iso at each level as in tower-gamma (1). OrientationNormalized fixes α, so the
    separate ∃ α loses nothing. Correct.
17. Second displayed equality, under c_J C_X a_A = a_B: `DiagonalPurityCompatibility`.
    For all diagonal orientations and line comparisons satisfying
    C_X(aE) ≫ omegaComparison = line ≫ aF, it gives C_X γ_A ≫ c_K =
    puritySourceComparison ≫ γ_B. The canonical twist comparison is a special case.
    It quantifies over every K with both projections invertible. The proof's third
    projection π_B(C_Y K, C_X ω_A) is then invertible by the projection square, so
    this is true and no weaker than the node. Correct.

Pinning of the existential data:
- `t`: the symmetries are pinned by signed K-flat generators, and the scalar
  tensorator by ScalarTensorComparisonModel.
- `q.tensors`: the unit iso is pinned by the RingedSiteDualityModel unit_model with
  `closed_eq`.
- `q.pullUnit`: pinned by the CoefficientPullback section normalization.
- `q.scalarUnit`: pinned by its sections equation through the adjunction unit and by
  the derived `model`.
- The finite coordinates cc/tc/gc/ui are the tower-gamma FiniteLevels coordinates,
  pinned the same way.
- `Coordinates.tensor_mem` (f^*K ⊗ W normalized) is true: levelwise tensor with
  normalization by associativity, and summed uniform bounds and Tor amplitudes.
No ∃ hides an arbitrary map.

Edge cases:
- E = F (le_rfl): allowed.
- d = 0: `orderedLine` gives the unit.
- K = 0: allowed.
- Empty X: no nonemptiness hypothesis.
- Ramified F/E: allowed.
- The first quotient is at n = 0 (exponent n+1).
- Universes: everything is in `u`, as in the dependencies.

Records:
- The item changed only `lean` and gained the new stmt_dep
  def-sp-field-purity-transpose-level-words.
- def-sp-field-purity-transpose-arrows is cited through that node.
- All three `lean.statement` fields are verbatim from the files.
- There is one sorry (the item theorem). No hollow definitions.
- Every declaration has source and blueprint docstrings. The item docstring carries
  the node's 5 proof steps. No line is over 100 characters.

Advisories (not faults):
- The new arrows node cites the lemma nodes, not the owners
  def-sp-field-exceptional-system-{domains,adjoints,components,laws}. The
  level-words node uses OrientationNormalized/gamma of
  def-pur-finite-smooth-canonical-maps through det-sp-tower-gamma.
- `inputWord`, `targetWord` and `finiteRightComparison` restate the tower-gamma
  constructors for an arbitrary Compactification c. The tower-gamma constructors need
  a literal j ≫ p factorization and SpTowerGluing.Levels, so they cannot be reused
  here.

Original self-audit text of the delivery:


The dispatcher explicitly prohibits starting another agent and delegates the
independent review to the maintainer. This section therefore records my separate
self-audit, not a claim of an independent worker review. I reopened the node,
source paragraph, finite theta definition, tower-gamma formula and finite
orientation equations. I corrected coefficient-map name resolution, made the
finite compactification/Noetherian instances explicit, and retained the canonical
unit comparison in the finite theta/orientation transports. I made the finite diagonal purity evaluation explicit in
`FinitePurityIdentification`, in addition to the finite theta equation. The two
displayed compatibility equations and all three supplied origin/Tor pairs are
present.
The maintainer's independent reading remains the delivery review.

## New nodes

`def-sp-field-purity-transpose-arrows` owns
`Sheaf.Paper.FieldPurityTransposeArrows`: the section-normalized scalar unitor,
canonical tensor/pullback coordinates, actual adjunction transpose tau,
coefficient-unit exceptional comparison, three-pair witness type, and displayed
system square, orientation composite, source comparison and unit constraint.
Its source is current blueprint paragraph (2). It uses the recorded normalized
`FieldExceptionalSystem.N/Adjoints` interface and existing projection and tower
word constructions, with no arbitrary map or existence choice. All definitions
have real data. The theorem asserts the existence of the canonical coordinate
structures. Its TeX definition cites every DAG interface used.

`def-sp-field-purity-transpose-level-words` owns
`Sheaf.Paper.FieldPurityTransposeLevelWords`: input/output finite words from the
retained etale origins, the unique counit-preserving ordinary adjoint comparison,
finite theta, normalized finite orientation, explicit finite purity evaluation,
and the conditional diagonal coefficient square. It depends on the new arrow
node and reuses `SpTowerP1` and the ordinary finite purity maps. Its source is the
same blueprint paragraph, including the specified finite maps. These are
proposition definitions, with no postponed proof.

For both nodes, I searched the DAG with `rg` and `blueprint_refs.py search
"tensor transpose"` (zero literal blueprint matches), and read the nearby
`def-sp-tensor-transpose-evaluation-words`,
`lem-sp-tensor-transpose-finite-evaluation` and
`lem-sp-tower-tensor-transpose-evaluation`. Their interfaces use the unnormalized
`SpTowerCalculus.C` adjunction and separate realization; these new definitions
are the canonical formulas directly on the dependency's normalized field-pair
adjunction. They reuse its data and the existing word constructors. I also
searched Mathlib via LeanFinder for "Canonical counit transpose of the inverse
projection formula on normalized derived coefficient towers, with coefficient
unit and scalar comparison" (eight unrelated cotangent results), LeanSearch for
"Finite etale evaluation words comparing the canonical tensor transpose and
diagonal purity map of normalized derived coefficient systems" (eight unrelated
duality/etale algebra results), and Mathlib grep for
`(purity.*transpose|transpose.*purity|WordComparison)` in CategoryTheory (no hits).
Direct searches of `lean/WeilConjectures` and `lean/Sheaf` found no
FieldPuritySystem/FinitePurityIdentification, only ScalarUnit structures for
other coefficient sites. All raw search entries are copied into each new
node's mathlib_searches. The data and definitions of the three modules have also
been read together in the self-audit described above.
