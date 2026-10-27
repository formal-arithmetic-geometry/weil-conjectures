## Worker report

The module `Sheaf.Paper.TowerOperationsGroundFieldRetagging` states
`AlgebraicGeometry.ProEtale.sp_tower_operations_ground_field_retagging` with `sorry`.
It constructs the retagging functor and the same underlying compactification, and
specializes the existing scalar-extension and signed-line definitions to the actual
ell-power quotient rings. Its helper definitions contain real data; there is one
postponed theorem. The repair adds two definition-owner nodes for already published data; it adds no Lean
definition, theorem, or dependency module.

The maintainer returned immutable head `9ad95781f860` for H2: two theorem nodes
were cited in `stmt_deps` only to obtain definitions in their modules. The saved
packet passed the initial required dry run (`2c6d8d59bb1`), but that mechanical pass
does not resolve the independent return. This repair removes the two sandbox-added
theorem statement dependencies and replaces them with definition owners:
`def-pur-signed-line-scalar-normalization-data`,
`def-sp-commutative-coefficient-ring-tower`, and the two new nodes below. The nodes
`det-sp-coefficient-towers-abelian` and
`lem-pur-signed-line-scalar-tensor-tower` remain in `proof_deps` verbatim. Their
containing modules remain public imports because the definition owners live in
those same modules. No theorem conclusion is used to state the retagging theorem.
The mathematical statement, proof, source, and full Lean module are retained.
The live base has no Lean attachment for this item; the sandbox differs from that
base only in the permitted `lean` and `stmt_deps` fields and new definition records.

### Hypotheses

| Node hypothesis or chosen datum | Lean rendering |
| --- | --- |
| Finite field of characteristic p and its fixed algebraic closure | `P : PurityFiniteSetting`, with `P.field : FiniteFieldDatum`; the finite cardinality, prime and algebraic-closure fields are the recorded global convention. |
| Prime ell distinct from p | `P.coefficients.l`, its inherited `Fact ...Prime` instance, and `P.coefficients.different`. |
| Finite extension E/Q_ell with its ring of integers | `P.extension`, the recorded finite-dimensional intermediate field in the fixed coefficient closure, and `Padic.coefficientExtensionIntegers`. The auxiliary positive `P.level` merely belongs to the conventions; every ell-power level is quantified independently below. |
| A_n = O_E/ell^n for n positive | `SpTowerShriek.R ... n` and `spCoefficientRings`: Lean index n denotes exponent n+1. The ideal is `spEllIdeal ... ^ (n+1)`, not the nth power of a uniformizer. |
| Separated finite-type k-schemes X and Y | `X Y : Over (Spec (CommRingCat.of P.field.k))`, with `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on each `.hom`. |
| A k-morphism f | `f : X ⟶ Y`; the Over morphism includes the structural-map equation. |
| Smooth, separated, pure relative dimension d >= 0 | `[IsSeparated f.left] [SmoothOfRelativeDimension d f.left]`, with `d : ℕ`. Mathlib's relative-dimension class implies smoothness and includes the empty-source case. |
| Field automorphism fixing k_0 | `σ : P.field.k ≃ₐ[P.field.k₀] P.field.k`. |
| Chosen compactification | `c : Compactification f.left`, with its existing `.i`, `.g`, open/proper instances and `.comm`. |
| The specified tower constructions | `b : SpTowerShriek.Base ...` and `o : SpTowerShriek.Operations ... b` fix the published normalized constructions once. These are construction-choice parameters from `tower_shriek_levels`, not extra conditions on f or its input towers. |

All variables and universes are bound explicitly and `autoImplicit` is false.
The small site has object universe u+1 and morphism universe u throughout. The
coefficient and module universe is u+1. No equality of those site universes is imposed.

### Conclusions, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| T^sigma is the same scheme, with Spec(sigma) composed with its structural map | `spGroundFieldRetag P σ := Over.map (Spec.map ...σ.toRingHom)`. Its object is literally `Over.mk (T.hom ≫ Spec.map ...)`; its underlying scheme and arrow are retained. |
| Identity of small pro-etale sites | Equality of `.left.ProEt` and heterogeneous equality of `ProEt.topology` at T and its retagging, for T = X or T = Y. |
| Same coefficient quotient maps, actions and semilinear transitions | Equality of the entire `spCoefficientRings` functors and the entire `spCoefficientPresheaf` on `(ℕ × T.ProEt)ᵒᵖ`. These include every horizontal quotient restriction, not only ring objects. `spCoefficientTowers` is the actual module-presheaf full subcategory on this presheaf, with no constraint on transitions. |
| Same abelian tower category, complexes and quasi-isomorphisms | Equality of `spCoefficientTowers`, of its `CochainComplex ... ℤ`, and of `HomologicalComplex.quasiIso ... (ComplexShape.up ℤ)`. The inherited morphisms and componentwise operations are those of the recorded category. |
| Same ordinary derived category | For every recorded abelian presentation A, equality of `spDerivedCoefficientTowers ... A`. A supplies the same quasi-isomorphism localization on both sides. |
| Same C_T, including uniform cohomological and Tor bounds and actual ambient arrows | Equality of the full predicate `spConstructibleTorTowers ... A` and its inclusion functor `.ι`. The predicate includes constructibility at every level and the single pair of cohomological and Tor intervals. The normalized predicate is deliberately not used. |
| Same ordinary unbounded derived tensor, unit, associativity, symmetry and coefficient comparisons | Equality of the entire `b.calculus` records. `Data.closed` retains the actual monoidal structure, while `tensorModels` retains its simultaneous K-flat total-tensor comparison. The unitors and associator are fields of that monoidal structure; the canonical symmetry is the localization of the same signed interchange of the same total complexes through the same representative comparison. Scalar extension models, tensor evaluation and `reduction_cocycle` are retained as parts of this record. The comparison is on system categories before evaluation. |
| Same exact pullback and pullback-tensor comparison | Equality of the entire `o.geometry` records for f and f^sigma, and explicitly of `SpTowerShriek.pull`. `Geometry` includes ordinary exact pullback, direct image, their specified ordinary adjunction and derived adjunction, and `tensorPullback` with its representative normalization. |
| Same Tate root and power transitions | Equality of the entire `proEtaleRootsOfUnityTower` functors, including power maps, and of `purTwistIntegralOne`, the prescribed inverse-root-limit scalar extension. |
| Same signed Tate lines at the actual quotient levels | Equality of `spEllTwistQuotient`, the actual commutative-ring-sheaf quotient of the constant valuation ring, and of `spEllTwistLine ... n m` for every n and every signed integer m. `spEllTwistOne` is precisely scalar extension of the published integral first line along that quotient. `spEllTwistLine` calls the dependency's `coefficientTwistLine`: tensor powers for nonnegative m and internal Hom for negative m. |
| Same signed quotient comparisons, including negative transitions | For independently chosen `Bσ` and `B` satisfying `SpEllTwistComparisonsNormalized`, the whole families are HEq and their actual `spEllTwistTransition` arrows are HEq for every m. At exponent one, the predicate fixes the map on ordinary local pure tensors by `s ⊗ (t ⊗ x) ↦ s q(t) ⊗ x`. All other exponents use the published `SignedLineComparisonNormalized`, whose negative formula is dual comparison followed by precomposition with the inverse positive comparison. The semilinear arrow is constructed by `scalarExtensionEmbedding` followed by restriction of scalars of `(B m).hom`. |
| Same twist multiplication, contraction and reassociation | For independently normalized `μσ` and `μ`, equality of the entire signed-product families. The condition is exactly `SignedLineProductNormalized` on these finite Tate lines, so includes a=0, b=0, positive and negative powers, and mixed-sign contractions. Applying the identical whole-tower tensor calculus to these identical ordinary maps gives the twist reassociations before any finite derived evaluation. |
| Same retagged ambient compactification | `spGroundFieldRetagCompactification` retains all ordinary compactification fields. Its ambient structural map over k is `.g ≫ ((spGroundFieldRetag P σ).obj Y).hom`. The compactification is an ordinary factorization, so no new geometric map is chosen. |
| Same compact-support functor on bounded-below towers | HEq of `DerivedCategory.Plus.ι ⋙ SpTowerShriek.F ... c` and its retagging. This compares entire functors and all derived tower arrows; the conclusion is restricted to Plus. `F` is the published exact open extension followed by total right derived direct image. |
| Same underlying pullback/direct-image adjunctions and extension-by-zero comparisons | HEq of `o.openOp` for j, of `o.geometry` for p, and of the full `o.openTensor j` family. These records include the ordinary and derived adjunctions with specified units/counits, and the inverse-adjunct normalization of the open-tensor isomorphism. |
| No input reduction-isomorphism condition | No `IsSpNormalizedTower`, cartesian-system condition, transition-surjectivity hypothesis, or derived reduction-invertibility assumption occurs. Canonical normalization of the comparison MAPS B and μ is distinct from normalization of input TOWERS. |

The comparison families B and μ are universally quantified with their defining
normalizations. They are not arbitrary replacement maps. Their existence is the
existing signed-line result applied to the finite Tate lines; uniqueness is tested
by comparing independent normalized choices. The theorem does not infer equality
of derived arrows from equality of evaluations. It compares ordinary transition
maps, full tensor representative data, and full functors on the common system site.

### Dependency declarations read and used

| Module | Declarations or interfaces used |
| --- | --- |
| `Sheaf.Paper.PurityFiniteSetting` | `WeilConjectures.PurityFiniteSetting` and its finite-field/coefficient data. |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing`; the imported original coefficient constructions fix O_E, its uniformizer and finite quotients. |
| `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact` | `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`. |
| `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `IsProper` and inherited separation for compactifications; explicit `IsSeparated` hypotheses. |
| `Mathlib.AlgebraicGeometry.Morphisms.Smooth` | `Smooth`, `SmoothOfRelativeDimension`. |
| `Sheaf.Paper.SmoothPurityCoefficientTowers` | `spEllIdeal`, `spCoefficientRings`, `spCoefficientPresheaf`, `spCoefficientTowers`. |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | `SpCoefficientTowersAbelian` and `spCoefficientEvaluation`, owned by new `def-sf-coefficient-towers-abelian-presentation`; `spCoefficientCommRings`, already owned by `def-sp-commutative-coefficient-ring-tower`. The abelianness existence theorem is only a proof dependency. |
| `Mathlib.Algebra.Homology.DerivedCategory.Basic` | `DerivedCategory`, `HasDerivedCategory`, quasi-isomorphism localization. |
| `Sheaf.Paper.SmoothPurityNormalizedTowers` | `spDerivedCoefficientTowers`, `spConstructibleTorTowers`; the unnormalized predicate and its full inclusion, not the normalized category named by the node's primary record. Both interfaces are public declarations of that recorded module. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | `SpTowerShriek.Base`, `.Operations`, `.Geometry`, `.Open`, `.B`, `.tau`, `.S`, `.pull`, `.F`, and `tower_shriek_levels`. |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | Its publicly imported original `CoefficientTwistsDetailed` interface: `coefficientTwistLine`, `purTwistIntegralOne`, and the coefficient-twist constructions. No Qbar twisting functor is substituted for a finite twist. |
| `Sheaf.Paper.SignedLineScalarTensorTower` | `signedLinePower` and `SignedLineComparisonNormalized` owned by `def-pur-signed-line-scalar-normalization-data`; `SignedLineProductNormalized` and `SignedLineBasisPowers` owned by new `def-sf-signed-line-product-normalization-data`. The signed comparison/product and tower theorems are only proof dependencies. The scalar unit construction is `scalarExtensionEmbedding` in the publicly imported scalar core. |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `ProEt.topology`. |
| `WeilConjectures.Compactification.RefinementCategory` | Its imported ordinary `Compactification` and recorded `Refinement` interfaces. |

All other already-stated proof dependencies have their modules explicitly imported
as plain imports. The theorem docstring gives the node's proof in eight paragraphs,
combining its tensor-model and tensor-coherence steps but retaining every cited node.

### Edge cases checked

- Sigma = identity: the structural map is postcomposed with Spec(id), and the
  underlying scheme and every constructed tower operation remain the same.
- Empty source or target and d=0: all category and functor expressions still exist;
  no nonemptiness, point, basis or positive-dimension hypothesis was added.
- Zero objects and strict towers with zero transition maps: the ambient category is
  `spCoefficientTowers`, not its normalized full subcategory. The conclusion applies
  to such towers; quotient comparison conditions concern only the fixed Tate line.
- The first coefficient level is n=0 in Lean, meaning exponent one. No zero-ring
  exponent-zero level replaces it. Every positive source level is included.
- Ramified E: the ring used is always O_E/(ell)^(n+1). Rank-one trivializations can be
  checked using the source's cofinal uniformizer filtration at exponent e(n+1), but
  no unramified hypothesis or identification of ell with a uniformizer is imposed.
- Twist exponent zero, negative exponents and mixed signs are included by integer
  quantification and the actual signed-power/dual normalization.
- The compact-support comparison uses Plus; pullback and tensor remain on the
  ordinary unbounded derived category.
- The equality of the C_T predicates includes the independently chosen uniform Tor
  and cohomological intervals; it does not impose an equality of those intervals.

### Searches and source checks

I read the node, every statement dependency and its recorded declaration/docstring,
Q30's stage-1 report, the current gamma proof (2)--(3), and the published system,
tensor, signed-line and compact-support module interfaces. There is no existing
Lean attachment for the item. The withdrawn example CompactObject module points to
the original `WeilConjectures.CategoryTheory.CompactObject`; I read that definition
and its DAG record as the current convention example.

Searches used the prescribed `batch2/msearch.py`:

- LeanFinder query: "Changing a scheme structural map by a ground field automorphism
  leaves strict coefficient towers and their derived operations unchanged". Eight
  results on Weierstrass base change and variable changes, none on the item.
- Loogle query: `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Equivalence.refl`.
  No hits.
- Mathlib grep query: `retag|Retag|spCoefficientTowers`. No hits.
- `rg` over the live `lean/WeilConjectures` and `lean/Sheaf` for
  `retag|Retag|ground.field`, then specifically `retag.*[Tt]ower|[Tt]ower.*retag`.
  The broad search found unrelated ground-field extension results and comments;
  the tower-retagging search found no existing statement.
- Exact blueprint-id search in `lean/WeilConjectures` found nothing.
- Exact helper and theorem-name search in both library roots found no declarations
  named `spEllTwist*`, `spGroundFieldRetag*`, or
  `sp_tower_operations_ground_field_retagging` before this delivery.

## New nodes

- `def-sf-signed-line-product-normalization-data` registers the unchanged definitions
  `SheafOfModules.SignedLineBasisPowers` and
  `SheafOfModules.SignedLineProductNormalized` from
  `Sheaf.Paper.SignedLineScalarTensorTower` with `existing: true`. It uses the
  already owned signed powers, tensor and sheaf Hom. Its statement records all
  four basis conditions: bijectivity after every restriction, the degree-zero
  unit, positive tensor recursion, and negative evaluation equal to one after
  every restriction. The product predicate quantifies over every such basis and
  every pair of signed integers and sends their tensor to the sum-degree basis.
  It asserts neither existence nor uniqueness. Source: the blueprint twist proof
  tensor-power/internal-Hom and finite-stage sentences, Stacks 03EK and 04TT.
- `def-sf-coefficient-towers-abelian-presentation` registers the unchanged structure
  `AlgebraicGeometry.ProEtale.SpCoefficientTowersAbelian` and evaluation abbreviation
  `spCoefficientEvaluation` from
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`, with `existing: true`.
  It cites the existing `def-sp-commutative-coefficient-ring-tower` for
  `spCoefficientCommRings`; it does not duplicate ownership of that definition.
  Its statement records the normalized equivalence, all four section/component
  equations, additivity, Grothendieck property, exact and filtered-colimit
  evaluation, ordinary derived localization, scalar/tensor models, ordinary
  adjunct reductions, derived representative equation, and equal-index and
  composite reduction equations. The evaluation abbreviation is exactly the
  equivalence followed by the existing system evaluation. The structure asserts
  no existence of a package. Source: the coefficient-tower blueprint clauses
  (1)--(3), the same source used by the published declaration.

Both new nodes have only definition-node dependencies, empty proof and proof_deps,
matching source records, the item's chapter/unit, and the required ancestry and
creation metadata. No new module is written. The original retagging helpers stay
in the item's module; they specialize the existing quotient, scalar-extension and
signed-line constructions rather than introduce another tower notion.

### Repair searches

For each new definition record, the three required `msearch.py` services were run
on 2026-10-22 and their actual results are recorded in `mathlib_searches`:

| Tool | Query | Result |
| --- | --- | --- |
| LeanSearch | `signed powers of a line sheaf normalized local basis tensor product multiplication` | Eight hits on ordinary/graded tensor powers and bilinear multiplication; no signed sheaf-line normalization predicate. |
| LeanFinder | Same signed-power query | Eight hits on cotangent bases and scheme structure-sheaf formulas; no match. |
| Mathlib grep | `SignedLineBasisPowers\|SignedLineProductNormalized` | Zero hits. |
| LeanSearch | `abelian presentation of varying coefficient towers with exact evaluation and normalized derived reduction maps` | Eight hits on algebra presentations, free abelian groups, the standard derived localization and tactics; no coefficient-tower data package. |
| LeanFinder | Same abelian-presentation query | Eight hits on algebra presentations; no match. |
| Mathlib grep | `SpCoefficientTowersAbelian\|spCoefficientEvaluation` | Zero hits. |

`rg` over both `lean/WeilConjectures` and `lean/Sheaf` found the existing definitions
in the two modules above and consumers, with no upstream replacement. Scanning all
DAG definition-node Lean records found no owner of the newly registered predicates
or presentation. It did find `def-sp-commutative-coefficient-ring-tower` and
`def-pur-system-level-left-extension-basic`, which are reused. The latter already
owns `StrictRingSystem`, `SystemScalarAssignment` and `SystemTensorCoherence`.
`tools/blueprint_refs.py search` found zero matches for the exact structure and
product names, and for `signed line` and `abelian presentation`. The ancestor
command confirmed `thm-pur-weil-equivariance-of-purity-and-trace`.

### Edge cases of the definition records

The signed predicates include zero and all negative degrees, every site object
and restriction, mixed signs and zero in both product positions. They do not add
a local-basis existence hypothesis to the retagging statement. The abelian
presentation retains equal-index transitions and reductions, every positive
coefficient level, and arbitrary strict towers, including zero and noninvertible
transition maps. Independent scheme and coefficient universes are retained with
coefficient universe `max u (t+1)` and its successor localization universe.
No mathematical statement correction or dispute is needed.

## Second reading by Q51

Author self-check for this repair: I reread the item and its complete saved Lean
module against the clause tables above. All geometric hypotheses, site and
coefficient identities, complexes and quasi-isomorphisms, unnormalized full
subcategory predicates, full tensor and geometry records, roots and signed
quotient transitions, normalized comparison/product uniqueness, bounded-below
compact support, and open extension tensor comparisons are unchanged. In
particular the module source is untouched and `lean.statement` remains its
signature verbatim. The new node signatures are verbatim from their existing
sources. The product definition and its basis predicate are genuine definitions,
not the existence/uniqueness theorem. The abelian-presentation definition is the
structure with its fields, not the theorem asserting `Nonempty`.

Return H2 is addressed by definition ownership alone: the two offending theorem
ids are absent from `stmt_deps`, still present in `proof_deps`; the scalar
normalization and commutative coefficient tower use their landed owners; the two
remaining notions have the new `existing: true` owners above. No rejected
statement is rebound and no definition or module is duplicated.

### Validation

The saved packet passed the initial required dry run at `2c6d8d59bb1` before this
repair. The repaired packet is compiled with the prescribed `scompile.py` and
checked with `deliver2.py --no-push` before final delivery; the results are appended
below.

Repaired module compile: `scompile.py` succeeded in sandbox mode (21.5 s) and
under its real module name (17.0 s), with no diagnostics. The complete theorem
signature and both new existing-definition signatures match the source verbatim.
