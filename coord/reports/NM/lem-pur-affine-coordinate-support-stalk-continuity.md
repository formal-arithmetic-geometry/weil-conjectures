## Worker report

Statement delivery for `lem-pur-affine-coordinate-support-stalk-continuity`.
The module is `Sheaf.Paper.AffineCoordinateSupportStalkContinuity`.
Its principal declaration is
`WeilConjectures.PurityFiniteSetting.affine_coordinate_support_stalk_continuity`.
The companion declarations are part of the same assertion and are all listed in
`lean.declarations`. No statement correction, new node, or dependency module is needed.

Hypothesis and clause correspondence (names below in
`WeilConjectures.PurityFiniteSetting`, except the stated Etale names):

| Node text | Lean rendering |
| --- | --- |
| The finite datum k, ell, E, n, A, with n at least one | The section parameter `P : PurityFiniteSetting.{u}` is the recorded finite datum. `P.field.k` and `P.Coefficient` are its actual ground field and lifted valuation-ring quotient. The positive level and distinct primes are fields of that datum, not additional assumptions. |
| Any commutative k-algebra R | `(R : Type u) [CommRing R] [Algebra P.field.k R]`; no finiteness, reducedness, smoothness, Noetherian, nonzero-ring or ramification-divisibility assumption. |
| Integer r and b at least zero | `(r : ℤ)` and `(b : ℕ)`; the signed sheaf uses the recorded finite tensor powers/internal dual, including negative r. |
| Finitely generated subalgebras ordered by inclusion | `ContinuityIndex R = {S : Subalgebra P.field.k R // S.FG}` with its inherited poset category. This is the index of the published `CommRingCat.fgSubalgebraDiagramOf`, not an arbitrary system of rings. |
| B_i=Spec R_i, B=Spec R, affine b-spaces and their zero sections | `continuitySpace`, `continuityOrigin`, and `continuityProjection` use `AffineSpace (ULift (Fin b)) (Spec (.of R))`, `AffineSpace.zeroSection`, and `AffineSpace.map` of the literal subalgebra inclusions. |
| Complementary opens j_i and j | The recorded `coordinateSupportSheaf` uses `(continuityOrigin R b).openComplement.ι`. The module's `continuityComplementMap` is the open-immersion lift of the actual ambient base change, and `continuityComplementSquare` records its factorization. |
| Ordinary small etale site, finite coefficients and bounded-below RQ | Every sheaf is `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} P.Coefficient)`. `continuityH` uses `Plus.singleFunctor 0`, the recorded `coordinateSupportedStalk.rightDerivedFunctorPlus`, and `Plus.homologyFunctor d`. |
| The literal finite twist A_P(r) | `continuityTwist` is `P.functorialCupTwist false`, the signed finite Tate sheaf at `P.diagonalExponent = ell^n`, valid for every positive level. `continuityTwistIdentification` is the recorded roots/tensor/evaluation-normalized pullback from Spec k to the coordinate space. The colimit is written in these canonical pulled-back coefficients. |
| H^d(RQ(A(r))) at x | `continuityStalk` and `continuitySupportedSheafStalkIso` identify the derived-supported-stalk model with the literal stalk of the cohomology sheaf of the recorded kernel functor. The latter reconstructs the published derived-composition/exact-stalk isomorphism at the inferred localization universe; it neither chooses arbitrary data nor equates site universes. |
| Geometric point on C and its image x_i | `{Ω : Type u} [Field Ω] [IsSepClosed Ω]`, `x : Spec (.of Ω) ⟶ continuitySpace R b`, and `hx : Set.range x.base ⊆ Set.range (continuityOrigin R b).base`. This includes algebraically closed geometric points and also the equivalent separably closed convention of the published etale-stalk API. `continuityPoint` is exactly `x ≫ continuityProjection`. |
| Every integer degree | `(d : ℤ)` throughout. |
| Canonical supported pullback transitions and legs | `Etale.affineSupportGerm_existsUnique` states the kernel-inclusion characterization; `affineSupportGerm` chooses only that uniquely determined natural transformation. `affineDerivedSupportGerm` is its normalized bounded-below derived base change. `continuityLeg`, `continuityTransition`, and `continuityLimitLeg` take its actual homology map and the actual coefficient pullback comparison. Image-point equalities are transported explicitly. |
| The A-linear colimit isomorphism | `continuityDiagram` and `continuityCocone` specify all transitions and legs; `continuityComparison = colimit.desc ...`. The main theorem asserts `IsIso` of exactly this morphism in `ModuleCat P.Coefficient`. Thus invertibility means an A-linear isomorphism, not an unrelated bijection or a mere existence of some isomorphism. |
| Both negative-degree sides vanish | The second conjunct of the main theorem gives `d < 0 → IsZero (colimit ...) ∧ IsZero (...)`. |
| Coefficient-line maps, tensor identifications and dual identifications | `continuity_coefficient_naturality`, `continuity_transition_coefficient`, and `continuity_comparison_coefficient` give actual commuting squares for every map of ground coefficient sheaves. In particular they apply to maps of the constant rank-one L_r, to the normalized signed tensor identifications, and to evaluation. This does not assert continuity for tensor products of supported complexes. |
| Supported ordered coordinate Kummer products from affine space over k | `Etale.continuity_global_germ_composition` is the derived equality for *every supported global class*, with the recorded `coordinateGlobalToStalk` as its underived map. It applies to the actual ordered coordinate Kummer class and each supported factor. The recorded `supportedCupFunctoriality` provides their pullback compatibility. This uses a stronger naturality interface to express the node's clause, without replacing the Kummer class or assuming a purity/orientation theorem. |
| Corresponding localization boundary maps, with the same open exchanges | `continuityOpenExchange` is the published ordinary mate `baseChangeMap`, conjugated by `squareUpperStarIso`. `continuityOpenGerm` gives its stalk leg. `continuity_sequence_squares` prescribes the first two squares. `continuityResolutionMap` is the resulting actual morphism of support sequences on models. `continuity_localization_boundary` is the explicit equation between their `triangleOfSESδ` maps and the first and third components. Injective resolutions compute the bounded-below functors; uniqueness of derived-unit maps identifies these components with the supported/higher-image legs in the comparison. |
| Any cofinal directed family, unchanged isomorphism | `continuity_cofinal` quantifies over a nonempty directed poset `J : Type u` and a final inclusion/reindexing `e`. It asserts invertibility of the *canonical* reindexing map and the reindexed comparison, and equality of their composite with the original comparison. |
| Localization at one element, stages containing it | `ContinuityContaining` is the literal full subposet of subalgebras containing the element. `continuity_containing_final` supplies nonemptiness, directedness and finality. `continuity_base_change` is the commuting colimit comparison square for every k-algebra map, so applies to the canonical R to R[1/f]. `continuityIndexMap` uses actual image subalgebras, and `continuityStageMap` is the restricted algebra map. Localized stages R_i[1/f] are represented by adjoining the image of f inverse to these image stages; that family is cofinal in the finite subalgebras of R[1/f], since a finite list of fractions has finitely many numerators. `continuity_cofinal` identifies its comparison with the one in the displayed square. |
| Common affine refinement and agreement of compatible finite orientations | `continuity_base_change` and `continuity_leg_composition` apply to every principal affine restriction and its composites. Choose a principal affine neighbourhood inside the intersection at the point (the whole intersection need not be affine). The commuting squares identify both constructions with their common restriction. Equality of the finite orientations is then preserved by these very same linear legs. No new orientation is chosen. |
| b=0, empty punctured opens | No declaration assumes b positive. `continuity_zero_coordinates` explicitly states the constant-fibre description in degree zero, vanishing in every other degree and invertibility of the comparison. Kernel normalization makes these legs the ordinary constant-line legs; the node's empty-product and zero-boundary conclusions follow from the empty complementary open. |

Dependencies and exact declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, and its commutative-ring instance.
- Mathlib `AlgebraicGeometry.Scheme`, `.Hom`, `AffineSpace`,
  `AffineSpace.map`, `IsOpenImmersion`, and `Scheme.smallEtaleTopology`;
  upstream `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` supplies
  `AffineSpace.zeroSection` and its closed-immersion instance.
- `Sheaf.AlgebraicGeometry.EtaleCoordinateSupport`: `coordinateSupportSheaf`,
  `coordinateSupportInclusion`, `coordinateSupportedStalk`,
  `coordinateSupportedStalkInclusion`, `coordinateGlobalSupport`, and
  `coordinateGlobalToStalk`. Its existing etale-only restriction constructor is not
  used for non-etale affine projections: the unique kernel-normalized germ
  factorization is supplied here for arbitrary maps, as an owning-node helper.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`: the pointed-neighbourhood
  stalk model, `Scheme.pointSmallEtale` and `upperStarCompSheafFiberIso`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and Mathlib:
  `DerivedCategory.Plus`, `.singleFunctor`, `.homologyFunctor`, and
  `Functor.rightDerivedFunctorPlus`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` is the dependency's recorded
  intrinsic coefficient-twist module; only its finite specialization is used here.
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist` and
  `FiniteEtaleTateSheaf` supply `Scheme.finiteEtaleTateTwist` and
  `Scheme.finiteEtaleTateSheaf` (positive tensors and negative internal duals).
- `def-pur-supported-class-operations` owns the existing definitions
  `functorialCupTwist` and `functorialCupEtaleTwistPullback` in
  `Sheaf.Paper.SupportedCupFunctoriality`. These plain definitions occur in the
  delivered signatures/data and use the canonical finite exponent
  `diagonalExponent`, not the divisible-level-only `P.exponent` API. This landed
  definition node and the signed finite-Tate-sheaf node are added to `stmt_deps`.
  `lem-pur-supported-cup-functoriality`, in the same module, remains in
  `proof_deps`: its theorem `supportedCupFunctoriality` supplies the proof's
  compatibility laws, but is not referenced or chosen by any delivered Lean term.
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`:
  `CommRingCat.fgSubalgebraDiagramOf`, whose exact poset and algebra inclusions are
  used by the coordinate model. `Subalgebra.map`, `.FG.map`, `.inclusion` and
  `AlgHom.codRestrict` are the actual image-stage constructions.
- `Functor.rightDerivedFunctorPlusBaseChange`,
  `Functor.rightDerivedFunctorPlusCompIso`, exact-functor derived comparisons,
  `Etale.baseChangeMap`, `squareUpperStarIso`,
  `ShortComplex.mapCochainComplexPullback`, and `DerivedCategory.triangleOfSESδ`
  supply the canonical comparison and boundary constructions.
- All recorded, available proof-dependency modules are imported privately, including
  relative higher-image continuity, exact stalk colimits, forgetting-coefficient
  exchange, injective support sequences and K-injective comparison. Mathlib's
  bounded-below injective-resolution, K-injective and exact-filtered-colimit modules
  are also included. No downstream purity or orientation theorem is imported.

Edge cases checked before writing: b=0 (explicit full-support theorem), b=1 (the
single principal puncture), R=0 (no geometric point), negative d, d=0 and d=1
(kernel/cokernel argument), d at least 2 (shifted open higher images), negative r
(internal sheaf dual), arbitrary positive n including levels not divisible by the
ramification index, arbitrary non-Noetherian R, nilpotents, a localized zero ring,
and affine intersections that are not themselves affine. The index is the genuine
finite-subalgebra poset, and the cofinal family has explicit directed/nonempty
hypotheses. No counterexample or statement fault was found.

Searches made with msearch.py, group NM and this item:

- LeanFinder: `filtered colimit geometric stalk local cohomology supported on zero
  section of affine space`: eight hits about ordinary scheme/module stalks and
  localizations, no supported-etale continuity statement.
- Loogle: `CategoryTheory.Limits.colimit.desc, AlgebraicGeometry.AffineSpace`:
  no hits.
- Mathlib grep: `coordinateSupport|supported.*colimit|stalk.*continuity`: no hits.
- LeanSearch: `filtered colimit geometric stalk cohomology with closed support
  affine inverse limit`: eight general colimit/affine-limit hits, no such statement.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for `coordinateSupport`,
  `affineCoordinate`, `supportStalkContinuity`, and the exact item id: found the
  recorded support functors and older coordinate-model theorem, but no affine
  supported-stalk continuity statement with these legs and compatibilities.
- Additional rg found the published `fgSubalgebraDiagramOf` ring diagram and the
  existing canonical open-exchange/short-exact derived-boundary APIs, which are reused.
  No private copy of the support or finite twist notion is introduced.

Sources read: Stacks etale-cohomology.tex lemma-relative-colimit-general (0EYM),
section-cohomology-support (09XP), and lemma-cohomology-with-support-triangle (0A45);
the current blueprint frame-independence statement and first sheaf-germ proof
paragraphs; the item and every stmt_deps node and recorded declaration.

All definitions have real construction data. The sole choice is from the named
unique kernel-factorization theorem; uniqueness determines precisely the map used
by all downstream constructions. Every postponed theorem belongs to this item's
canonical-map assembly or compatibility clauses, is listed in `lean.declarations`,
and has a source and proof plan in its docstring. Every theorem body is `by sorry`.
The three named additive instances simply reuse existing typeclass data.

Validation: prescribed scompile.py, server single-file sandbox and library-name
compilations, clean with no warnings. No local compile, global build, direct git
operation, or shared-source edit was made.

## Second reading by NM

Self-audit of the node and module, not an independent-agent review: the dispatcher
explicitly prohibits starting other agents and assigns the independent review to
the maintainer. Checked each row above against the actual signature/data. During
this audit I replaced a tautological refinement equality with the actual affine
base-change comparison square, added an explicit resolution-boundary equation,
and reconstructed the canonical sheaf-stalk comparison at the inferred derived
localization universe instead of imposing a universe equality. The file compiles
with all coefficient, point, support and index parameters explicitly bound.

## Returned-delivery repair (2026-10-21)

Repaired H2 from the independent review of immutable head `94c669a47203`:
replaced `lem-pur-supported-cup-functoriality` in `stmt_deps` with its landed
plain-definition owner `def-pur-supported-class-operations`, and retained the
theorem node in `proof_deps`. Updated the dependency paragraph above. The module
is unchanged, as the return requests; the advisory redundant bare `Nonempty`
clause in `continuity_zero_coordinates` is retained. No mathematical statement,
proof dependency, or other node field is changed by this repair.

Self-check: the saved packet's initial dry run passed; nevertheless its statement
dependencies still contained the returned H2 defect, which is now repaired.
Read both owning node records and the definitions' signatures and docstrings;
confirmed that the delivered module uses `functorialCupTwist` and
`functorialCupEtaleTwistPullback` and never references `supportedCupFunctoriality`.
The delivery wrapper rebases the retained packet onto the current live branch.
