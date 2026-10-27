## Worker report

The module `Sheaf.Paper.DerivedScalarMateComposition` states the complete normalized
geometric scalar-mate result. The primary declaration is
`AlgebraicGeometry.DerivedScalarMate.derived_scalar_mate_composition` (composition and
identity); `normalization` gives the representative and counit-mate clauses, and
`commuting_square` gives arbitrary commuting-square pasting. All theorem proofs are
`sorry`. Definitions contain actual data, and choices occur only after uniquely
characterized existence theorems. Every helper is listed in `lean.declarations` and has
its owning-node source docstring. No mathematical statement correction is made.

The previous dispatch apparently treated the reviewed stage-1 split as completed work.
The current live item has status split, a reviewed stage-1 proof and no Lean record.
Stage 2 is precisely the missing statement. The retained sandbox contained only brief
markers, so this delivery creates its module and record from the current live node.

The coefficient and arrow structures package the objects already fixed in the statement;
they introduce no alternative sheaf category or freely supplied comparison map.
`Coefficients.model` is the existing `DerivedChangeOfRingsCochainModel`, whose ordinary
objects and maps are the actual sheafified tensor construction and whose derived pair
has the universal left-derived property. Normalized adjunctions are explicit fields,
with their ordinary and derived unit normalizations, rather than arbitrary adjunctions.
Restriction exactness and sheafification are the standard properties of these actual
categories and functors, included to elaborate the existing interface. In particular
these fields assert no flatness of the coefficient map.

Clause-by-clause correspondence:

- Schemes Z ->g T ->f S: the implicit `X Y Z : Scheme.{u}` are respectively the
  mathematical Z,T,S, and `g : Edge x y`, `f : Edge y z` carry their scheme maps.
  Each site is literally `Scheme.ProEt.topology X`, on `X.ProEt`, with object universe
  u+1 and morphism universe u. Coefficient/module universe is u+1. Standard derived
  localization has its existing u+2 Hom universe. No universe equality is imposed.
- The arbitrary commutative ring-sheaf map at each corner is `Coefficients.A`, `.B`,
  `.φ`. `Edge.cA` and `.cB` identify geometric inverse images with the source rings;
  `.compatible` says that the ring map is its transported inverse image. These are
  presentations of the statement's pulled-back rings, not additional flatness assumptions.
  `Edge.comp` uses exactly `proEtaleRingCompositeCoefficients` for both coefficients.
- Module sheaves and ordinary unbounded derived categories are the existing
  `Scheme.proEtaleRingModules` and `DerivedCategory`, including the actual localization
  `DerivedCategory.Q`. The internal-module equivalence is publicly imported as the
  node requests; no separate internal-module category is substituted for these categories.
- T_V is `Coefficients.model.T`, with ordinary tensor `model.E`, prescribed objects
  and maps, its universal counit `model.ε` and K-flat computation property. The fields
  `ordinary`, `derived`, `ordinary_unit`, `derived_unit` impose the representative-normalized
  scalar adjunction of the dependency. The tensor convention writes the scalar first.
- The geometric functors are the published `Edge.pA`, `.pB`, `.rA`, `.rB`; `.dA`, `.dB`
  are `proEtaleRingDerivedAdjunction`, which descends the uniquely unit-normalized
  module adjunction. No geometric adjunction or direct-image operation is a parameter.
- `Edge.restrictionSquare` is the unique identity on sections of direct image followed
  by scalar restriction. Its geometric inverse mate is `Edge.action`. Exact localization
  gives `.derivedAction`; the inverse scalar-adjunction mate is `.theta`, using the
  dependency's `ScalarPullback.mate`. These definitions fix the action square itself.
- `Edge.ordinaryTheta` is the same scalar mate before localization. Its inverse is
  `.chi`. Clause 1 of `normalization` is the ordinary scalar-unit equation. Under the
  tensor adjunction and its sectionwise universal property this uniquely fixes the
  balanced/coequalizer comparison: insertion of 1 tensor m is taken to insertion of
  1 tensor the inverse image of m. Thus chi is not an arbitrary tensor isomorphism.
- `.lambda` is the inverse isomorphism of `.theta`. Clause 3 of `normalization` states
  `lambda.inv = theta`, equivalently lambda = theta inverse, without asking Lean to
  synthesize an unavailable local IsIso instance in a public signature.
- For EVERY flat-term K-flat P, clause 2 of `normalization` gives invertibility of the
  pulled K-flat counit and the precise representative equation for lambda: first the
  target counit and exact-pullback factorization and Q(chi), or first lambda then the
  source factorization and source counit. This identifies lambda with the balanced
  tensor/pullback comparison on representatives, on the entire unbounded category.
- `Edge.beta` is literally `mateEquiv h.dA h.dB` applied to lambda. The last clause of
  `normalization` is the defining counit transpose:
  pullback(beta) followed by the B-counit equals lambda followed by T(the A-counit).
  This is exactly the beta specified in the node, not an arrow asserted to exist.
- `Edge.kappaA` and `.kappaB` are conjugates under the ACTUAL canonical derived adjunctions
  of the dependency's normalized pullback compositor. That fixes their adjunction
  compatibility and the composite counit; no compositor is supplied as an assumption.
- In `derived_scalar_mate_composition`, clause 1 is, in Lean's left-to-right order,
  `beta_fg ≫ kappaB = T_S.map kappaA ≫ beta_f ≫ Rf_B.map beta_g` for every K.
  Its domains are the full derived categories, with no boundedness hypothesis.
- Clause 2 is `beta_id ≫ idDirectB = T.map idDirectA`. The identity coefficient maps
  are the inline helper `ringId`; the ordinary direct-image identities are uniquely
  fixed by section restriction along the inverse of `Over.pullbackId`. Identity
  pullbacks descend their geometric conjugates, and identity direct images are their
  derived conjugates. Therefore this says beta_id is the identity under exactly the
  canonical identity comparisons, without a choice of isomorphism in the conclusion.
- `commuting_square` has j,q,p,j' in their actual scheme directions. `comm` is equality
  of their composites with the coefficient inverse-image identifications included.
  This is the bundled version of jq=pj' after transporting the rings as specified in
  the node. Its equation takes each iterated beta path, precomposes T(kappaA) and
  postcomposes inverse kappaB, and equates them in the common composite endpoints;
  `eqToHom` accounts explicitly for the common-composite equality. This is precisely
  the node's equality under the normalized compositors. The square is arbitrary:
  neither Cartesian, proper, open nor flat is required.
- No beta is assumed invertible. All IsIso assertions concern the normalized pullback
  and scalar comparisons or the K-flat resolution counits. No finite, constructible,
  completion, nonzero-ring or nonempty-scheme condition occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent alias of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` (publicly imported).
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, and the existing
  `DerivedChangeOfRingsCochainModel` universal-pair presentation it normalizes.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: publicly exports the full
  arbitrary-ring-sheaf `proEtaleRingModules`, module pullback/direct image and the
  canonical `proEtaleRingDerivedAdjunction` from `ProEtaleOperationsCanonicalAdjunction`.
  We use those full general declarations, with no constant or finite specialization.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: `ScalarPullback.mate`,
  `kflat_scalar_comparison_normalization`, `θ_composition`, `θ_identity`.
  The proof plan transports the same comparison through the small model; the delivered
  normalization keeps the original pro-etale universes and the same actual operations.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons` (proof plan).
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateIsoEquiv`;
  these are the recorded mathlib_match of `def-weil-pbc-adjunction-mate`.
- Added the already-landed statement dependency
  `lem-weil-pbc-proetale-derived-pullback-composition`: its recorded module
  `Sheaf.Paper.IntegralFinitePullbackComposition` supplies the full, general
  `WeilConjectures.integralTowerGeneralPullbackComposition` alias. Its canonical
  compositor is constructed from the theorem's uniquely characterized existence;
  `Edge.kappaA` and `Edge.kappaB` therefore genuinely use this theorem dependency.
- The inline helper `restrict` uses `SheafOfModules.restrictScalars` directly.
  The inline helper `ringId` uses `conjugateIsoEquiv`, `Scheme.proEtaleSheafAdjunction`
  and `AlgebraicGeometry.ProEtale.lowerStarId`, imported from
  `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`.

Searches for an existing exact statement (all through the prescribed msearch wrapper,
plus read-only rg of the project and upstream sources):

1. LeanFinder: "Derived scalar extension counit mates for pulled back sheaves of rings
   respect geometric composition and identities". Eight results, including
   `SheafOfModules.pullbackComp`, pullback identity laws and pullback unit transposes;
   these are ordinary generic maps, not this normalized derived statement.
2. Loogle: "CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_hcomp".
   `CategoryTheory.mateEquiv_hcomp` is the one result. Read the mates source:
   horizontal pasting alone does not identify the actual K-flat scalar comparison.
3. Mathlib grep: "scalar.*mate.*comp|mateEquiv_hcomp". Seven hits in generic mates and
   bicategorical mates, no exact sheaf-derived scalar theorem.
4. LeanSearch: "Derived coefficient extension direct image counit mates respect
   geometric composition, identity and commuting square pasting". Eight results:
   exponentiable-morphism counit laws, Scheme.Modules pseudofunctor laws, and generic
   derived adjunction/mate facts. None contains the required representative normalization.
5. `rg -n 'derivedScalarMate|scalar.*mate.*comp|mate.*scalar.*comp'` in both
   `lean/WeilConjectures` and `lean/Sheaf`, and the item id in upstream. Found finite
   coefficient exchange constituents and other scalar comparison statements; no exact
   arbitrary-ring-sheaf geometric composition theorem or occurrence of the item upstream.
   Searches for scalarMateComposition/ScalarMateComposition likewise found no match.

Edge cases checked before writing: identity f or g reduces composition to the identity
normalization; arbitrary nonflat coefficient change (e.g. Z -> Z/2) is admitted because
all scalar extension is derived. Zero rings and the empty scheme are allowed; all maps
are then maps in the corresponding degenerate module categories and the uniquely fixed
identities remain defined. Complexes need not be bounded in either direction. A commuting
square is not required Cartesian and neither of its beta paths need be invertible.
The universe check explicitly retains the small site's distinct object and Hom sizes.

The proof docstrings carry the reviewed six-step argument: identify lambda using the
K-flat normalization; use the composite counit formula; transpose the iterated beta;
apply f-counit naturality, then both beta transpose equations, then lambda_g naturality;
identify the composite transpose and use injectivity; obtain identity and arbitrary
square pasting. Construction helper docstrings state their uniqueness or invertibility
arguments. These helpers are parts of the same specified canonical maps, not independent
new mathematical notions. There are no new DAG nodes or dependency-record repairs.

Validation: scompile.py compiled the full module in sandbox and library module modes
with no errors or unexpected warnings. The final delivery checks additionally validate
the explicit invertibility clause and recorded dependency alias.

The recorded composition module imports generic integral instances with max-universe
conclusions. The four exported `coefficientSiteSmall`, `coefficientAbSheafify`,
`coefficientRingSheafify`, `coefficientLocallyBijective` instances merely specialize
those existing witnesses to the original site and coefficient universe u+1. Their
bodies are the existing declarations at explicit universe arguments, with no new
construction or postponed proof. Their priority prevents unrelated integral universe
parameters from making class inference ambiguous. No site is resized by these aliases.

## Returned-delivery repair

The retained packet and the reviewer diagnostic for immutable returned head
791665c979bd were checked against the current live node. Before
repair the prescribed fresh dry run passed at 769e746c70a, but the saved packet still
contained exactly the returned H2 fault. The following substantive repair addresses it.

Removed the added `stmt_deps` entry
`lem-pur-proetale-inverse-image-tensor-comparison` and its direct module import.
Its tensor-comparison conclusion σ was never used. Inlined its two plain constructions
as `AlgebraicGeometry.DerivedScalarMate.restrict` (a transparent abbreviation of Mathlib
scalar restriction) and `.ringId` (the same conjugate of the canonical `lowerStarId`).
Both helpers have source/blueprint docstrings and are listed in `lean.declarations`.
All references now use those helpers. They contain real construction data, without
postponed proofs or an arbitrary comparison parameter. Their bodies are identical
constructions after unfolding the original aliases, so no mathematical claim changes.

Retained `lem-weil-pbc-proetale-derived-pullback-composition` in `stmt_deps`:
`Edge.kappaA` and `.kappaB` still use `integralTowerGeneralPullbackComposition`,
which chooses the uniquely normalized compositor supplied by that theorem.
The original scheme/site universes, arbitrary coefficient maps, normalized adjunctions,
K-flat representative clause, counit orientation, composition, identity and arbitrary
commuting-square clauses are unchanged. The advisory normalization clause 3 is still
the definitional equation identifying lambda's inverse with theta.

## Second reading by Q51

Self-check for this dispatcher-assigned repair (no other agents were started): read the
node and the repaired module together. The only signature changes replace the old
transparent restriction alias by the inline identical alias, and the old identity-ring
comparison by the identical conjugate construction. Schemes remain `Scheme.{u}`, site
objects have universe u+1 and morphisms u, and coefficients/modules have universe u+1.
No flatness, properness, boundedness or invertibility of beta was introduced. The
normalization theorem still includes the ordinary unit equation, every flat-term
K-flat representative, lambda inverse = theta, and beta's counit transpose. The main
theorem still states composition and identity with the same kappa maps; the final
theorem still states arbitrary commuting-square pasting. The retained compositor
statement dependency supplies actual chosen data, whereas the removed theorem's σ
occurs nowhere. All source definitions are imported directly or obtained from the
retained dependency modules. No node statement, proof plan or dependency record changes.

Repair validation: the prescribed `scompile.py` compiled the repaired module in sandbox
mode (29.4 s) and library-module mode (42.8 s), with no errors or unexpected warnings.
The recorded main signature is verbatim; both new helpers are in `lean.declarations`;
all source lines are at most 100 characters; no old helper namespace remains in the
module. Against the current main node the only changed fields are `lean` and the
addition of the genuinely used, already-landed pullback-composition statement dependency.
