## Worker report

This repairs the return on immutable head 9e310850b83b (H3, H8 and H11).
The saved packet was first checked with deliver2.py --no-push: it passed the
mechanical checks, producing dry-run commit 400e6c1ad1. Its mathematics still
had the returned defects, so it was not pushed. The arbitrary comparison datum
has now been removed completely. The item statement, source, proof and proof
dependencies are unchanged. The only additions to stmt_deps are three already
recorded nodes whose published interfaces this module uses.

The module is Sheaf.Paper.ExceptionalCoefficientComparison. Its main declaration
is AlgebraicGeometry.Etale.exceptional_coefficient_comparison. The namespace
ExceptionalCoefficients contains helpers for the very canonical maps and
identifications specified in this node, all listed in lean.declarations.
Definitions have actual data. Theorems have sorry proofs and source/proof
plan docstrings; no definition contains sorry. No independent new notion or
replacement definition of the derived category, scalar extension, coefficient
ring, constructibility or Tor amplitude is introduced.

Hypothesis-by-hypothesis rendering:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The integers r, m and d are natural
  numbers; `hmr : m ≤ r` and `hm : 1 ≤ m` give r ≥ m ≥ 1 and d ≥ 0.
- A_r and A_m are the existing `FiniteReduction.Coeff.{u} l r` and
  `FiniteReduction.Coeff.{u} l m`. These are the published double ULifts of
  `ZMod (l ^ r)` and `ZMod (l ^ m)`, with their transported ring structures.
  `FiniteReduction.quotient l hmr` is their actual quotient ring homomorphism.
  The lifts accommodate the ModuleCat-valued small-etale universe convention;
  they add no mathematical hypothesis.
- X and Y are `Scheme.{u}` with `[IsNoetherian X] [IsNoetherian Y]`.
- The given morphism f has `[SmoothOfRelativeDimension d f]`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]` and `[QuasiCompact f]`. The latter two express
  finite type. `[HasCompactification f]` is the existing compactifiability
  predicate; all constructions use its chosen genuine compactification.
- `hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)` says ell is
  invertible on Y. Its pullback is invertible on X, so explicitly repeating
  the X condition would be redundant. No assumption of flatness of a quotient
  ring map is made.
- `DerivedCategoryModule A T` is the existing ordinary-etale derived category
  of `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)`.
  `DerivedCategory.boundedConstructibleFiniteTor A T K` uses the existing
  bounded-constructible and finite-Tor predicates. The latter tests derived
  tensor against every degree-zero module sheaf, with one finite interval;
  it is not a test on constructible sheaves alone.
- `rightDerivedLowerShriek`, `rightDerivedUpperShriek` and
  `rightDerivedUpperShriekAdjunction` are the actual P_A, G_A and ambient
  adjunction, and likewise over B. `dualizingComplex` is G_A of the unit.
- S_T is the published `scalarExtension (FiniteReduction.quotient l hmr) T`,
  the chosen left adjoint to exact derived scalar restriction. The published
  representative-normalized `scalarTensorIso` identifies its restriction
  with tensor by B over A. It is not a variable functor in this theorem.
- `hb : ExceptionalCoefficients.CompactSupportCocycle l f` is exactly the
  hypothesis about b for all consecutive positive quotient levels. It
  quantifies over r, m, n, both inequalities and bounded constructible
  finite-Tor M, with the actual two quotient associators displayed.

The canonical maps, rather than arbitrary arrows:

- `pullbackMap` is the inverse mate of the existing exact
  `scalarRestrictionPullbackIso`. Its isomorphism theorem computes this mate
  by ordinary balancing on K-flat representatives. `pullbackIso` is asIso
  of that map.
- `properMap` uses `derivedUpperStarLowerStarAdjunction` over B: it transposes
  the inverse scalar/pullback comparison followed by S of the A proper
  counit. This fixes precisely the proper coefficient comparison in the node.
- `openIso` comes from uniqueness of left adjoints applied to the exact
  restriction/pullback comparison and the open lower-shriek adjunctions.
  Its ordinary normalization is identity/balancing on the open and zero
  outside, as explained in its docstring.
- `compactSupportMap` is the proper comparison at the open extension of M,
  followed by proper direct image of `openIso`. Thus b has the specified
  open/proper factorization. `compactSupportMap_isIso` states its
  invertibility on bounded constructible finite-Tor inputs under the node's
  actual quotient-ring and geometric hypotheses.
- `comparisonInverse` is the inverse of that actual b whenever it is an
  isomorphism, and is extended by zero elsewhere solely to give a total
  term before proving the domain result. The main theorem explicitly proves
  b is an isomorphism at G_A K. Consequently the fallback is never used by
  any of its conclusions, including the unit used in tensor compatibility.
- `mateMap` is the B exceptional adjunction homEquiv applied to this inverse
  b followed by scalar extension of the A exceptional counit. Thus c is
  defined by the required counit transpose, rather than supplied as data.
- `tensorIso` is uniquely normalized by ordinary scalar balancing and the
  published `scalarExtensionRepresentative`. `TensorNormalizationAux`
  displays the equation on pairs of cochain complexes using localization
  tensorators. `siteTensorIso_existsUnique` uses HEq to identify this SAME
  natural isomorphism with its site-specific tensor-functor presentation;
  it introduces no new freedom. The opaque transport avoids expanding the
  entire derived monoidal structure during kernel checking.
- `unitIso` is similarly uniquely fixed by the localization unit and the
  ordinary multiplication B tensor_A A -> B. These choices are from uniquely
  specified universal/normalization properties, not from mere existence.
- `quotientAssociator` is `ProEtale.pbcFixedScalarExtensionComp` for the actual
  three quotient ring maps, with the composite ring hom equality supplied.
  Its normalization is the published scalar-adjunction normalization.

Clause-by-clause conclusion (six conjuncts):

1. For every bounded constructible finite-Tor K on Y, G_A K satisfies the
   same predicate on X. This is the previously missing domain-preservation
   conclusion. It makes b at G_A K available.
2. For every such K, `IsIso (compactSupportMap ... (G_A.obj K))`, and the
   displayed equality `P_B.map (mateMap ... K) ≫ epsilon_B =
   comparisonInverse ... (G_A.obj K) ≫ S_Y.map epsilon_A`.
   On this explicitly asserted domain comparisonInverse is b inverse, so
   this is precisely the node's defining counit equation.
3. Naturality is quantified over K, K', their two domain proofs and every
   h : K ⟶ K'. Its two sides are S_X(G_A h) followed by c_K', and c_K
   followed by G_B(S_Y h).
4. The quotient clause explicitly introduces a third level n, `hnm : n ≤ m`
   and `1 ≤ n`. It equates S_mn(c_rm) followed by c_mn and G_n of the
   Y-associator with the X-associator followed by c_rn. It therefore compares
   the actual direct and two-step c's under BOTH canonical associators.
5. `TensorCompatibility` equates S_X(phi_A,K) followed by c_K with
   `tensorDomainMap` followed by phi_B,S(K). The domain map is the actual
   scalar tensorator followed by scalar/pullback balancing, then tensor
   with c at A_Y and G_B of the normalized unit identification. Both phi's
   are the recorded `smoothTensorDualityMap`, with the existing finite-ring
   projection formula, rather than unspecified tensor arrows.
6. For every Noetherian Y' and every g : Y' ⟶ Y,
   `BaseChangeCompatibility` writes both composites on `pullback f g` using
   the actual projections. They go from S_X' g'^* G_A K to G'_B g^* S_Y K.
   One path is S(beta_A), c_f', then G'_B of scalar/pullback balancing;
   the other is balancing, g'^*(c_f), then beta_B. Each beta is the recorded
   `smoothExceptionalBaseChangeMap`. The existing base-change instance
   supplies compactifiability of f'; finite type over Noetherian Y' supplies
   Noetherian X'. An arbitrary Cartesian presentation is canonically
   isomorphic to this chosen pullback, so no Cartesian square is excluded.

No conclusion or hypothesis assumes c is invertible. The full ten-step
natural-language proof is in the main theorem docstring, including the Tor
interval shift [a-2d,b-2d], finite-affine constructibility descent, the explicit
counit-transpose quotient computation, projection/tensor compatibility, and
proper/open mixed base change followed by the beta/c counit computation.
Each postponed helper has its own proof plan and source; all are components
of the maps and identifications already specified in this DAG statement.

Dependency declarations used (full names are prefixed with AlgebraicGeometry
and, for functors, Etale unless otherwise stated):

- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `SmoothOfRelativeDimension`;
  Mathlib.AlgebraicGeometry.Noetherian: `IsNoetherian`;
  Mathlib morphism files: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- Sheaf.AlgebraicGeometry.CompactifiableOverField reexports
  WeilConjectures.Compactification.Defs: `Compactification`,
  `HasCompactification`. Its additional existence theorem over a field is
  not imposed on this arbitrary Noetherian-base statement.
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  `DerivedCategoryModule`, `constantComplex`,
  `DerivedCategory.boundedConstructibleFiniteTor`. The recorded
  WeilConjectures.AlgebraicGeometry.DerivedCategories source was read via
  scompile.py --source; the imported smooth interfaces already reexport the
  same categories through the older Sheaf module, so importing both duplicate
  declarations is avoided.
- Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  WeilConjectures.SixFunctors.Etale.Derived.UpperShriek:
  `rightDerivedUpperShriek`, `rightDerivedUpperShriekAdjunction`.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`;
  Derived.OpenImmersionLowerShriek:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`.
- Sheaf.AlgebraicGeometry.SmoothTensorDuality:
  `smoothTensorDualityMap`, `isIso_projectionMap_of_finite`;
  Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange:
  `smoothExceptionalBaseChangeMap`.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor: `derivedTensor`;
  Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf:
  `Scheme.IsConstructibleEtaleModuleSheaf` (through existing domain predicates).
- Sheaf.Paper.EtaleDerivedScalarTensor: `scalarExtension`,
  `scalarExtensionRepresentative`, `scalarTensorIso`;
  Sheaf.Paper.WitnessCompatibility: `ProEtale.pbcFixedScalarExtensionComp`;
  WeilConjectures.SixFunctors.ProEtale.ScalarExtension:
  `ProEtale.etaleSheafExtendScalars` and its adjunction.
- Sheaf.Paper.FiniteReductionConstructibility:
  `FiniteReduction.Coeff`, `quotient`, `ringFinite` and the bounded-flat-model
  reduction statement used in the proof plan.
- Sheaf.Paper.EtaleUnboundedRestrictionComparison:
  `scalarRestrictionPullbackIso`, reexporting the recorded bounded-below
  interface. Its newly published exact ambient comparison is reused directly.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the general canonical K-flat tensor/pullback comparison behind the specified
  constant-coefficient normalization. It is publicly imported, not replaced
  by an unconstrained isomorphism hypothesis.
- Mathlib.CategoryTheory.Adjunction.Mates: `mateEquiv`, `conjugateIsoEquiv`;
  Mathlib's actual localization tensorators and the upstream
  `Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans` and unit map render
  the representative normalization equations.

Searches (no exact existing theorem):

- Saved packet searches: LeanSearch on right-adjoint scalar-extension mates;
  LeanFinder on exceptional coefficient/counit comparisons; Loogle
  `CategoryTheory.Adjunction, "mate"`; Mathlib grep
  `mate.*tensor|tensor.*mate|counit.*projection`. The hits are generic module
  scalar adjunctions, categorical mates and rigid-category lemmas.
- Repair searches: msearch.py leanfinder on canonical extension of scalars,
  compact support, etale exceptional inverse image and the counit; eight
  generic ModuleCat/cotangent hits, no ordinary-etale combined statement.
  Loogle `CategoryTheory.Adjunction, conjugateEquiv` returned no match;
  grep `restrictScalars.*[Dd]erived|[Dd]erived.*restrictScalars` returned none.
- rg in both the upstream WeilConjectures tree and shared lean/Sheaf for
  coefficientComparison, exceptionalCoefficientComparison, scalarExtension,
  derivedRestrictScalars, scalar tensor and pullback comparisons found the
  published scalar interfaces and canonical smooth phi/beta above. Further
  inspection of the current recorded restriction dependency found the new
  unbounded comparison; a draft local duplicate was removed in its favor.
- grep for the item id in upstream sources found no exact existing theorem;
  DAG searches distinguish the pro-etale finite-coefficient comparison nodes
  from this ordinary-etale statement. No new independent definition node
  was needed.

Edge cases checked by reading the actual equations and endpoints: r=m gives
identity quotient coefficients (the canonical identity scalar equivalence,
not a literal equality of chosen adjoints); n=m and n=1 are included in the
three-level equation; d=0 has no artificial positive dimension condition;
K=0 and the empty X are allowed; g=id and arbitrary non-flat g are allowed
in the Cartesian clause. The non-flat coefficient quotient Z/ell^2 -> Z/ell
is included, since all scalar functors are derived and no coefficient
flatness is assumed. No source statement correction or disputed statement
is needed.

Validation: the full module compiled cleanly with scompile.py (exit 0).
The repaired packet passed deliver2.py --no-push at a992177952. A final
self-check then narrowed the b-isomorphism helper from general finite rings
to the exact quotient rings and geometric hypotheses of this node, avoiding
an unnecessary generalization; the final packet is recompiled and preflighted
after that adjustment.

## Second reading by Q71

Author self-check, not an independent second worker: the dispatcher explicitly
prohibits starting agents and states that the maintainer supplies independent
review. The prior certification of the arbitrary-datum packet was incorrect
and is superseded by the following concrete checks.

H3: I reread the node with the repaired source open. There is no arbitrary
scalar or exceptional functor parameter and no unrelated quotient/tensor/base
change arrows. I traced properMap to the actual proper counit, openIso to the
actual restriction square and open adjunctions, compactSupportMap to those two
parts, and mateMap to the actual exceptional homEquiv. I checked the first
conjunct is G_A-domain preservation, the second asserts b_G_AK invertible,
the quotient equation binds n with both associators, and the base-change
equation contains both actual pullback projections and both canonical beta's.
The tensor equation uses the two recorded phi's and the normalized scalar,
pullback and unit arrows.

H8: I checked every declaration has a source and blueprint docstring, each
postponed helper has a full proof route, and the main docstring covers all ten
DAG proof steps. The normalization existence statements determine their data
uniquely; definitions do not contain postponed data.

H11: The hypothesis/clause correspondence above describes the current source,
not the removed arbitrary datum. In particular I checked the arithmetic,
Noetherian and invertibility binders, the actual CTF domain, the three-level
cocycle and the Cartesian endpoints separately. Independent mathematical
certification remains the maintainer's review of this delivery.

## Maintainer review fix (H4)

Independent maintainer review of immutable head c1df27a3bf6a. The module's
`pullbackMap`, `pullbackMap_isIso`, `pullbackIso` and `properMap` were second
definitions of the recorded `AlgebraicGeometry.Etale.scalarPullbackIso` and
`AlgebraicGeometry.Etale.scalarMate`. Those are declarations of
lem-pur-etale-scalar-mate-projection in `Sheaf.Paper.PurEtaleScalarMateProjection`,
which landed before this delivery. They are on the same categories: the
K-flat-normalized canonical tensor/pullback identification, and the transpose of
the scalar-extended proper counit under the B inverse-image/direct-image
adjunction. The fix removes the four private declarations and imports that
module. `compactSupportMap` now uses `(scalarMate φ c.g).app` at the open
extension, and `tensorDomainMap` and `BaseChangeCompatibility` use
`(scalarPullbackIso φ _).inv.app`. The paragraphs of the worker report above
that describe `pullbackMap`/`pullbackIso`/`properMap` are superseded by this
section. The main statement, its record statement and all other helpers are
unchanged. The fixed module compiles cleanly with nt_compile.py.
