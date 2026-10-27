## Worker report

This delivery states `WeilConjectures.ExplicitScalarCone.explicitScalarConeWordCoordinates`
and the representative-level clauses of the same node in
`Sheaf.Paper.ExplicitScalarConeWordCoordinates`. Every theorem has proof `sorry`;
the six helper definitions contain only the actual existing functor applications and
composites. No new mathematical notion, ring, tensor, reduction, or realization is chosen.
The natural-language statement and accepted proof are unchanged.

Source read: main-20261015, sec-poincare-duality/sk-lem-finite/
prop-weil-operations.proof.md, first sentence, and sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, first paragraph. These reference the pullback and
inverse automorphism squares; the detailed ten-step normalization argument is the
agent-extracted proof in this node. That argument is included step by step in the
main theorem docstring, with all named dependencies. This is not attributed verbatim
to the blueprint or to a Stacks tag.

Hypotheses and clauses, read against the node:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. E and L have `Field`, p-adic `Algebra` and
  `FiniteDimensional` structures. `ι : E →ₐ[ℚ_[l]] L` expresses the coefficient
  inclusion intrinsically, including identity inclusions. Field embeddings into a
  fixed algebraic closure introduce no further structure used in this identity.
  The valuation rings, uniformizers, quotients and same-index inclusions are the
  existing `Padic.coefficientExtension*` and `integralScalarQuotientSheafMap` data.
- `X Y : Scheme.{u}`, `g : X ⟶ Y`, `[IsIso g]`, and both residue-field
  `Invertible (l : ...)` instances state the scheme hypotheses. The small site is
  Mathlib `Scheme.ProEt` with `ProEt.topology`: its objects remain in u+1 and its
  morphisms in u. The coefficient/module universe is u+1, not a replacement site.
  A single arbitrary u accommodates both schemes and both coefficient fields as
  in the recorded intrinsic constructibility and specified-alpha interfaces; it
  does not identify site object and morphism universes.
- `DerivedCategory (integralTowerModules l E Y)` is the ambient completed-ring
  module-sheaf derived category. `hK : sfIntegralConstructible ... K` states
  derived completeness, constructible positive reductions, and their common
  finite cohomological interval. It imposes no Tor interval.
- `SEY`, `SEX`, `SLY`, `SLX : CoefficientDerivedSystemCalculus ...` give the
  whole strict quotient system categories, simultaneous reduction `reduction`,
  fixed realization `coefficientSequenceLimit`, and adjunction with its actual
  `adjunction.counit`. `IsNormalizedCoefficientSequence` is the same normalization
  as the finite derived tensor transition-adjoint isomorphism: its definition is
  the universal Hom-bijection criterion for exactly that transition. It is the
  normalized-system notion already used by the calculus dependency. The older
  `NormalizedDVRTower` record has an unrelated finite-field parameter; no second
  normalization predicate or substitute arbitrary system is introduced here.
- `pullbackSystem` is U_g,E C, `scalarSystem` is S_Y C, `sourceSystem` is A,
  and `targetSystem` is B, with C literally `SEY.reduction.obj K`. Their operations
  are `integralComparisonDerivedSequencePullback` and
  `integralComparisonDerivedSequenceScalar`, with all quotient transitions.
- `ρEX`, `ρLX`, `ρLY : IntegralComparisonRoosModel ...` retain the ordinary
  limit cone on K-injective resolutions. `UE`, `UL : IntegralComparisonPullbackModel`
  and `SX`, `SY : IntegralComparisonScalarModel` are arbitrary supplied normalized
  primitive models. Their `normalization` fields quantify over every simultaneous
  quotient presentation, fixing the actual tensor generators, scalar association,
  canonical universal scalar counits and zero-shifted-coordinate Roos comparison.
  No existence theorem is used to restrict the choice to one particular model.
- `_hC`, `_hU`, `_hS`, `_hA`, `_hB` each spell out the three prescribed assumptions
  at the corresponding system: normalization; constructible-complete realization;
  and invertibility of the actual counit. They are precisely the node's five
  effectivity assumptions, not flatness of a quotient coefficient map.
- `betaA` is the map of `UE.realization.hom.app K` under completed scalar change,
  then `SX.realization` at L(U C), then L(S_X(e_UC)). This is exactly the displayed
  `r_S,UC` and beta_A. `betaB` is completed pullback of `SY.realization`, followed
  by `UL.realization` at L(S C), followed by L(U_g,L(e_SC)). No intermediate counit
  is replaced by a reduction isomorphism.
- `explicitScalarConeSystemCoordinates` is the universal localization/counit
  equation for balanced association: Q of the actual ordinary entire-system
  comparison equals the prescribed kappa after the two fixed scalar counits.
  This is the precise meaning of kappa^D = kappa_C, not equality only after level
  evaluation. A simultaneous flat-term K-flat quotient presentation qualifies as
  its K-flat system input. All transitions are retained.
- `explicitScalarConeLevelCoordinates` binds any good P, any isomorphism
  `Q.obj P.obj ≅ K`, degree i, positive level n+1, and arbitrary local tensor
  generators p,a,b,s. It states for `scalarPullbackLevel` exactly
  `((g^-1(p tensor a)) tensor b) tensor s` mapping to
  `g^-1(p tensor iota(a)) tensor (iota(b) pi_L(s))`. The term
  `scalarPullbackGenerator` includes the finite scalar b; neither a nor b is
  silently specialized to one. Q is literally ordinary scalar extension of P.
- `explicitScalarConeBothCoordinates` uses the same `scalarPullbackTower` d_n,
  `scalarPullbackChain` delta_P and canonical `scalarRoosMap`. After the
  tensor/product comparison its unshifted projection is product(d_n) in degree i;
  its shifted projection is product(d_n) in degree i-1. Thus both coordinates,
  with the signed mapping-cocone convention, are explicitly included.
- `explicitScalarConeAugmentationCoordinates` states the exact quotient tuple
  on arbitrary pure tensors and zero for every shifted coordinate of
  `integralScalarCompletionChain`, the chi used in specified alpha.
- The main equality is `alpha.hom ≫ betaB = betaA ≫ L.map kappa.hom`, which is the
  node's beta_B composed with alpha equals L(kappa_C) composed with beta_A.
  Alpha is exactly `scalarPullbackCompleted`, with the completeness proof from
  `specifiedPullbackComparisonAlpha`. Its recorded definition conjugates the
  localized `scalarPullbackChain` by the two normalized chi maps; that dependency
  states its full representative formula for every P and resolution isomorphism.
  No arbitrary comparison map is substituted.
- `explicitScalarConeWordCoordinates_naturality` gives the square for arbitrary
  derived f between constructible-complete objects for the common expression
  beta_A followed by L(kappa). Together with the main equation at each endpoint
  this gives naturality of beta_B alpha. The main expression contains no P, while
  all three representative conclusions quantify over every P and e; this states
  independence under canonical resolution comparisons without choosing one P.

Dependency declarations used (the recorded owning modules were opened):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the existing completed coefficient
  sheaves and actual quotient projections retained by its public imports.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` reexports the recorded global
  `integralDerivedPullback`, its good-class model and Roos/tower operations.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and the defining representative comparison.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientSequenceLimit` and the actual
  whole-system reduction/adjunction interfaces, using
  `IsNormalizedCoefficientSequence` from `CoefficientRingedSequenceSite`.
- `Sheaf.Paper.NormalizedDVRTower`: `normalizedDVRRes` and canonical quotient
  restriction, used inside the existing normalized-sequence predicate.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`: derived sequence operations,
  ordinary `integralComparisonSequenceScalarPullback`, its derived
  `integralComparisonSystemScalarPullback`, scalar model and universal counits.
- `Sheaf.Paper.IntegralComparisonRealizationModels`: all three normalized model
  structures, their realization fields and fixed entire-system counit construction.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; the recorded
  `integralOperationsGoodComplex` is the flat-term K-flat resolving class.
- `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`:
  `specifiedPullbackComparisonAlpha`, its `scalarPullbackCompleted`, level/tower/
  chain maps and completion augmentation, retained from its public imports.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing sheaf tensor interface.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the recorded
  `Scheme.proEtaleSheafInverseImage`, coefficient structure maps and module
  pullback, underlying the existing finite pullback generators.
- `Sheaf.Paper.ScalarPullbackStrictConeNaturality`:
  `scalarPullbackGenerator`, which encodes the full two finite scalar generators.
  The new definition-only node `def-pod-scalar-pullback-generator` owns this
  existing helper because it occurs in the delivered signatures. The theorem
  node remains in proof_deps only.

All sixteen recorded proof-dependency modules are imported, publicly where their
interfaces occur in signatures and otherwise as proof imports. The existing helper receives a new definition-only node; there is no
dependency-module repair.

Edge cases checked: E=L with identity inclusion is admitted (balanced association
becomes multiplication); g=identity is admitted (unit inverse-image identifications);
K=0 and the empty scheme are admitted; n=0 is exponent one, so all positive levels
are covered without an artificial level-zero hypothesis. Ramified inclusions use the
same-index iota_n and no flatness, injectivity or Tor-amplitude premise. Arbitrary
shifts and unbounded K-flat representatives are allowed. The ambient formula is an
equality of derived morphisms, not merely equalities of separate finite evaluations.

Searches actually run through msearch.py, with results in searches.jsonl:

- LeanFinder: "Completed integral scalar extension and isomorphism pullback comparison
  in normalized quotient-system realization word coordinates" returned eight adic
  completion/module results, none about these module-sheaf words.
- Loogle: "Functor.map, Adjunction.counit" returned zero hits with diagnostic
  "unknown identifier 'Adjunction.counit'"; this was not counted as an exact-match
  exclusion by itself.
- Mathlib grep: "scalar.*[Ww]ord|[Ww]ord.*[Cc]oordinate|[Ss]calar.*[Cc]one" returned
  only an unrelated DFinsupp coordinate comment.
- LeanSearch: "Derived scalar pullback comparison normalized realization of quotient
  systems" returned vector-field pullback and unrelated scalar/module results.
- Direct rg of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the item id, scalar/word-coordinate concepts and the proposed names found
  no existing exact statement or name collision. Closest project statements are
  IsomorphismScalarComparisonAgreement (the parent cancellation), the strict
  cone-naturality and augmentation-cone nodes, and the primitive realization models;
  none states this beta_A/beta_B identification. All are reused rather than copied.

Validation: the primitive coordinate definitions and initial main equality passed
scompile.py. The explicit representative clauses were then added and compiled as
one module. One compiler failure was repaired by qualifying `Limits.Pi.map` rather
than the unrelated function `Pi.map`. The final module compiles cleanly through scompile.py (both sandbox and library
module modes), with no errors or warnings. The prescribed deliver2.py --no-push
dry run passed server preflight and per-file compilation: OK, commit b258b3632ce.
No source statement was corrected, no dependency was replaced, and no disputed
statement or unresolved node fault remains.


## New nodes

`def-pod-scalar-pullback-generator` records the existing plain definition
`WeilConjectures.scalarPullbackGenerator` in
`Sheaf.Paper.ScalarPullbackStrictConeNaturality` with `existing: true` and
`declarations` containing that definition. No module is added. It defines
`b • gamma_g(p tensor a)`, the local source generator in the item's displayed
finite-level formula. The source is the same extracted blueprint normalization
calculation, with the existing definition's Stacks 03D2/03EK attribution.
Its binders cover every scheme morphism g, every complex P, degree i and index n,
and arbitrary local sections p,a,b, exactly as the published definition does.
The coefficient sheaves and pullback/tensor notions are cited from their existing
nodes. There is no theorem choice or postponed proof in this definition.

Searches: LeanSearch for "Local inverse image tensor generator with a finite
quotient scalar for completed integral pullback" returned 8 ordinary tensor and
adic completion results; LeanFinder for "scalarPullbackGenerator local inverse
image tensor generator multiplied by a finite quotient scalar" returned 8
presentation and differential results; Mathlib grep for
`scalarPullbackGenerator|integralOperationsPullbackGenerator` returned zero hits.
The exact results are copied from searches.jsonl into the new node. Direct rg of
dag/nodes found only the theorem node's helper listing, with no definition owner;
rg of lean/Sheaf found the one existing definition; rg of lean/WeilConjectures and
dag/lean_names_upstream.json found no hit. `blueprint_refs.py search
scalarPullbackGenerator` returned zero matches; its ancestor command returned
`prop-weil-operations`. Thus this is ownership of an existing project definition,
not a duplicate mathematical construction.

## Returned delivery repair

The immutable return at 2b8fc6801169 identified H2: the theorem node
`lem-weil-scalar-pullback-strict-cone-naturality` had been added to stmt_deps only
to access a plain definition. Replaced that added statement dependency with
`def-pod-scalar-pullback-generator`, as the return explicitly requests. The theorem
remains unchanged in proof_deps. Added the three advised landed definition owners:
`def-coef-ringed-sequence-site` for `IsNormalizedCoefficientSequence` and
`coefficientSequenceLimit`, `def-coef-derived-system-calculus-data` for
`CoefficientDerivedSystemCalculus`, and `def-sf-additive-roos-map` for
`scalarRoosBoundary`/`scalarRoosMap`. Their recorded source signatures and docstrings
were read. No other existing node is edited. No mathematical statement or Lean
source is changed; the main node differs from current shared main only in lean and
stmt_deps. The first saved-packet dry run passed (7938f16d336), but did not detect
this semantic ownership issue, which is repaired here.

Self-check: the existing generator body is exactly finite-scalar multiplication
of the inverse-image generator of the quotient tensor section. Its signature
uses independent site and coefficient universes t and u, imposes no IsIso or
flatness hypothesis, and admits zero sections, the zero complex, empty test
objects, identity g and n=0 (exponent one). The delivered coordinate module is
byte-identical to the saved packet; the maintainer's soundness findings for its
five effectivity hypotheses, full generator formula, both Roos coordinates,
completion augmentation, and naturality continue to apply.


Repair validation: scompile.py rechecked the unchanged coordinate module against
the live published library on 2026-10-23: sandbox mode 35.9 s and library mode
30.0 s, both clean. A direct JSON comparison against current shared main confirms
that only lean and stmt_deps change on the main node, with proof_deps identical.
The new existing:true signature was checked verbatim against the published source.
All Lean lines are at most 100 characters, and autoImplicit is explicitly false.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
