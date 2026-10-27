## Worker report

The module `Sheaf.Paper.CompactificationBProjectionReduction` states
`AlgebraicGeometry.ProEtale.CompactificationBProjection.compactification_b_projection_reduction`.
Its sole postponed theorem has a full eight-step proof docstring. All helper definitions
have real data and source/blueprint docstrings. No mathematical statement is corrected.

The statement is in the ordinary derived category of the vertical coefficient sequence
site. `CompleteProjectionDescent.derivedTowerEquivalence` is the published exact
strict-system equivalence, so this retains every quotient transition and all derived
morphisms, including morphisms invisible to separate evaluations. Index n means ell^(n+1).

Hypotheses and clauses, in statement order:

- The implicit parameters `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the prime and arbitrary finite
  coefficient extension. There is no unramifiedness restriction.
- `D : FiniteFieldDatum`, `_hl : l ≠ D.p`, and `X Y : Over (Spec (.of D.k))`
  give precisely the algebraic closure of a finite field and its characteristic.
  The locally-finite-type, quasi-compact and separated structure morphism instances
  give separated finite-type k-schemes. `f : X ⟶ Y` is a k-morphism;
  `[SmoothOfRelativeDimension d f.left]`, `[IsSeparated f.left]`, `d : ℕ`
  give smooth separated pure relative dimension d >= 0. `c` is the fixed compactification.
- `m : CompleteProjectionDescent.DescentModels l E` presents the published operations,
  not arbitrary maps: its tensor and pullback comparison fields retain quotient/K-flat
  normalizations, and its open scalar map has the actual adjunction-unit normalization.
  `AX`, `AZ`, `AY : SpNormalizedEquivalence ...` are the normalized reconstruction
  presentations on X, the compactification and Y. Their unit and counit belong to the
  actual reduction/limit adjunction. They add presentation data, not a geometric condition.
- K and M are objects of `finiteTorConstructibleIntegralCategory`, whose underlying
  predicate is derived completeness and bounded constructibility together with a single
  finite Tor interval for all reductions. The cohomological interval is also uniform.
- `CompleteProjectionDescent.rings`, `transitions`, `red` and `lim` are the actual
  ell-power quotient rings, quotient maps, derived scalar reduction and total derived
  limit after scalar restriction. These are the R_W, B_n, r_W and L_W in the node.
- `integralImage c` is the separately derived open/proper composite. The canonical
  `compactificationLimit`, followed after reduction by the actual counit, is exactly
  `reconstruction c ... N`. This is the pinned b_N, not an existential isomorphism.
  The source's canonical limit comparison identifies this presentation with P.
- `completedInner f K M` is literally
  `integralCompletedTensor (integralDerivedPullback f K, M)`, hence D_(K,M).
  `completedSource c K M` is literally the completed tensor of K and P M.
- The existential isomorphisms h and v have their forward maps fixed by `innerUnit`
  and `sourceUnit`. The latter is the published tensor chi; the former composes chi
  with the published pullback unit tensored with identity. Thus these introduce the
  actual ordinary/complete coordinate identifications, not choices of alpha or b.
- `q` first reduces h inverse, then uses `m.tensor` and `m.pull` with the tensor
  bifunctor. `s` first reduces v inverse, then uses `m.tensor` and identity tensor
  the actual `reconstruction M`. These are the canonical simultaneous quotient
  comparisons q and (identity tensor b_M) tau with their full system normalization.
- `ordinaryAlpha` is exactly `ringedCompactificationProjection`, composed with the
  source and target canonical Koszul symmetries. `alpha` transports it by the two
  fixed comparison units. `systemAlpha` performs the same two swaps around
  `systemProjection`. `hOpen` asserts invertibility of the specified open unit mate;
  this is a conclusion, not an extra hypothesis on M or K.
- The finite-Tor membership clauses cover D, K completed-tensor P M, P M and P D.
  `normalized` transports `spNormalizedConstructibleTorTowers` through the exact
  strict-system/sequence-site equivalence. The explicit clauses cover r_X M,
  r_Y K, r_X D, r_Y(K completed-tensor P M), F r_X D, r_Y P M, r_Y P D,
  f_bullet^* r_Y K tensor r_X M, r_Y K tensor F r_X M and its F image.
  The b, q and s clauses assert the canonical maps are isomorphisms. Membership
  for their remaining isomorphic endpoints follows from those identifications.
- The first equation is, in Lean composition order,
  `redY.map alpha ≫ reconstruction D ≫ F.map q = s ≫ systemAlpha`.
  This is the node's first displayed compatibility equality with no evaluation.
- For arbitrary proofs that alpha and systemAlpha are invertible, the next equation
  is `redY.map (inv alpha) ≫ s = reconstruction D ≫ F.map q ≫ inv systemAlpha`.
  It preserves the conditional nature of the inverse assertion.
- The last clause quantifies K', M', their canonical h', v', and arbitrary morphisms
  a, b, and states naturality of the completed alpha. The other factors are already
  natural transformations in the published interfaces; the h/v formulas uniquely
  determine their coordinate identifications. Hence the whole square is natural.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`;
  its finite-field base convention is `FiniteFieldDatum` (imported by that module).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  scheme properties are the existing Mathlib `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated` classes. The scheme-morphism-property node is a convention record.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`, with
  its actual open i, proper g and commutativity equation.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the completed coefficient sheaf.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers` and
  `SpCoefficientTowersAbelian`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`;
  `Sheaf.Paper.FiniteTorAmplitudeSites` and its recorded integral counterpart
  `finiteTorConstructibleIntegral`, `finiteTorConstructibleIntegralCategory`.
- `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `SpNormalizedEquivalence`;
  its normalized domain is `spNormalizedConstructibleTorTowers`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`;
  the published completed functors are `integralDerivedPullback` and
  `integralCompletedTensor`, with their canonical representative comparisons.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the counit-defined projection
  convention `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`;
  its concrete ordinary implementation is `ringedCompactificationProjection`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  the finite-level derived pullback/tensor interfaces represented simultaneously
  by `VaryingRing.G` and the closed tensor of `SemilinearSections.Data`.
- `Sheaf.Paper.CompleteProjectionMateDescent`: `DescentModels`, `red`, `lim`, `adj`,
  `integralImage`, `systemImage`, `compactificationLimit`, `reconstruction`,
  `systemOpenInverse`, `systemProjection`. This is the already-landed entire-system
  version of the reconstruction/direct-image/gluing notions in the statement.
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`: `ShiftedTensorModel`,
  `shiftedTensorResolving`, `derivedTensorSymmetry`. The two symmetry presentations
  restrict the existing tensor representative comparisons; they choose no tensor.

The two theorem modules supply published definitions. The H2 repair below gives
those definitions their own DAG owners and cites the other four existing definition
owners requested by the return. No Lean declaration is duplicated or replaced. The three older modules IntegralReconstructionComparisons,
IntegralDirectImageTower and SmoothPurityTowerGluing are not directly imported:
the concrete whole-system interfaces above give the notions used, with the actual
limit/counit normalization. Directly importing those unused theorem modules reaches
an unrelated broken proper-closed-heart proof (an expanded coefficient-admissibility
interface). Narrowing imports avoided that failure without changing any source,
notion, comparison normalization or dependency node.

Searches performed (the search wrapper records the full replies):

- leanfinder: "Integral compactification projection commutes with whole-system
  reduction under the specified reconstruction counit". Eight irrelevant hits,
  mainly Profinite Nobeling/locally constant constructions; no match.
- loogle: "CategoryTheory.Adjunction.homEquiv, CategoryTheory.MonoidalCategory".
  Eight generic adjunction/lax-monoidal/currying hits; no compactification result.
- Mathlib grep: "projection.*(reduction|tower)|reduction.*projection", CategoryTheory.
  No matches.
- rg in both project Lean trees for the item id and projection/reduction/tower
  terms found the general `complete_projection_mate_descent`, not this pinned,
  completed coefficient-first compatibility square. Read its full signature and
  definitions before using it; the present node supplies its constructibility
  hypotheses and states the completed swapped-coordinate consequence.

Edge cases checked mathematically: identity f and trivial compactification;
proper-only and open-only factors; d = 0; zero M or K; shifted inputs and the
Koszul sign on the two tensor swaps; ramification e > 1 (ell^n = unit times
varpi^(en), retaining the cofinal ell-power convention); empty schemes. No added
nonemptiness, unramifiedness, faithfulness of level evaluation, or monoidality of
inverse limit is used. No statement dispute was found.

Validation: scompile.py compiled the final module twice (sandbox elaboration and
library module elaboration), cleanly with no warnings. All variables/universes are
explicitly bound and autoImplicit is false. No local or global library build was run.


## Repair of returned immutable head d57e733e0f90

H2 is repaired by definition ownership, not by re-pushing the returned metadata.
The returned sandbox signature matches its recorded Lean statement. Current main
has no attachment or module for this item; its remaining node fields are retained.
The only Lean source changes are four explicit public imports of the existing
owners listed below. The complete theorem signature and every mathematical
construction are unchanged from the reviewed delivery.

1. Removed `lem-sp-complete-projection-mate-descent` and
   `lem-pur-shifted-tensor-morphism-calculus` from the item's stmt_deps. These are
   theorem nodes, and the statement uses their module definitions. The former
   remains an existing proof dependency; the two theorems are not used as owners.
2. Added `def-pur-compactification-reduction-models`, an existing:true definition
   node owning the normalized model and canonical comparison/projection definitions
   in `Sheaf.Paper.CompleteProjectionMateDescent`. Its main declaration is
   `AlgebraicGeometry.ProEtale.CompleteProjectionDescent.DescentModels`. The listed
   declarations include the exact `red`, `lim`, `adj`, `integralImage`, `systemImage`,
   `compactificationLimit`, `reconstruction`, `systemOpenInverse` and
   `systemProjection` used by the item, together with their ordinary-unit and
   adjunction-mate normalization definitions. This records existing data; it adds
   no existence or invertibility assertion.
3. Added `def-pur-ringed-site-signed-tensor-models`, an existing:true definition
   node owning `ShiftedTensorModel`, `shiftedTensorResolving` and
   `derivedTensorSymmetry` in `Sheaf.Paper.ShiftedTensorMorphismCalculus`, with the
   ordinary module/derived categories, total tensor and signed representative
   predicates they use. Its main declaration is `SheafOfModules.ShiftedTensorModel`.
   The actual symmetry is the published unique signed representative construction.
4. Added all four uncited owners named by L:
   `def-sp-projection-reduction-presentation` for rings/transitions/System/Integral
   and derivedTowerEquivalence;
   `def-pur-integral-ringed-projection-maps` for ringedCompactificationProjection;
   `def-sf-integral-system-canonical-bridge` for ringedPull and its ordinary models;
   `sk-def-sp-normalized-towers` for spNormalizedConstructibleTorTowers.
   Their modules now also occur as explicit public imports.

## New nodes

Both new nodes are in sec-poincare-duality, unit sk-lem-finite, with the item's
blueprint ancestor prop-weil-operations and the inherited via path prefixed by
this item. Each has import_flags [], full source metadata and three kinds of
search records. Definition ownership scans of all DAG lean.module records found
no prior definition owner for either module. blueprint_refs.py name searches for
DescentModels and ShiftedTensorModel found no blueprint matches; broader searches
found related theorem nodes and a scheme-specific signed shift, a different notion.
LeanSearch, LeanFinder, Mathlib grep and both project-tree searches were run; the
queries and actual returned names are stored in each new node's mathlib_searches.
All definitions are existing:true re-exports, so no new module is required.

The original edge-case checks continue to apply unchanged. New-definition checks:
the model node asserts no existence or projection invertibility; it pins all
comparison maps by ordinary unit sections and actual derived mates. The symmetry
node uses flat-term K-flat complexes and the (-1)^(pq) signed summand formula,
with independent site object and morphism universes. Zero complexes and shifts
introduce no additional assumptions. No statement correction or dispute is needed.

Repair validation: scompile.py compiled the module with the four explicit owner
imports cleanly in both sandbox and library mode. The theorem signature remains
verbatim equal to lean.statement from the returned delivery. The delivery dry run
also checks all existing:true declaration re-exports on the live server.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
