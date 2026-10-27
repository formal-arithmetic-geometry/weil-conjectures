## Worker report

The module `Sheaf.Paper.SystemProjectionFormulaCoherence` states the strict-system
projection composition identity, joint naturality, its specified finite projection
normalization, and equality after the actual total derived inverse limit. All
proofs are `sorry`; all helper definitions contain real data. The natural-language
statement, proof, and proof dependencies are unchanged. There is no statement
dispute or source correction.

### Hypotheses and objects

- The finite-field datum is `D : FiniteFieldDatum.{u}` from
  `Sheaf.Paper.FiniteFieldFiber`. It retains the prime characteristic, finite field,
  and algebraic closure. `[Fact l.Prime]` and `hl : l ≠ D.p` render the coefficient
  prime hypotheses. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` render the finite coefficient extension. The
  valuation ring and fixed uniformizer are those already used by
  `Padic.coefficientExtensionRing`; they are not replaced by a new tower.
- `X Y Z : Scheme.{u}` have their named `Over (Spec (.of D.k))` structures,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` structure morphisms.
  The last two together mean finite type. The morphisms `f`, `g` have `IsOver`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. Explicit `include`
  directives retain every geometric hypothesis in the theorem declarations,
  including the hypotheses not needed just to type the equality.
- `IntegralSystemRealization.System l E W` is the existing
  `coefficientSequenceDerived l E W`, the derived category of strict semilinear
  module systems. Its coefficient ring sheaves are the constant positive
  quotients on `W.ProEt`. The site has object universe `u+1` and morphism
  universe `u`; no equality of these universes is imposed. Index `n : ℕ`
  denotes the node's positive exponent `n+1` throughout.
- The normalized full subcategory is exactly
  `FiniteAdjunctionDiagram.domain l E W`. Its first conjunct is
  `IsNormalizedCoefficientSequence`; its second is `∀ n, FiniteExceptional.domain`
  of the evaluated object. This is bounded constructible finite Tor amplitude
  separately at each level, with no common interval across levels. `_hM` and
  `_hN` supply these two membership assertions. Naturality uses the same
  membership for all four objects and arbitrary ambient morphisms `v`, `w`,
  as appropriate to a full subcategory.
- `o : Operations l E` and `z : Realizations l E D o` are the specified
  simultaneous geometric section models, with their actual units, counits,
  compositors, open tensor maps, and canonical semilinear bridge. This is the
  presentation package defined by `def-sf-integral-system-realization-data`,
  not an assumption of a new projection or composition map. Its interface is
  used as published; no realization existence theorem is used in these definitions.
- `cf`, `cg`, `cfg` are arbitrary compactifications of `f`, `g`, `f ≫ g`.
  `support` is literally open extension followed by proper direct image in
  those models. This presents the specified finite-adjunction realization:
  its `SystemRealization.supportIso` identifies its restricted functor with
  this same ambient compactification word. No independent functor is supplied.

### Clauses and canonical maps

- `projection` is the existing `compactificationProjection`, literally the
  proper counit-defined projection mate, then the open tensor comparison,
  then the canonical pullback composition cast. There is no arbitrary map
  parameter and no selection from finite evaluations.
- `refinement` is the actual intrinsic proper/open mate with the direct-image
  compositor and equality casts. `change` uses the two projections from the
  upstream canonical graph common refinement `Compactification.inf`.
  `triangleWord` is the proper/open compatible-triangle word, including the
  open and direct-image compositors. `compositor` transports that word through
  the canonical `Compactification.Triangle.ofHasCompactification` and the
  three graph refinements. Thus it is the geometric compact-support compositor
  formed in the same models, not an isomorphism chosen from its existence.
  The item-local `inverseOnDomain` explicitly uses `inv` when `IsIso` holds
  and zero otherwise; its value off that domain adds no invertibility hypothesis.
  The theorem asserts `IsIso (compositor ... M)` on the node's domain.
- `projection_natural` gives joint naturality in both variables, with the
  tensor of the support-image of `v` and `w` on one side, and support applied
  to the tensor of `v` and pullback of `w` on the other.
- `leftMap` is `PF_g`, then `F_g(PF_f)`, then the compositor at
  `M ⊗ f* g* N`, then support applied to the inverse of the canonical
  pullback compositor. `rightMap` is the tensor of the compositor at `M`
  with the identity of `N`, then `PF_(f≫g)`. Their inferred source is
  `F_g(F_f M) ⊗ N` and their common target is `F_(f≫g)(M ⊗ (f≫g)*N)`.
  The first equality conjunct of `system_projection_formula_coherence`
  asserts their equality in the actual derived category of strict systems.
- The finite projection is fixed independently of evaluation by
  `finiteProperProjection` (the existing finite adjunction counit transpose),
  `finiteOpenTensorInv` (the existing finite open unit transpose), and
  `finiteProjection` (their compactification composite). The finite tensor
  factor is `canonicalFinitePullbackTensor`, with its recorded K-flat
  representative normalization. `finitePullComp` is the existing ordinary
  pullback compositor descended to derived categories. `residueInvertible`
  constructs the required prime unit by transport from the fixed base field;
  it adds no extra hypothesis.
- `projection_evaluation` explicitly identifies evaluation of the system
  projection with `finiteProjection`, using the existing support evaluation,
  evaluation tensor, and inverse-image evaluation comparisons at both ends.
  The compositor is the geometric proper/open word using `z.properOpen`
  (whose `adjunct` and `canonical` fields fix that mate), so evaluation uses
  the same finite geometric compositor. The `∀ n` conjunct of the main theorem
  states the finite evaluated composition equalities. Together with
  `projection_evaluation` these are the specified finite projection words,
  rather than arbitrary equal images with unnormalized projection factors.
- `coefficientSequenceLimit l E Z` is the existing total derived inverse limit
  after termwise scalar restriction to the completed ring
  `R_Z = lim B_(n,Z)`. The final conjunct is equality of this functor's images
  of the two actual system arrows. The equality is asserted before applying
  evaluation or inverse limit; evaluation is not assumed faithful.

### Dependency declarations

The original statement dependencies were read in their node records and source
signatures/docstrings. Their interfaces used here are:

- `Sheaf.Paper.NormalizedDVRTower`: `WeilConjectures.NormalizedDVRTower`,
  with its normalized-system specialization retained by the published domain.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its
  counit/open-tensor projection construction, specialized by
  `IntegralSystemRealization.compactificationProjection`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, for the completed
  ring already used in the reconstruction calculus.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleEtale`, and the existing pro-etale
  finite-Tor predicate used by `FiniteExceptional.domain`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology` (Mathlib match).
- Scheme-morphism-properties is a convention node with no declaration; the
  actual Mathlib classes listed above render its content.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`,
  `coefficientSequenceDerivedEvaluation`, and `coefficientSequenceLimit`.
- `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`:
  `WeilConjectures.FiniteAdjunctionDiagram.finiteAdjunctionDiagramRealization`,
  `FiniteAdjunctionDiagram.domain`, and `SystemRealization.supportIso`.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, the
  simultaneous semilinear operations and adjunction normalization.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition`, the finite geometric
  compositor realized by the same compatible-triangle/refinement word.

The definition owners explicitly cited by the repaired packet are:

- `def-sf-integral-system-operations`: `Operations`, `Compositors`, `pull`,
  `finiteAdj`, and `finiteOpenAdj` in
  `Sheaf.SixFunctors.IntegralSystemOperations`.
- `def-sf-integral-system-canonical-bridge`: `CanonicalBridge` in
  `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`.
- `def-sf-integral-system-realization-data`: `Realizations`, `ProperOpenCoherence`,
  `compactificationProjection`, and `supportEvaluation` in
  `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`.
- `def-pur-finite-pullback-tensor-comparison`: `canonicalFinitePullbackTensor`;
  `def-pur-completed-pullback-tensor-comparison`:
  `pullbackTensorDerivedEvaluation` and the canonical system tensor comparison.
- `def-coef-ringed-sequence-site`: `coefficientSequenceDerivedEvaluation` and
  `coefficientSequenceLimit` in `Sheaf.Paper.CoefficientRingedSequenceSite`.
- `def-coef-finite-adjunction-system-data`: `FiniteAdjunctionDiagram.domain`
  in `Sheaf.SixFunctors.FiniteAdjunctionSystemData`.
- `def-weil-derived-pullback-tensor-hom`: `finiteDerivedPullback` and
  `finiteIntrinsicDerivedTensor` in `Sheaf.Paper.DerivedPullbackTensorHom`.
- `def-weil-extension-by-zero`: `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`
  in `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `def-weil-ambient-exceptional-adjoint`:
  `AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate` in
  `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`.
- `def-sp-finite-intrinsic-open-square`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullbackComp` in
  `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`.
- `def-sf-semilinear-proper-open-comparisons`:
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId` in
  `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.

These are existing definition nodes, not new mathematical prerequisites. The two
previously added theorem citations `lem-sf-integral-compactification-system-realization`
and `lem-coef-finite-free-extension` are removed. The original base dependencies
are retained. The latter theorem's module is no longer directly imported.

The available proof-dependency modules are imported without `public` where
not already statement imports. The three new stage-1 obligations for
proper/open invertibility, compatible-compositor normalization, and compositor
refinement square have no Lean records yet; they are proof obligations, not
missing objects needed to type this statement. Their exact roles and all seven
DAG proof steps are retained in the main theorem's proof docstring. No downstream
finite-free compact-composition module is imported: that node cites this item.

### Edge cases and verification

Checked the statement and definitions on identity maps and compactifications,
identity refinements, empty schemes/open pieces, zero objects, and the first
positive coefficient level (`n=0` here means exponent one). No nonemptiness of
a scheme or nonzero-object condition is introduced. Pullback equality casts
retain identity and arbitrary compactification cases. The normalized domain
retains quotient transitions and allows nonuniform bounds at different levels;
no flatness of a quotient ring map is assumed. Finite-type geometric hypotheses
are explicit even where the ambient maps exist more generally.

Every universe and variable is explicitly declared with `autoImplicit false`.
The module compiles cleanly through `scompile.py`, both under its sandbox name
and its actual library module name. An ambiguous inherited general
`IntegralHom.derivedCategory` instance was disabled for instance search so that
the unchanged intrinsic finite coefficient category uses its existing standard
localization; this does not alter the site, coefficient size, or mathematics.
No definition contains `sorry`; the three named theorems have source and complete
natural-language proof docstrings.

### Searches

The actual remote search outputs are saved in the sandbox's `searches.jsonl`.

- `msearch.py` leanfinder: "coherent projection formula maps on strict coefficient
  systems before derived inverse limit" returned eight unrelated inverse-system
  or LightProfinite projection identities, no matching geometric statement.
- Loogle: "CategoryTheory.mateEquiv, CategoryTheory.Functor.map_comp" returned zero.
- Mathlib grep: "projectionFormula|projection_formula|ProjectionFormula|mateEquiv_hcomp"
  in CategoryTheory returned seven occurrences in generic adjunction/bicategory
  mate modules, no strict-system compact-support result.
- LeanSearch: "projection formula composition coherence for compact support
  derived coefficient systems" returned eight unrelated group-cohomology,
  Cech-nerve, continuous-map, gluing, and cochain declarations.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed item-id grep
  upstream, found no theorem stating this node. Existing system mate/projection
  helpers and finite compact-support results were read and reused. The only
  finite-free compact-composition reference to this item is downstream, so it
  was excluded from the import path.

## New nodes

None. The added declarations are component words and normalizations belonging
to this node's own specified projection and compositor, not independent notions.

## Dependency modules

None. All recorded dependency declarations are used as published.

## Repair of returned head c7a37ee323a3

The initial saved-packet dry run passed (f8a766dc94b), but the independent return's
H2 finding was still present. This repair changes the actual Lean source and node
record rather than re-pushing that packet. Every requested owner is listed above.

`inverseOnDomain` is now defined in this item's module, with explicit universes,
`HasZeroMorphisms`, real `if IsIso then inv else 0` data, a source/blueprint
docstring, and its own entry in `lean.declarations`. Both graph-refinement
transport and finite open tensor inversion use it. This is a component of the
item's specified word, as explicitly requested in the return, not an independent
new notion or a theorem assumption.

`residueInvertible` no longer uses the uncited theorem
`PurCompactSupport.coefficientPrimeUnit`. It constructs characteristic `D.p` on
`D.k₀` from the recorded cardinality using Mathlib's
`charP_of_card_eq_prime_pow`, transports it to `D.k` using
`charP_of_injective_algebraMap'`, and uses
`CharP.cast_ne_zero_of_ne_of_prime` and `isUnit_iff_ne_zero` before transporting
along the actual residue evaluation. These are proof terms in the real
`Invertible` construction, not new postponed theorems. The distinct-prime edge
case is precisely `hl.symm`; no extra characteristic assumption is introduced.

## Second reading by Q70

This is the dispatcher's requested self-check; no additional agent was started.
The maintainer's independent reading already accepted the mathematics. I reread
the node and every declaration in this file after the repair: finite-field,
coefficient-extension, all scheme and morphism hypotheses, normalized levelwise
finite-Tor domains, arbitrary compactifications, joint naturality, canonical
finite projection evaluation, the compositor's invertibility, the displayed
system equation, all finite evaluations, and total inverse limit remain exactly
as documented above. The main theorem's signature is unchanged and is verbatim
in `lean.statement`. Only construction-level inverse and unit proof terms and
definition-owner citations changed. No statement correction, dependency-interface
replacement, new node, or new `sorry` was introduced. The base node's proof,
proof dependencies, source, and natural-language statement remain unchanged.
