## Worker report

The module `Sheaf.Paper.AdicNormalizedFibreScalar` states
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_scalar` with
one sorry. `NormalizedScalar` packages exactly the scalar part of the normalized
comparison assertion. Its structure fields are data/propositions, not axioms or
postponed constructions. No proof is supplied and no node statement is changed.

Hypotheses and clauses, in node order:

- The base field is `{k : Type u} [Field k]`; the prime is `(l : ℕ)
  [Fact l.Prime]`; invertibility is `[Fact (IsUnit (l : k))]`.
  Every scheme is the existing `FiniteTypeBase k` (separated, finite type over k),
  with the existing `base l X` giving the noetherianity, finite dimension and
  stalkwise invertibility consequences. All maps `g : Y.scheme ⟶ X.scheme`
  between those schemes are allowed; no flatness or smoothness is imposed.
- Finite coefficient fields are the universally quantified `A B : Type u`,
  `[Field A] [Field B]`, `[Algebra ℚ_[l] A] [Algebra ℚ_[l] B]`, with both
  `FiniteDimensional` instances, and an actual inclusion `i : A →ₐ[ℚ_[l]] B`.
  Quantifying fields and embeddings rather than their presentations as subfields
  of a chosen algebraic closure is invariant under field isomorphism and adds
  no mathematical case. The fixed algebraic closure and pair category are ambient
  context, not further input to this finite-stage assertion.
- The integer rings, uniformizers, quotient coefficient rings and continuous
  completed/rational sheaves are the recorded `Padic.coefficientExtension*`,
  `integralCoefficientSheaf`, `rationalCoefficientSheaf`, and the actual
  coefficient maps in `R.fieldChange`. There is no replacement coefficient sheaf.
- `R : ContinuousRational.Family l` is the existing coherent realization family.
  `NormalizedFibre.Heart l A (base l X)` is exactly the localized standard heart
  of the raw completed constructible category. `heartScalar l A B i X` is the
  literal restriction of `pbcRationalScalarExtension`; `heartPull` is the actual
  completed rational pullback. The statement does not substitute an arbitrary
  scalar functor or a derived category of discrete coefficients.
- `ω : Fibres l R` consists of the dependency's exact finite-dimensional point
  functors, normalized by inverse-limit lattice fibres and its `fractions`
  equation. `α : NormalizedPullback l R ω` is the SAME family's normalized
  pullback comparison, including its quotient and germ normalization, identity
  and scheme-composition equations. The theorem chooses these together with beta,
  so no unrelated alpha can enter the mixed square.
- `NormalizedScalar.scalar` is a natural isomorphism
  `heartScalar ⋙ ω_B ≅ ω_A ⋙ ModuleCat.extendScalars i.toRingHom`, in precisely
  beta's direction. Mathlib puts the scalar on the left of a balanced tensor;
  the node's right tensor order is canonically the same module.
- `local_normalization` quantifies EVERY source chart C, adaptedness proof hA,
  lattice N and rational presentation φ. It gives the scalar adaptedness hB,
  lattice M and presentation ψ on the same chart; `IsScalarChartMap` pins its
  restriction comparison q to `R.fieldChange`, `scalarModelMap`, the actual
  derived counit and tensor units. The equation for ψ pins it to q, scalar φ
  and η. Thus ψ cannot absorb an arbitrary scalar or hide normalization.
- `τ n : finiteScalarLevel ... (N.system.obj (op n)) n ≅ M.system.obj (op n)`
  is the scalar reduction tower with exponent n+1. This is the cofinal source
  presentation of the node's minimal exponent ceil((n+1)/e): the source transition
  from exponent n+1 to that exponent becomes an isomorphism after tensoring with
  D/v^(n+1), since the smaller source uniformizer power already acts by zero.
  The identification preserves the tensor unit, so it describes the same
  normalized tower, not a different scalar operation. This is the same convention
  already used by the combined comparison's `finiteScalarLevel`.
- `IsScalarLattice` fixes the integral section map δ by every finite reduction
  cone and fixes its rationalization on integral tensor sections. This states
  that the integral lattice of the actual realized scalar object is the ordinary
  finite-free scalar tensor, with no unspecified rational isomorphism.
- The natural diagram isomorphism `e : scalarQuotients ... ≅ M.system ⋙ stalk`
  identifies every scalar stalk with the quotient of D tensor_A lim N_n.
  That quotient is canonically M tensor_A D/v^(n+1). Its displayed equation
  sends b tensor a germ to the germ of b tensor the section. No flatness of a
  finite quotient coefficient map is assumed. As a natural diagram isomorphism,
  e commutes with all quotient projections.
- The integral isomorphism `a : extendScalars(integerInclusion).obj
  (N.fiber ...) ≅ M.fiber ...` satisfies
  `a.hom ≫ limMap e.inv = scalarCompletionMap ...`. The right hand side is the
  EXISTING actual reduction-cone map, not a chosen completion isomorphism. Since
  a and e are isomorphisms this says that actual map is an isomorphism, with
  target the limit of the quotients. Its inverse and rationalization are fixed.
- The last pure-tensor equation of `local_normalization` specifies beta inverse:
  b tensor (a0 tensor n) maps to (b * i a0) times (1 tensor a(1 tensor n)).
  Both sides are thereby the canonical L tensor_A M. This explicitly identifies
  beta with the localized inverse completion map and balanced associator.
- `unit_normalization` holds for every degree-zero derived presentation and
  every pro-etale section germ; its e' equals the ACTUAL `scalarModelMap` and its
  inverse-beta formula is b times the scalar tensor germ. This also controls
  arbitrary presentation changes, not just selected lattice coordinates.
- `scalar_id` uses `pbcRationalScalarUnit` and `ModuleCat.extendScalarsId`;
  `scalar_comp` uses `pbcRationalScalarCompComponent` and
  `ModuleCat.extendScalarsComp`; their underlying maps are fixed by HEq to the
  actual raw comparisons. They are the specified balanced tensor associators.
- `mixed` uses `R.mixed` on its underlying heart isomorphism and the SAME α.pull
  at A and B. Its displayed composite equation is exactly the mixed square.
  Quotient compatibility is in the diagram e, reduction-cone equations and the
  α normalization. Limit maps are actual `limMap`; rationalization is actual
  `extendScalars`. Hence their equations persist through these operations.
- Naturality on ALL heart morphisms is part of `scalar` being a natural iso,
  including every fractional lattice arrow. The existing ω.fractions identifies
  those arrows with inverse uniformizer powers of inverse-limit maps. Universal
  quantification of source charts/presentations plus the intrinsic unit equation
  gives independence of lattice, chart, stratification and fractional representative
  by conjugation on a common refinement.

Dependency declarations read and used (including public transitive interfaces):

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, weakly-etale small site.
- `Sheaf.Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`;
  `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`;
  `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`, the heart used here.
- `Sheaf.Paper.IntrinsicQbarCategory`: `WeilConjectures.intrinsicPbcQbarCategory`
  is the ambient pair category, no common-stage assertion is added.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension`,
  `pbcRationalScalarExtension`, `pbcRationalScalarUnit`, `pbcRationalScalarCompComponent`.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `ContinuousRational.continuous_rational_derived_realization`, `Family`, `At`.
- `Sheaf.Paper.AdicNormalizedFibreExactness`: `adic_normalized_fibre_exactness`;
  its public data module supplies `Assertions`, `Lattice`, `Chart`, `Heart`, `rationalFiber`.
- `Sheaf.Paper.AdicNormalizedFibrePullback`: `NormalizedPullback`,
  `adic_normalized_fibre_pullback`; its shared data/coherence modules supply
  `Fibres`, `heartScalar`, `heartPull`, `presentedFibre`, `germ`, `scalarModelMap`.
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`: `etale_stalk_tensor_unique`,
  `etale_stalk_scalar_unique` for arbitrary ring maps and normalized germ formulas.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the original coefficient definitions.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower` and its actual
  completed coefficient and compatible finite quotient projections.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: `AdicIntegralDiagramOfUniverses`,
  `LisseIntegralSheafOfUniverses`, `adicIntegralFiberOfUniverses`, publicly importing
  the ramification-ceiling scalar construction in `LisseAdicSheaves`.
- `Sheaf.Paper.LisseCompletedSystemComparison`: `CompletedLisse.completed_system_comparison`.
- Proof-only imports also include `Ideal.adic_tower_reconstruction`,
  `Padic.extension_integers_dvr`, `spectralNorm.completeSpace`, realization scalar
  coherence, and the inverse-image germ theorem, as prescribed by the proof plan.

Existing auxiliary definitions are reused, never duplicated:
`scalarQuotients`, `scalarCompletionMap`, `finiteScalarLevel`, `finiteScalarUnit`,
`IsScalarChartMap` and `IsScalarLattice` are all already owned by
`lem-per-adic-normalized-fibre-comparisons` in
`Sheaf.Paper.PerAdicNormalizedFibreComparisons`. That module is imported for its
DEFINITIONS ONLY. The new theorem does not use `normalizedFibreComparisons` as a
premise, so its intended proof remains the seven node steps. Import-cycle exception:
the maintainer must OMIT the future proof import of this scalar module into
`PerAdicNormalizedFibreComparisons` (stages/2-statements.md §3.7). Adding that
reverse import would close a cycle. This is a pre-existing placement of real
construction data together with their downstream theorem, not a prerequisite wait.
No shared source was edited, and no duplicate definition node was introduced.

Edge cases checked before writing: zero lattices/rank zero satisfy the same finite-free
completion and pure-tensor formulas; empty schemes introduce no geometric-point witness;
empty strata are allowed by the existing chart/stratification types. The identity
coefficient extension is explicitly covered. Arbitrarily ramified extensions are covered,
including e>1 and repetitions of the ceiling index. Non-flat finite quotient ring maps
are allowed. No tensor/limit exchange for arbitrary modules is asserted: the limit
normalization applies only to the prescribed finite-free chart lattices. Universes are
the dependency's scheme/finite-field universe u and module universe u+1; the algebraic
closure's size is irrelevant to this finite-stage result. Scheme maps need not be k-linear,
as in the recorded pullback interface.

Searches actually made:

- msearch LeanFinder: “Normalized geometric fibres of completed lisse adic sheaves
  commute coherently with finite ramified coefficient scalar extension”: eight hits,
  normalization-of-schemes lemmas and `AdicCompletion.tensor_map_id_left_eq_map`,
  none the stated theorem.
- msearch Loogle: `TensorProduct.assoc, ModuleCat.extendScalars`: zero hits.
- msearch Mathlib grep: `normalized.*[Ff]ibre.*[Ss]calar|[Ss]calar.*normalized.*[Ff]ibre`:
  zero hits.
- msearch LeanSearch: “Geometric fibres of completed lisse adic sheaves commute
  with finite ramified coefficient field extensions”: eight hits on completion and
  condensed colimits, no normalized adic scalar theorem.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the above conceptual regex and
  `lem-per-adic-normalized-fibre-scalar`: only the pullback module's descriptive text.
  Subsequent concept search located the combined theorem's existing helpers, reused
  here. Name search `adic_normalized_fibre_scalar|NormalizedScalar` also checked
  `dag/lean_names_upstream.json`; no conflicting declaration.
- Read BS 6.8.4(1),(4), 6.8.15 directly from the local PDF (pdftotext); read the
  current blueprint smooth-pullback proof. The node's finite-free calculation is
  agent-written as recorded, consistent with this source. No statement dispute.

## Second reading by Q62

Self-review with the node and generated module reopened; no independent agent was
started, as the dispatcher's explicit instruction prohibits that. The maintainer's
independent review is still required. The first compiler pass found that the new
scalar family has two explicit field parameters that the old packaged comparisons
had already applied; all calls now supply A B. The copied local algebra binder was
replaced by explicit tensor ring-hom notation, so no let-bound proposition appears.

Checked the full clauses again: no rank or common-stage descent fields were imported
into the new assertion; alpha belongs to the same omega and the mixed comparison
is the actual R.mixed; raw scalar unit/composition are fixed; both lattice and chart
presentations are pinned by tensor-unit and derived-counit equations; the finite
stalk comparison is natural as a diagram; the integral iso equals the actual reduction
cone after the prescribed inverse limit; beta inverse is its localized balancing
formula for every presentation. The n+1 cofinal indexing is mathematically the
same ramified quotient tower as the node's ceiling indexing, with matching units.
The structure is a package of this theorem's clauses, not a private copy of any
coefficient, stalk, lattice, realization or pullback notion. The downstream import
exception is listed explicitly above. No node field outside lean was changed.

Validation: scompile.py passed sandbox compilation in 27.1 s and library-module
compilation in 20.6 s, with no diagnostics. deliver2.py --no-push passed the
server preflight and compilation (dry-run commit ebbf1110c89).
