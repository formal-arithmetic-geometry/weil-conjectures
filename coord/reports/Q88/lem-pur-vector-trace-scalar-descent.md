## Worker report

The module Sheaf.Paper.VectorTraceScalarDescent states the entire node as one theorem,
AlgebraicGeometry.Etale.VectorTraceScalar.vectorTraceScalarDescent, with proof `sorry`.
Its helper definitions are actual composites of published maps. The natural-language
statement, dependencies and proof plan are unchanged. No statement correction is needed.

Hypothesis and clause correspondence:

- `N : ℕ`, `hN : 0 < N` express N ≥ 1. The independently bound coefficient types
  `A B : Type (u + 1)`, `[CommRing A] [CommRing B] [Finite A] [Finite B]` are the
  finite commutative rings called A and A' in the node. `φ : A →+* B` is unital;
  `hA : (N : A) = 0` and `hB : (N : B) = 0` say N kills both rings.
- `S : Scheme.{u}`, `[IsNoetherian S]`, `hS : IsUnit (N : Γ(S, ⊤))` are the base B
  of the node, Noetherian with N invertible. The coefficient ring B in Lean is A'
  of the node; the scheme S is B of the node.
- `r : ℕ`, `F : SheafOfModules.{u} S.ringCatSheaf`, `[F.IsFiniteLocallyFreeOfRank r]`
  render the constant-rank bundle. Its total space and projection are precisely
  `VectorBundleZeroSection.scheme S r F` and `VectorBundleZeroSection.π S r F`.
  The already recorded integration construction establishes its affine and finite-type
  properties; these are not extra assumptions.
- `DerivedCategoryModule A T` is the full ordinary small-etale derived category.
  `scalarExtension φ T` is the recorded everywhere-defined derived tensor with B.
  No flatness or Tor-bound assumption occurs.
- `balancing` selects the unique ordinary balancing family from
  `finite_tate_scalar_source_normalization`. `line` is its actual
  `finiteTateScalarLineMap` at degree one. `unit` is the published
  `purityScalarUnitMap`, so it is multiplication with the specified single/unit maps.
- `base` forms the prescribed tensor powers of shifted balanced lines, starting with
  `unit` at zero. This is l_{T,d} in the ordered shifted-line presentation
  `affineLinearBaseCoefficient` already used by vector integration. `pullBase`
  transports it by the published scalar/pullback comparison. No new Tate objects,
  arbitrary orientation, root or scalar map is introduced.
- The projective map `projective` is `scalarMate` followed by proper pushforward of
  `line`. The proper comparison is precisely the actual counit transpose of the
  recorded proper scalar theorem. The normalized decomposition and Kummer component
  are those of `projectiveLineTraceDatum`, and the trace is `projectiveLineTrace`.
  `sum` is d_B, with projections Q(pr_1) followed by l and Q(pr_2) followed by u.
- Conjunct 1 is Q(h_A) followed by tilde q = u followed by h_A'.
  Conjunct 2 is Q(b_A) followed by tilde q = d_B followed by b_A'.
  Conjunct 3 is tilde q followed by t_p,A' = Q(t_p,A) followed by u.
  Lean's left-to-right `≫` reverses the node's written composition order.
- Conjunct 4 quantifies `∀ d : ℕ`, including zero. `affineTrace` is the actual
  ordered-coordinate adjunction counit transported by `affineLinearCompactComparison`.
  `affineCoefficient` uses the existing coefficient descent into inverse image of the
  ordered base tensor, the actual normalized scalar/pullback comparison, and the
  inverse coefficient descent. `affine` uses `compactScalarChosenMap` and pushes this
  coefficient map forward. Thus its equation has exactly the prescribed
  compactification scalar comparison, rather than an unspecified isomorphism.
- Conjunct 5 is the required global integration equation. `vector` uses the actual
  `compactScalarChosenMap` on `VectorBundleZeroSection.π S r F` and pushes `pullBase`
  forward. Its source and target are the existing `vectorIntegrationSource`s;
  `vectorBundleIntegration` is the recorded glued map at each coefficient ring.
  The compactification is the same canonical chosen compactification as that source.
  Open-restriction and proper-refinement comparisons are retained by using the
  published scalar map itself; they are not replaced by a freely chosen arrow.

Dependency declarations used:

- Sheaf.AlgebraicGeometry.VectorBundleZeroSection:
  `AlgebraicGeometry.VectorBundleZeroSection.scheme`, `.π` (via integration).
- WeilConjectures.AlgebraicGeometry.DerivedCategories:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the ordinary derived category.
- Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings publicly retains
  DerivedChangeOfRingsCochainModel; the etale specialization is the existing
  `AlgebraicGeometry.Etale.scalarExtension`.
- Sheaf.Paper.EtaleCompactScalarCoherence:
  `compactScalarMap`, `compactScalarChosenMap`, `etaleCompactScalarCoherence` and
  its published composition, restriction and refinement laws.
- Sheaf.Paper.FiniteTateScalarSourceNormalization:
  `WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization`,
  `finiteTateScalarLineMap`, `purityScalarUnitMap` from its public dependency.
- Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction:
  `exists_ordinaryFiniteP1Adjunction`, with `OrdinaryFiniteP1Datum` and its `.chern`
  and `.decomposition` fields, as used by the canonical trace datum.
- Sheaf.AlgebraicGeometry.ProjectiveLineTrace:
  `projectiveLineTraceTransport`, `projectiveLineTraceDatum`, `projectiveLineTrace`.
- Sheaf.AlgebraicGeometry.AffineSpaceTopTrace and its public construction modules:
  `affineTraceCounit`, `affineTraceProjection`, `affineTraceRight`,
  `affineLinearCoefficientDescent`, `affineLinearBaseCoefficient`,
  `affineLinearCompactComparison`.
- Sheaf.AlgebraicGeometry.VectorBundleIntegration:
  `vectorIntegrationCoefficient`, `vectorIntegrationSource`, `vectorIntegration_geometry`,
  `vectorBundleIntegration`. The coefficient is already expressed as inverse image
  of the ordered shifted Tate tensor; it is used verbatim.

All recorded proof-dependency modules are imported, with plain imports for those
needed only by the proof. The theorem docstring gives all eleven node-proof steps,
combining the projection and boundedness steps into the corresponding induction and
then the exact degree-zero descent argument. No general derived Hom descent is used.

Edge cases checked before writing: rank and affine dimension zero use the identity
adjunction and multiplication; the empty base is permitted by every binder; N=1
permits the zero rings; no Nontrivial or nonempty assumption is present. The nonflat
map Z/4 → Z/2 satisfies the hypotheses at N=4 on a base where 2 is invertible:
all scalar maps here are derived, and the flatness used to compute Tate inputs is
flatness of the line over its own ring, not of the coefficient homomorphism.
For φ=id, the maps are the normalized identity comparisons. The recursive coefficient
map retains the ordered tensor structure at dimension two and introduces no sign
from odd shifts.

Searches for existing statements (2026-10-22):

- msearch.py leanfinder, query “derived scalar extension compatibility of vector bundle
  integration trace via Kummer projective line and affine coordinate tower”: eight hits
  on algebraic field traces, no etale integration theorem.
- msearch.py loogle, query “AlgebraicGeometry.Etale.vectorBundleIntegration,
  AlgebraicGeometry.Etale.projectiveLineTrace”: zero hits, unknown project identifier.
- msearch.py grep, query “vectorBundleIntegration|projectiveLineTrace|affineTraceCounit”
  in Mathlib/CategoryTheory: zero hits.
- msearch.py leansearch, query “derived scalar extension vector bundle integration trace
  Kummer projective line”: eight unrelated field-trace hits, no match.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for vector/scalar,
  scalar/trace and the exact item id. The item id has no declaration. Existing
  categorical perfect-complex trace scalar laws concern a different trace.
  ReductionExceptional has shifted-line and tower scalar helpers, but it concerns the
  downstream chart reduction interface; the present maps instead reuse the item's
  normalized finite-Tate dependency and the already specified coefficient descent.
  P1SplittingScalar has the prime-power splitting case, not the arbitrary-N bundle
  theorem. P1CounitScalar is an adjunction-counit compatibility interface, not this
  global integration equation. None states this node.

No STATEMENT-DISPUTED flag or node fault is identified.

## Second reading by Q88

No separate worker was started: the dispatch expressly forbids sub-agents and requires
self-delivery, with the maintainer performing the independent review. A self-check
against the node found and repaired a missing application of Q to the first Kummer
component in the initial draft. All five equations now have the same derived sources
and targets as the node. The coefficient/base name difference is documented above.
The helper maps were checked against the actual definitions of integration and affine
coefficient descent; no unconstrained map was substituted.

Validation: the module-mode import probe accepted the exact current normalization
signature. A full diagnostic compile of the final declarations succeeded in 33.8 seconds
in sandbox mode and 31.6 seconds in library mode. Its only warning was the deliberately
added profiler setting in the diagnostic copy; that setting is absent from the delivery.
The typed `balancing` helper isolates the unique ordinary witness and avoids repeatedly
expanding the large normalization proposition while elaborating the shifted line map.

Final delivery-file compile: clean in sandbox mode (43.4 seconds) and actual module
mode (44.9 seconds), without errors or warnings. No profiling option is delivered.
