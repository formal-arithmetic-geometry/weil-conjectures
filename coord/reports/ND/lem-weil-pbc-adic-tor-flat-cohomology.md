## Worker report

The module `Sheaf.Paper.AdicTorFlatCohomology` states exactly the three-condition
cohomology-flatness equivalence and its final reduction clause. Both theorem proofs
are `sorry`. The two supporting definitions have complete data: the canonical
cohomology reduction arrow, and the predicate expressing flatness on every supplied
system of common local models. They are helpers of this node, not restatements of
other DAG nodes. The node changes only in `lean`; there is no statement correction,
new node, dependency module, or mathematical dispute.

### Hypotheses and clauses

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. `pbcPadicCoefficientDatum l E` uses the
  recorded actual valuation ring `Padic.coefficientExtensionIntegers l E` and
  chosen uniformizer, not an unrelated ring or an additional coefficient datum.
- The scheme is `(T : Scheme.{u})`. The finite affine Noetherian cover is
  `[IsNoetherian T]`: Mathlib's `IsNoetherian` is locally Noetherian and compact;
  `isNoetherian_iff_of_finite_affine_openCover` identifies it with the node's
  description. Finite dimension is `_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n`.
  Local invertibility is `_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`.
  Thus no assumption on nonempty schemes, strata or covering members is added.
- Membership is `K : PbcBoundedConstructibleComplete T
  (pbcPadicCoefficientDatum l E)`. This is the published full subcategory of the
  actual completed-coefficient derived category. Its property includes derived
  completeness, a uniformly bounded constructible canonical reduction tower, and
  existence of compatible etale-origin witnesses. The specialization reuses the
  recorded `IntegralUniformCoefficient` datum without adding a scalar action.
- The completed ring is `pbcAdicCompletion T d`; the quotient ring at Lean index
  `n` is `(pbcAdicRings T d).obj (op n)`. Lean index zero denotes mathematical
  exponent one, so every positive quotient occurs and exponent zero is excluded.
  `pbcReductionAdicTower T d K.obj` is the published canonical normalized tower;
  its level is `(pbcCompletedReduction T d n).obj K.obj`.
- Clause (a) is `∀ m : ℤ, PbcLevelwiseTorVanishing T d
  (pbcReductionAdicTower T d K.obj) m`. The dependency predicate quantifies over
  `n : ℕ`, `q : ℤ` with `m + 1 ≤ q`, and `p : ℕ` with `0 < p`. It applies
  `pbcDerivedExtend` for the consecutive quotient map to `H^q(K_(n+1))[0]` and
  requires `IsZero` of degree `-(p : ℤ)` cohomology. Universally quantifying the
  cutoff covers every integer q (choose m = q - 1); conversely all-degree Tor
  vanishing implies every cutoff condition. Hence this is exactly the node's
  all-cutoff higher-Tor condition, not termwise flatness of a representative.
- Clause (b) is `∀ q : ℤ, SheafOfModules.IsFlatOnSite
  (J := ProEt.topology T) (R := pbcAdicCompletion T d)
  ((DerivedCategory.homologyFunctor _ q).obj K.obj)`. The imported predicate
  means exactness of the sheafified tensor functor, precisely the node's flatness.
- Clause (c) is `PbcSuppliedModelCohomologyFlat T d K.obj`. This definition
  universally quantifies the common bounds `d₀ ≤ d₁`, the recorded finite
  `LocallyClosedStratification T`, a covering sieve on each stratum, and an
  entire dependent family of `AdicTowerLocalModel` objects on those covers.
  It then tests every integer cohomology degree of every supplied model complex
  for `IsFlatOnSite`. The ring is exactly
  `(adicTowerInverseImage (U.hom ≫ S.immersion α)).obj
  (pbcAdicCompletion T d)`, the restricted completed sheaf. The fields of the
  recorded local-model structure retain bounded terms, adic lissity, finite-lisse
  cohomology of every reduction, coefficient-linear reduction identifications,
  and their normalization compatibility. None is replaced by arbitrary maps.
- `pbc_adic_tor_flat_cohomology` concludes `(a ↔ b) ∧ (b ↔ c)`, which gives
  precisely all three equivalences. It imposes no flatness premise.
- The final clause is `pbc_adic_flat_cohomology_reduction`, under clause (b),
  available from any of the equivalent conditions by the preceding theorem.
  It states for every quotient index n and degree q that
  `IsIso (pbcCohomologyScalarExtension T (pbcAdicProjection T d n) K.obj q)`
  and that the reduced cohomology is `IsFlatOnSite` over the quotient ring.
  The source of this arrow is `(pbcExtend φ).obj (H^q(K))`, the recorded
  ordinary sheaf tensor/scalar extension; its target is `H^q(Lφ*(K))`.
  The arrow is constructed by applying cohomology to the derived adjunction
  unit, following the exact-restriction cohomology comparison, and taking the
  ordinary scalar-extension adjunct. The tensor-unit normalization of the
  imported adjunctions fixes the cocycle map z ↦ z tensor 1. Thus its
  invertibility specifies the canonical reduction identification, not merely
  existence of an isomorphism between the two objects.

### Dependency declarations and sources read

Read the node, all seven statement-dependency statements and records, the stage-2
brief and stage document, delivery-errors section H, the compact-object example,
and the blueprint `sec-smooth-base-change/sk-rem-rest/
thm-weil-pbc-integral-truncations.md`, statement hypothesis paragraph and proof.
The module and theorem docstrings carry the source and all eleven proof steps.
The clause theorem's docstring details steps 3 and 4 which prove that clause.

The statement imports and uses these recorded interfaces:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition`. Read their
  signatures and construction docstrings in `CoefficientExtension` as well.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, the actual coefficient limit and normalized scalar
  extensions. This is reused through the published pbc tower interface.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcPadicCoefficientDatum`,
  `pbcPadicCoefficientFacts`, and `pbcBoundedConstructibleComplete`; the latter
  abbreviates `PbcBoundedConstructibleComplete` from the imported
  `Sheaf.Paper.BoundedConstructibleComplete`. The statement uses that same
  underlying full subcategory so local-ring invertibility is written literally.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcModules`, `pbcExtend`,
  `pbcDerivedExtend`, `pbcRestrict`, `pbcScalarAdjunction`,
  `pbcDerivedScalarAdjunction`, `pbcAdicCompletion`, `pbcAdicRings`,
  `pbcAdicProjection`, `adicTowerInverseImage`, `AdicTowerLocalModel`, and
  `IsUniformlyBoundedConstructibleAdicTower`. Read the complete local-model
  structure, its compatibility equation, and the normalized adjunction signatures.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, with its independent-universe tensor definition.
- `Sheaf.Paper.LevelwiseAdicTruncations`: `PbcLevelwiseTorVanishing`,
  `pbcReductionAdicTower`, `pbcReductionEvaluationIso`, and
  `pbc_reduction_adic_tower_laws`. Read both the Tor predicate and the canonical
  tower's explicit data and laws.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies
  `Functor.mapDerivedCategoryHomologyFunctorIso` for the canonical map.

All recorded proof-dependency modules, including the Smith-normal-form and
cohomology-long-exact Mathlib leaves, are imported. No existing mathematical
notion is redefined privately. All universes and variables are explicitly bound;
the small pro-etale site's object universe u+1 and morphism universe u remain
distinct, with coefficients and module sheaves in u+1.

### Edge cases and searches

Checked the empty scheme/empty stratification, zero ambient complex and zero
local models, the first quotient exponent one, every integer q and cutoff m,
and every positive Tor degree p. No lower bound on q or nonempty chart is imposed.
A positive torsion block `[A --varpi^e--> A]` is detected at n ≥ e by Tor_1,
including n = e = 1; it is not mistakenly declared flat. Empty systems cause
no converse gap because K's recorded membership supplies a common-model system.

Actual searches (repeated during this repair; the earlier search log is retained):

- `msearch.py ... leanfinder` with query “Flat cohomology of an adically complete
  constructible sheaf complex characterized by higher Tor of successive
  reductions”: eight hits, including `AdicCompletion.flat_of_isNoetherian`,
  `Module.Flat.iff_rTensor_exact`, and `Module.Flat.tfae_equational_criterion`;
  none states the sheaf-derived equivalence, every-model condition and canonical
  reduction clause together.
- `msearch.py ... loogle 'Module.Flat, IsDiscreteValuationRing'`: zero hits.
- `msearch.py ... grep 'adic.*Tor.*flat|torCompatible_iff_flat'`: zero Mathlib hits.
- `rg` for those patterns and the proposed helper names in upstream
  `WeilConjectures` and project `lean/Sheaf`: only the related
  `pbc_torCompatible_iff_flat_cohomology` in `IntegralCanonicalTruncations`.
  Read it: it uses degree-zero K-flatness to state a related ambient equivalence
  and omits the every-supplied-model condition and canonical reduction clause.
  It is not an exact existing match. The proposed helper names had no hits.
- `grep -rn` for this node id in upstream `WeilConjectures`: no hits.

### Compilation and repair of the previous blocker

The previous run stopped on duplicate retired K-flat declarations in the
levelwise-truncation import closure. This run tested dependency-only repairs in
scratch files, then recompiled the actual full statement against the current
published dependency sources. The current wrapper successfully rebuilds
`RingedTensorCohomologicalBounds` and `LevelwiseAdicTruncations` and compiles
`AdicTorFlatCohomology` with no errors or warnings. No dependency repair is needed
in this delivery; all trial dependency modules remain in scratchpad only.
The final packet contains exactly the item's module, its lean-only node copy,
and this report. The required `deliver2.py --no-push` result is recorded below.

Dry run: `deliver2.py ND lem-weil-pbc-adic-tor-flat-cohomology --no-push`
printed `OK (dry run)`: the single module compiles and the preflight passes except
for the independent second reading, which the second reader supplies. Nothing
was pushed. No self-authored second-reading section was added.

## Second reading by ND

I opened the node copy, the source paragraph in
`sec-smooth-base-change/sk-rem-rest/thm-weil-pbc-integral-truncations.md`, and
`Sheaf/Paper/AdicTorFlatCohomology.lean`. The item-by-item rendering is:

- The coefficient data are rendered by `l : ℕ`, `[Fact l.Prime]`,
  `E : Type (u + 1)`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`; `pbcPadicCoefficientDatum l E` supplies the
  recorded valuation ring, ideal, quotients, and uniformizer. This is the node's
  finite extension `E / ℚ_ℓ`, `A = 𝒪_E`, and `P_n = A/(ϖ^n)`.
- The scheme hypotheses are rendered by `[IsNoetherian T]`,
  `_hdim : ∃ n, topologicalKrullDim T ≤ n`, and
  `_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`. They match the finite affine
  noetherian-cover, finite chain-length, and local invertibility hypotheses; no
  nonempty or finite-type assumption is added.
- `K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)` is the
  recorded bounded constructible complete object. Its canonical tower is
  `pbcReductionAdicTower ... K.obj`, with levels
  `pbcCompletedReduction ... n`; `pbcAdicCompletion` and `pbcAdicRings` render
  `A_T` and `R_n`. The Lean index `n` denotes exponent `n + 1`, so every positive
  quotient in the node occurs exactly once.
- Clause (a) is rendered as
  `∀ m : ℤ, PbcLevelwiseTorVanishing ... m`. Unfolding that dependency gives
  `∀ n q, m + 1 ≤ q → ∀ p, 0 < p → IsZero (H^(-p)(H^q(K_(n+1))[0]
  ⊗ᴸ_{R_(n+1)} R_n))`. Quantifying all integer cutoffs is equivalent to the
  node's `∀ n ≥ 1, ∀ q, ∀ p ≥ 1` condition (take `m = q - 1`), and retains the
  levelwise-truncation formulation required by the dependency node.
- Clause (b) is the displayed `∀ q` predicate
  `SheafOfModules.IsFlatOnSite` over `pbcAdicCompletion ...`, exactly the
  exact-tensor definition of flatness in the node.
- Clause (c) is `PbcSuppliedModelCohomologyFlat ... K.obj`. Its binders supply
  the common bounds, finite locally closed stratification, covering sieves, and
  every `AdicTowerLocalModel`; its final predicate tests every model cohomology
  sheaf over the inverse-image completed ring. This is precisely “every supplied
  common local model,” including its normalization and reduction data.
- The conjunction of the two displayed equivalences is the node's three-way
  equivalence. `pbc_adic_flat_cohomology_reduction` assumes clause (b), one of
  those equivalent conditions, and states for every quotient index and degree
  that `pbcCohomologyScalarExtension` is an isomorphism and the reduced
  cohomology is flat over its quotient ring. The arrow is the canonical map
  built from the normalized scalar adjunctions, so this is the node's canonical
  reduction clause rather than an arbitrary comparison.

Edge cases checked: `T = ∅`, empty strata and covering sieves, zero complexes and
zero model cohomology, exponent one (`n = 0` in Lean), `p = 1`, arbitrary integer
degrees including the cutoff boundary, and the given characteristic/invertibility
hypothesis. No case is excluded by the universes: `T : Scheme.{u}`, coefficients
in `Type (u + 1)`, and the pro-etale site/object and morphism universes remain
distinct.

For the one-definition check I reran the three required searches: `msearch.py`
LeanFinder for “adic Tor flat cohomology,” Loogle for the module-flat/DVR form,
and `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for adic/Tor/flat
patterns and the helper names. The only related declaration is
`pbc_torCompatible_iff_flat_cohomology` in `IntegralCanonicalTruncations`; it
does not state the supplied-model clause or the canonical reduction clause, so
it is not an existing match. The two helpers in this module are new notions
belonging to this item, with real definitions and no duplicated declaration.

No mismatch was found, so no statement, dependency, or helper was changed. The
module compiled with `scompile.py` with no errors or warnings.
