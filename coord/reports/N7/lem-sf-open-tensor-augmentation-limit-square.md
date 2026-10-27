## Worker report

The delivery states `WeilConjectures.OpenTensorAugmentation.openTensorAugmentationLimitSquare`
in `lean/Sheaf/SixFunctors/OpenTensorAugmentationLimitSquare.lean`. There is one theorem,
with proof `sorry`, and no new definitions. Only the item's `lean` field changes.
No dependency module or new DAG node is needed.

Sources read: Bhatt–Scholze, *The pro-étale topology for schemes*, PDF pp.49–50,
Lemmas 6.5.5 and 6.5.8(2),(3), including the standing qcqs hypotheses of §6.5;
Stacks `sites-cohomology.tex`, `lemma-derived-limit-is-ok` (0940), and
`proetale.tex`, `lemma-j-shriek-limits` (09BP); the current blueprint's
`sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`.
The last source supplies the open-factor coherence context; this item's explicit
augmentation calculation is the agent-formulated refinement in its four DAG proof steps.

### Hypothesis and object correspondence

- Finite-field datum: `D : FiniteFieldDatum.{u}`; coefficient prime:
  `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- Finite extension: `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. Its integer ring, chosen uniformizer and positive
  quotients are the existing coefficient-extension constructions, used by the
  completed ring and finite tensor tower. No new coefficient ring is defined.
- Schemes and open immersion: `{U X : Scheme.{u}}`, `j : U ⟶ X`,
  `[IsOpenImmersion j]`. Both schemes have `Over (Spec (.of D.k))`, locally
  finite-type and quasi-compact structure maps, and `j.IsOver` that base.
  These are precisely finite-type k-schemes and a k-morphism. There is no
  separatedness assumption.
- The completed-coefficient module categories are `scalarReductionSource l E W`.
  They are the existing `SheafOfModules` categories on `W.ProEt` over the
  completed coefficient sheaf. The small site has object universe `u+1` and
  morphism universe `u`; these universes have not been equated. `DerivedCategory.Q`
  localizes the ordinary unbounded complexes, without passing to the complete
  subcategory to form tensors or limits.
- Exact ringed-slice extension/restriction: `o : IntegralOpenReduction.Operations`;
  `OpenSemilinearTensor.extensionComplex` and `restrictionComplex` are the
  actual termwise functors of that interface. The existing `o` includes their
  canonical slice identifications; no arbitrary extension or restriction is used.
- K and P are represented by `Q` and `F`, and `_hK`, `_hP` say exactly
  `sfIntegralConstructible` of their localized objects. The hypotheses `hQ`,
  `hF`, `hQX`, `hFU` express the flat-term K-flat representatives required in
  the node, including the extended and restricted representatives. These are
  conditions on representatives, with no extra boundedness or Tor condition
  on K or P. Open extension/restriction preserve this resolving class; the
  construction of those representatives is part of the cited tensor interfaces.
- `SX`, `SU`, `AX`, `AU`, `st`, `m`, `c`, `q` are the already recorded
  simultaneous coefficient-system, scalar, tensor and quotient-comparison
  presentations. They instantiate the constructions specified by the node.
  In particular `q : OpenTensorQuotient.Comparison` contains the actual
  `OpenFactorCoherence.Tensor` models `tensorX` and `tensorU`; no second
  completion map is defined.
- The strict T and S towers are exactly
  `(integralOperationsTensorTowerFunctor l E X).obj (extensionComplex.obj Q,F)`
  and `(integralOperationsTensorTowerFunctor l E U).obj (Q,restrictionComplex.obj F)`.
  Their objects are the restricted-scalar finite total tensors, and the
  functors retain every quotient transition. Index `n : ℕ` denotes exponent
  `n+1`, so there is no spurious exponent-zero level or missing exponent-one case.
- `z : OpenTensorQuotient.StrictSquare` is the specified strict augmented
  square, with `z.upper.map`, `z.lower.map`, and `z.gamma`. Its `square` and
  `lowerRouteFormula` are the strict augmentation equality in the node. `_nX`
  and `_nU` are the existing `RoosNormalization` clauses. The ordinary gamma^B
  is represented by `m.totalComparison.chain Q F`, whose summand and generator
  normalization is part of `TotalComparison`.
- `lambda` is the natural chain isomorphism presenting the supplied lambda_S.
  `_first` fixes its first coordinate to the actual `piComparison`, and
  `_shifted` fixes the shifted coordinate to the same product comparison.
  These spell out the signed normalization from the node, rather than assume
  the desired augmentation square. Such a normalized comparison is supplied
  by `SfOpenRoos.comparison`/`exactProductFunctorStrictLimit`.

### Conclusion correspondence

The theorem returns `bT`, `bS` as chain representatives of the two actual derived
augmentation maps. Their four coordinate clauses fix, for every positive quotient,
the first coordinate to `z.upper.map.app (op n)` or `z.lower.map.app (op n)` and
all shifted coordinates to zero. Therefore these are the specified `(c,0)` maps,
not unspecified lifts with the same separate derived evaluations.

`IsIso (DerivedCategory.Q.map bT)` and its bS counterpart are the two
invertibility assertions. The two following equality clauses identify those same
maps with `ordinary.representative.hom ≫ chi.app ≫
integralCompletedTensorComparison.hom`. Thus, under the defining completed-tensor
identifications, a_T and a_S equal the actual recorded chi maps. Two explicit
isomorphisms `compareX` and `compareU` identify the existing signed total tensor
presentations; their homogeneous local pure-tensor formulas force the canonical
identification. These isomorphisms and their normalization are conclusions, not
assumed arbitrary maps. Every comparison equation and the final square is an
ordinary equality in the derived category. The existential flatness witnesses
translate `integralOperationsGoodComplex` to the existing
`ProEtaleTensorModel.representative` domain; they are conclusions, not additional
mathematical assumptions.

The final clause is an ordinary equality in the ambient derived category:

```
Q.map bT ≫ Q.map (integralOperationsRoosMap z.gamma.hom) =
  Q.map (m.totalComparison.chain Q F).hom ≫
    Q.map (extensionComplex.map bS) ≫ Q.map (lambda.hom.app S)
```

In mathematical composition order this is exactly
`L_X(gamma) a_T = lambda_S j_!(a_S) gamma^B`. The exact functor's usual
`mapDerivedCategoryFactors` transports this termwise representative into
`j_!(a_S)`; hence both sides use the actual derived morphisms. The Roos objects
are the recorded mapping cocones of `1-s`, computing total right derived limits
by the cited normalized strict-limit comparison. Products of evaluations in a
bare derived category are never used to infer equality. There is no finite-Tor
assumption over any finite quotient, and no boundedness assumption on the
representatives or on the finite tensor totalizations.

### Dependency declarations used

Each recorded dependency is imported directly; the collection node for scheme
properties has no module and supplies the usual finite-type conventions.

| Dependency module | Recorded declaration / interface used |
| --- | --- |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` | `SheafOfModules.IsFlatOnSite` |
| `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` | `CochainComplex.IsKFlatIndependentCoefficients` |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | `IntegralOnSlice.completedTensor`; reexported `integralOperationsTensorTowerFunctor`, `integralCompletedTensorComparison`, normalized Roos construction |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | `OpenFactorCoherence.Tensor`, `Tensor.chi`, `IsTensorChain`, `IsTensorCompletion` |
| `Mathlib.Algebra.Homology.DerivedCategory.Basic` | `DerivedCategory`, `DerivedCategory.Q` |
| `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` | `integralConstantToCompletionOfUniverses`; reexported completed coefficient sheaf |
| `Sheaf.Paper.SfIntegralConstructible` | `sfIntegralConstructible` |
| `Sheaf.Paper.FiniteFieldFiber` | `FiniteFieldDatum` |
| `Sheaf.Paper.IntegralReductionTowerCanonical` | `canonicalIntegralReductionTower`; reexported finite reductions, quotient transitions, scalar-unit sections |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing` and its coefficient constructions |
| `Mathlib.AlgebraicGeometry.OpenImmersion` | `AlgebraicGeometry.IsOpenImmersion` |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `Scheme.ProEt.topology` |
| `Sheaf.CategoryTheory.RingedSiteModules` | `CategoryTheory.ringedSiteModules` |
| `Sheaf.Paper.ExactProductFunctorStrictLimit` | `CategoryTheory.exactProductFunctorStrictLimit` |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | `constructibleTensorCompletion`, `constructibleTensorBoundary` |
| `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` | `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` |
| `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` | `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`, canonical adjunction |
| `Sheaf.Paper.SfOpenRoosExtensionComparison` | `SfOpenRoos.comparison`, `ComparisonAssertions` |
| `Sheaf.SixFunctors.OpenTensorNormalization` | `SheafOfModules.openTensorNormalization` |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | `openTensorQuotientAugmentation`, `Comparison`, `StrictSquare`, `RoosNormalization` |

The type signatures and normalization docstrings of the tensor, quotient and Roos
interfaces were read, including the full `StrictSquare`, `Tensor.canonical`, and
`ComparisonAssertions` definitions. No existing declaration gives this item's
specific invertible augmented limit square. The downstream
`OpenProjectionRoosCompletion` has related clauses but is the consumer whose
proof cites this item, and is deliberately not imported.

### Edge cases and searches

Checked U empty, X empty, j the identity, either input zero, positive exponent
one, arbitrary quotient transitions, and unbounded representative complexes.
There is no nonemptiness assumption on a scheme, no truncation of the tower,
and no finite Tor-amplitude condition. Identity and empty cases reduce to
their canonical coordinate maps. Non-separated finite-type schemes are included.
The proof docstring follows the four recorded DAG steps and retains both signs.

Actual searches made with `msearch.py N7 lem-sf-open-tensor-augmentation-limit-square`:

- `leanfinder`: “augmented strict finite tensor projection square derived limit
  open extension”. Eight hits (finite-product extension, ordinary limit
  monoidal comparison, Čech nerves), none this theorem.
- `loogle`: “DerivedCategory, tensor, limit, augmentation”. Zero hits;
  `tensor` is an unknown identifier in that service. This is not claimed to
  establish absence.
- `loogle`: “OpenTensorQuotient.Comparison, OpenFactorCoherence.Tensor, IsIso”.
  Zero hits; project names are unknown to that service.
- `leansearch`: “The quotient augmentations of an open tensor projection
  formula yield a commuting square under the derived inverse limit”. Eight
  hits on ordinary tensor/direct limits and `limit.isoLimitCone_inv_π`, no
  derived pro-etale augmented square.
- `grep`: “open.*tensor.*augmentation|augmentation.*limit.*square|OpenTensorAugmentation”
  (Sheaf filter), zero service hits; direct project `rg` did find the expected
  existing quotient and scalar-unit augmentation interfaces, which are reused.
- `grep`: “openTensorAugmentation|augmentationLimit|tensor.*limitSquare”
  (WeilConjectures filter), zero service hits.
- `grep`: “Roos|augmentation.*limit|tensor.*completion” in Mathlib CategoryTheory,
  zero service hits.
- Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf`, of
  `dag/lean_names_upstream.json`, and of Mathlib found no declaration with the
  item's id or proposed full declaration name. Related project declarations
  supply the strict square and normalization, not the conclusion of this item.

No statement dispute, source correction, new notion, or dependency repair is reported.

### Validation

Compiled only through the prescribed server wrapper `scompile.py`. The final
module compiled as both the sandbox module and its library module with no errors
or warnings. The only postponed proof is
`WeilConjectures.OpenTensorAugmentation.openTensorAugmentationLimitSquare`.
The scoped heartbeat setting accounts for the several existing tensor and
Roos presentations in the single signature; each final compile was about 22–24 s,
within the unmodified 60 s limit. All variables and universes are explicitly bound.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
