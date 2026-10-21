## Worker report

Item: `lem-weil-pbc-pulled-reduction-normalization-comparison` (Q43).

The module `Sheaf.Paper.PulledReductionNormalizationComparison` states
`AlgebraicGeometry.Scheme.PulledNormalization.pulled_reduction_normalization_comparison`.
Its conclusion is `Nonempty (Comparison d g)`. `Comparison` spells out the
normalized natural comparisons, their computation on actual module cochain
complexes, the square, triple coherence and scalar unit. The only postponed proof
is this theorem. The auxiliary definitions have real data from the published
coefficient, scalar-extension and pullback constructions; no arbitrary comparison
map is introduced in place of a canonical construction.

The node's statement, statement dependencies and proof are unchanged. There are
no new nodes and no dependency repairs. In particular, the recorded strict-tower
comparison and independent-coefficient K-flat interfaces are available and used.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| A morphism of schemes g:T'→T | `{X Y : Scheme.{t}} (g : X ⟶ Y)`, with X=T', Y=T. |
| The adic datum of the recorded node | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`. Its existing fields supply the Noetherian ring, ideal, finite perfect positive quotients and torsion hypothesis; none is replaced by a new assumption. |
| Small pro-etale sites | `ProEt.topology X`, `ProEt.topology Y` on the original sites. Object, morphism, coefficient and derived morphism universes remain respectively t+1, t, t+1, t+2. |
| B_W, R_W and S_n,W | `d.completedRing W`, `exchangeConstantRing W A`, and `d.finiteRing W n`. |
| Arbitrary K in D(B_T) | The laws quantify `(K : d.derived Y)`; there is no completeness, boundedness, constructibility or torsion condition on K. |
| Positive quotient exponents | The published coefficient API is zero based: n denotes exponent n+1. Thus `a ≤ b` is exactly b≥a≥1 in the paper, including exponent one. |
| K_n | `(d.reduction Y n).obj K`, using the existing completed-coefficient derived scalar extension. |
| N=Lg_R* Res K | `(PulledReduction.source d g).obj K`; its ordinary functor is the recorded `PulledReduction.ordinarySource`. |
| N_n | `(N d g n).obj K`, namely the preceding source followed by `reductionDerivedChange X (OrderedExchange.quotient d X n)`. |
| Finite module inverse image and H_n | `finitePull d g n` is exactly `proEtaleRingModulePullback` for `d.finiteRingIso g n`; `H d g n = d.reduction Y n ⋙ (finitePull d g n).mapDerivedCategory`. |
| Specified finite comparison tau_n | `Comparison.tau n : N d g n ≅ H d g n`, with `ordinaryTau_formula` and `tau_representative` fixing the normalized finite map of the strict-tower comparison. These are not bare uncharacterized objectwise isomorphisms. |

The finite comparison is specified by the strict comparison's same local formula:
`([x] tensor r) tensor s` goes to `[x tensor 1] * r-bar * s`.
`constantGenerator` and `finiteGenerator` use the published pullback adjunction
units, and `reductionTensorSection` is the existing sheaf tensor section. The
formula is required for all modules, all source-site objects and all sections and
coefficients. `tau_representative` fixes its derived localization through the
canonical computation counits. Thus the finite comparison is characterized by
its normalized map, rather than choosing an unrelated isomorphism or assuming
new comparison data as a hypothesis. The strict comparison's tower-level target
and this finite pullback target agree by these normalized computations.

### Clauses of the conclusion

| Node clause | Lean rendering |
| --- | --- |
| thetaN is successive scalar normalization | `scalarPresentation` packages the existing ordinary extension and its universal derived pair. `ScalarNormalization` specializes the dependency's `Normalization` to those exact functors. `thetaN` is `scalarAssoc` whiskered by the recorded N source, followed by the coefficient equality `quotientComp`. The ordinary double and triple tensor formulas and derived representative equation are inherited from `Normalization`. |
| thetaH is canonical pullback/scalar comparison followed by pulled completed normalization | `thetaH` is defined as the composite of explicit functor associators, `proEtaleReductionPullbackInv` and `Functor.whiskerRight (completedReductionDerivedNormalization Y d b a h) (finitePull d g a).mapDerivedCategory`. `quotientCompatibility` states the coefficient-square identity needed to type this canonical mate, and is proved as part of the conclusion rather than assumed of g or d. |
| thetaH invertible | `Comparison.thetaH_isIso` for every b,a and a≤b, in the actual S_a,T'-module derived category. |
| thetaH (tau_b tensor 1) = tau_a thetaN | `Comparison.square`; scalar extension of tau_b is `.map ((tau b).hom.app K)`. The equality uses Lean's left-to-right composition convention, so its order exactly matches the displayed square. |
| Natural in K | `H`, `N` and all scalar/pullback constructions are functors; `tau`, `thetaN` are natural isomorphisms and `thetaH` is a natural transformation. Ordinary representatives are also natural isomorphisms. Naturality is part of their types. |
| Triple coherence for c≥b≥a | `Comparison.associative`; `quotientAssociator` is the normalized derived associator specialized to q_c,b and q_b,a, transported along the existing `reductionCoefficientMap_comp` equality. The equation compares the two-step thetaH route with this associator followed by thetaH_c,a. |
| Equal-index scalar unit | `ordinaryUnit`, `ordinaryUnit_formula`, `derivedUnit` and `unit_representative` fix the ordinary multiplication map and its derived localization; `Comparison.unit` identifies thetaH_a,a with exactly that unit. This does not substitute an arbitrary automorphism of H_a. |
| Any flat-term K-flat representative P | `computed`, `tau_representative`, `theta_representative` universally quantify P, the recorded `CochainComplex.IsKFlatIndependentCoefficients`, and flatness of each `P.X i` using `SheafOfModules.IsFlatOnSite`. These are hypotheses solely of the representative-computation clauses. |
| Actual computation maps invertible | `computed` asserts `IsIso (nCounit d g n P)` and `IsIso (hCounit d g n P)`. Both counits are explicit composites of published scalar computation counits and exact-pullback derived factorizations. |
| Double balancing before inverse image | `ScalarNormalization` uses `Normalization.ordinary_hom`, `ordinary_inv` and `representative` for the actual scalar functors, while the Y-side completed normalization in `thetaH` is the datum's `completedReductionDerivedNormalization`, defined using its `reductionBalance` maps. Their formula is `(x tensor t) tensor s` mapped to `x tensor q(t)s`. |
| Double balancing after inverse image/scalar extension | `ordinaryTheta_formula` says `(s * [x tensor 1]) tensor v` maps to `q(s)v * [x tensor 1]`. Scalar-first tensors in the published API reverse the written order of the scalar and module slot, without changing the map. |
| Both triple composites have q_c,a(t)q_b,a(s)v | `ordinaryTriple_formula` is a conjunction: its first equation evaluates the composite through b; its second evaluates the directly reassociated route. Both right sides are literally the same product times `finiteGenerator`. The pre-inverse-image formula is the datum's `reductionBalance_cocycle` and the recorded normalization's associativity and section formula. |
| Formulas are maps of sheaf tensor complexes | `ordinaryTau` and `ordinaryTheta` are natural transformations of the actual sheaf-module scalar/pullback functors. `NatIso.mapHomologicalComplex ... (.up ℤ)` applies these maps degreewise to actual cochain complexes, and `DerivedCategory.Q.map` localizes them. `CochainComplex.mapBifunctor` supplies the imported recorded tensor-complex notion; the degree-zero coefficient complexes yield the ordinary scalar complexes used by this API. |
| These formulas induce the derived maps | `tau_representative` and `theta_representative` are the commuting computation-counit equations, with no replacement by merely isomorphic objects. |
| Independence of representative | The comparisons and all coherence equalities are defined/required for every object K of the derived category. The computation equations hold for every eligible P mapping to `DerivedCategory.Q.obj P`; they do not select a special resolution as part of the statement. Universal scalar counits and exact pullback factorizations are the resolution comparisons. |

### Dependencies and sources read

Statement dependency declarations, including their full signatures and docstrings:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, its completed and
  finite coefficient sheaves, `reductionCoefficientMap`, `reductionChange`,
  `reductionDerivedChange`, `reductionScalarComplexCounit`,
  `completedReductionProjection_comp`, `completedReductionDerivedNormalization`,
  and the double/triple `reductionBalance` specifications.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the dependency's recorded
  `pbcQbarCompletedPull`, whose public imports retain the integral ambient
  `Sheaf.Paper.CompletedTowerPullback` construction. This statement concerns the
  integral ambient category, not the extra rational constructible specialization.
  `proEtaleRingModulePullback`, `proEtaleRingModuleAdjunction`,
  `proEtaleSheafInverseImage`, and `proEtaleReductionPullbackInv` are the retained
  original-site finite/constant constructions; `Sheaf.Paper.FourCorners` exposes
  the scalar comparison and coefficient-square properties.
- `Sheaf.Paper.PulledReductionStrictTowerComparison`:
  `AlgebraicGeometry.Scheme.PulledReduction.strictTowerComparison`, `res`,
  `ordinarySource`, `source`, `IsStrictNormalized`, and `targetCounit`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`;
  its public data module provides `Presentation` and `Normalization` with explicit
  normalized tensor, derived, unit and coherence fields. The specialization uses
  the already published universal derived pairs, with explicit canonical
  sheafification instances to retain the site's unequal universes.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (the recorded predicate).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `HomologicalComplex.mapBifunctor`, the total tensor-complex construction.

All recorded proof-dependency modules are imported, including K-flat resolution,
constant/completed equivalence, K-flat preservation under ringed inverse image,
independent-universe derived change of rings and ringed pullback, the flat finite
adjunct, normalized scalar comparison, ringed tensor section calculus and
site derived tensor descent. The theorem docstring carries the node's seven-step
proof plan and names those prerequisites.

Source material consulted: `literature/stacks-project/sites-cohomology.tex`,
Tags 07A4, 0D6D and 0G7E (tensor pullback, composition, and K-flat pullback), and
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction.proof.md`.
The detailed quotient balancing calculations are those written in the item node.

### Edge cases checked

These are statement checks, not claims of separately proved Lean examples.

- g equal to an identity and empty schemes: only the canonical site inverse image
  and coefficient identifications occur; no points, nonemptiness or field
  characteristic hypothesis has been added.
- K=0, and arbitrary unbounded or noncomplete K: the ambient derived category is
  unchanged. K-flat/term-flat assumptions appear only when computing on P.
- Lowest positive exponent, b=a and c=b=a: zero-based indexing includes all of
  them. The unit field explicitly includes equality of indices; the triple field
  permits equality at either step.
- Nonflat quotient maps, for example the ordinary reduction from a second power
  to a first power of a nonzero adic ideal: no flatness of q_b,a is assumed. All
  reductions remain derived, and the representatives have flat terms over their
  respective source rings.
- Zero quotient rings (including the unit ideal) are not excluded beyond the
  conditions already contained in `AdicCoefficientDatum`.
- Arbitrary scheme universe t: the small pro-etale site's object and morphism
  universes are not identified. Explicit canonical coefficient sheafification
  resolves inference without adding a universe equality hypothesis.

### Searches for an existing statement

The searches used the prescribed `msearch.py` wrapper with this group/item:

- LeanFinder: `Derived pullback scalar extension quotient normalization associativity unit coherence`.
  Eight results, including ordinary scheme-module pullback composition and
  pseudofunctor unit/associativity lemmas; none states this derived completed/
  constant finite comparison and its normalized square.
- Loogle: `SheafOfModules.pullbackComp, ModuleCat.extendScalars_assoc`.
  No results.
- Mathlib grep: `pullback.*[Nn]ormaliz|[Nn]ormaliz.*pullback`.
  Ten results concerning scheme normalization and its pullbacks; no match for
  derived successive quotient comparison.
- Project and upstream rg:
  `pulled-reduction-normalization|PulledReduction|pulledReduction|successive.*[Nn]ormalization`
  in `lean/WeilConjectures` and `lean/Sheaf`.
  Found the strict-tower comparison, generic successive derived normalization,
  and a scheme-derived tensor normalization interface. None states this node.
  The first two supply the interfaces used here rather than private copies.
- Exact `grep -rn` for the item id in `lean/WeilConjectures`: no match.

No statement dispute or source fault was found. Compilation uses only the
prescribed `scompile.py` wrapper, against the live published library. The final
module compiles with no errors or non-sorry warnings.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
