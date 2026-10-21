## Worker report

The item is stated by `AlgebraicGeometry.Scheme.rationalRealizationDegreeReflection`
in `Sheaf.Paper.RationalRealizationDegreeReflection`. Its proof is exactly `by sorry`.
There is no change to the item's mathematical statement or dependency lists.

Hypotheses and notation, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `pbcIntegralDatum l E` and `pbcUniformizer l E` give the recorded integer ring,
  ideal and chosen uniformizer. No additional valuation or flatness is chosen.
- `(X : Scheme.{u}) [IsNoetherian X]`, the finite-dimension Fact
  `∃ n : ℕ, topologicalKrullDim X ≤ n`, and the invertibility Fact
  `∀ x : X, IsUnit (l : X.presheaf.stalk x)` express exactly the scheme hypotheses.
- `PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)` is the full completed
  integral category, retaining the compatible etale-origin witnesses.
  `PbcRationalCategory ... (pbcUniformizer l E)` and `pbcRationalization ...` are
  the existing raw scalar localization and Q, without an idempotent envelope.
- `(R : RationalModuleRealization l E X)` uses the dependency's actual coefficient
  comparisons, derived extension, object/fraction formulas, exactness and
  constructible-cohomology assertions. In particular its coefficient map is
  `R.integralIso.hom ≫ R.inclusion`, from completed B_X to the continuous E_X.
  The tensor sheaves, continuous constructibility, finite stratifications,
  derived categories and homology functors are those of the recorded dependencies;
  this theorem introduces no alternate encoding of any of them.
- `(_hJ : R.J.FullyFaithful)` is precisely the assumed full faithfulness, not a
  claimed proof or an essential-surjectivity hypothesis.
- `rationalRealizationTStructure l E X` is `(pbc_localized_tstructure X l E).choose`.
  The theorem specifies both zero halves as strictly full integral images; these
  determine the t-structure uniquely. This selects the already specified localized
  structure, not a t-structure satisfying additional assumptions. Its shifts and
  triangles are the dependency's localized ones. `rationalRealizationCommShift`
  only exposes `R.shift` as a global instance for the connecting-arrow formula.

Conclusions, in their order in the signature:

1. For every integral K and integer m, the first conjunct is the equivalence of
   localized `le m (Q.obj K)` with `IsZero (H^r (J.obj (Q.obj K)))` for all `m < r`.
   The second is the corresponding `ge m` equivalence for all `r < m`.
2. The existential families α and β are natural isomorphisms of functors from
   the entire rational category, for every integer m. Thus naturality includes
   arbitrary rational morphisms and fractions, not just images of integral maps.
   The first equation is the lower counit normalization; the second is the upper
   unit normalization. The third includes `truncGEδLE m (m+1) rfl`, the specified
   `R.J.commShiftIso 1`, and the shifted α component: it is exactly commutativity
   at the connecting arrow of the truncation triangle, with β at m+1. Together
   these equations compare the whole triangles with identity on JZ.
3. The natural isomorphism for every r compares the functor
   `Q ⋙ shiftFunctor _ r ⋙ truncLE 0 ⋙ truncGE 0 ⋙ R.J` with
   `ι ⋙ DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (...) ⋙
   DerivedCategory.singleFunctor _ 0`. The left side is realization of the
   heart-valued cohomology object, with H^0(K[r]) = H^r(K). The right side is
   the ordinary sheaf E_X tensor_B_X H^r(K), placed in degree zero. The use of
   functor isomorphism makes this identification natural in K.
4. For every rational object Z, `t.heart Z` is equivalent to vanishing of the
   realized cohomology in every degree other than zero.
5. For every ambient rational derived object M, being isomorphic to realization
   of a heart object is equivalent to `R.J.essImage M` and concentration in degree
   zero. With the assumed full faithfulness, this states the asserted heart
   identification without asserting essential surjectivity onto all constructibles.

All universes and variables are explicit (`set_option autoImplicit false`). No
Tor-compatibility or torsion-free-cohomology hypothesis occurs. There are no new
DAG notions and no statement correction or disputed statement.

Dependency declarations read and used (direct public imports unless noted):

| Node notion | Module | Declaration |
|---|---|---|
| finite stratification | `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` | `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` |
| sheaf tensor | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` | `SheafOfModules.cochainModulesMonoidal` |
| derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic` | `DerivedCategory`, `DerivedCategory.singleFunctor` |
| cohomology | `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` | `DerivedCategory.homologyFunctor` |
| coefficient extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing` and imported coefficient constructions |
| completed coefficients | `Sheaf.Paper.AdicCoefficientDatum` | `AlgebraicGeometry.Scheme.completedReductionTower` and its coefficient constructions |
| completed integral category | `Sheaf.Paper.IntegralUniformCoefficient` | `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete` and `PbcBoundedConstructibleComplete` |
| continuous constructibility | `Sheaf.Paper.ContinuousConstructibleModule` | `AlgebraicGeometry.ProEtale.IsContinuousConstructible` |
| small pro-etale site | `Mathlib.AlgebraicGeometry.Sites.Proetale` | `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology` |
| raw rationalization | `Sheaf.Paper.PbcRationalCategory` | `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`, `PbcRationalCategory`, `pbcRationalization` |
| general module sheaves | `Sheaf.CategoryTheory.RingedSiteModules` | `CategoryTheory.ringedSiteModules` |
| specified realization | `Sheaf.Paper.RationalModuleRealizationFunctor` | `AlgebraicGeometry.Scheme.RationalModuleRealization`, `rationalModuleRealizationFunctor` |
| localized t-structure | `Sheaf.Paper.LocalizedTStructure` | `AlgebraicGeometry.Scheme.pbc_localized_tstructure` |
| integral t-structure | `Sheaf.Paper.IntegralTStructure` | `AlgebraicGeometry.Scheme.pbcIntegralTStructure`, `pbc_integral_tstructure` |
| standard ambient t-structure | `Mathlib.Algebra.Homology.DerivedCategory.TStructure` | `DerivedCategory.TStructure.t`, `DerivedCategory.isLE_iff`, `isGE_iff` |
| truncation/heart tools (proof import) | `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` | `CategoryTheory.Triangulated.TStructure.homology₀`, `isHomological_homology₀`, imported truncation adjunctions |
| good truncation tools (proof import) | `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` | imported good truncations; its recorded `CategoryTheory.IsSequentialHomotopyColimit` is not needed in the formula |

The actual source PDF was read with pdftotext, printed pp. 60--62: Proposition
6.8.11(3) characterizes integral constructible complexes by bounded constructible
cohomology; Proposition 6.8.14(2) gives the rationalization equivalence. The item
uses the explicitly stated full-faithfulness hypothesis and the existing integral
and rational t-structures to draw its degree and truncation conclusions. The
proof docstring reproduces all seven DAG proof steps, including inverse lifting
for each reflected bound and the kernel/image calculation for heart cohomology.

Edge cases checked: zero K and the empty scheme give zero sheaves and satisfy
both reflected bounds; all integer m and r (including negative degrees and r=0)
are retained. The strict inequalities correctly exclude the endpoint in each
bound. A torsion integral sheaf can become zero after localization and therefore
satisfy every localized bound; the claim uses QK rather than the original K and
so does not incorrectly reflect an integral bound. No reduction/truncation
commutation is used. The cohomology functor order is shift r, lower truncation
at zero, upper truncation at zero, giving H^r in the heart, with no sign reversal.
The triangle upper endpoint is m+1, and the separate unit equation is at m.

Searches performed through msearch.py:

- LeanFinder: “A fully faithful t exact functor reflects cohomological bounds and
  commutes with canonical truncation triangles”. Eight results, including
  `Functor.map_distinguished_exact`, `IsTriangulated.of_fully_faithful_triangulated_functor`
  and `Functor.map_distinguished_iff`: generic exactness infrastructure only.
- Loogle: `CategoryTheory.Triangulated.TStructure`. Twelve results: the t-structure,
  IsGE/IsLE and its bounded/plus/minus/le/ge object properties, not this theorem.
- Mathlib grep: `IsTExact|truncLE|truncGE` in
  `CategoryTheory/Triangulated/TStructure`. Twenty-two displayed results for
  ordinary truncations, induced t-structures and extended truncations. Read the
  truncLE/truncGE and truncGEδLE definitions; none states the item.
- LeanSearch: “A fully faithful t exact functor reflects t structure bounds and
  commutes naturally with truncations”. Eight results for reflected isomorphisms,
  limits/colimits, triangulated structures and unrelated simplicial functors;
  no match for the complete item.
- Project/upstream rg: `rational.*[Rr]ealization|realization.*[Tt]runc|lem-per-rational-realization-degree-reflection`
  in both `lean/WeilConjectures` and `lean/Sheaf`: the recorded module realization
  and other monodromy/comparison contexts only; no degree-reflection theorem.
  Exact-name search for `rationalRealizationTStructure|rationalRealizationDegreeReflection`
  in Mathlib, both source roots and `dag/lean_names_upstream.json`: no matches.

Validation: prescribed scompile.py compiled the item cleanly (library path 9.4 s,
sandbox 8.1 s). The realization dependency also compiled privately while its landing
was in progress; it has since landed and is not included in this packet. The final
dry run uses the landed dependency. No local lake/global build was run.

## Second reading by Q23

Author's second pass, not an independent review (the dispatcher forbids spawning
agents and the maintainer supplies independent review). Reopened the item and
final signature. Matched the coefficient and scheme hypotheses, the specified
realization, full faithfulness, both bounds, both natural comparisons, both
normalization equations, the connecting arrow with the shift comparison,
the natural degree-zero sheaf identification and both heart formulations.
The first compile exposed the unregistered shift field; the only adapter now
returns that exact field. The initial missing server dependency subsequently landed; the redundant unchanged
copy was removed after preflight identified that it was now present on the base. No mathematical mismatch or statement change was
found. In particular the chosen t-structure is determined by the existing
localized half descriptions, and the ordinary sheaf is extended from completed
coefficients, rather than from an incorrectly identified constant ring sheaf.
