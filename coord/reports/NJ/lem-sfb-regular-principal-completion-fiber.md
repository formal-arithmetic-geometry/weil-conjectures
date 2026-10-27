## Worker report

The module `Sheaf.Algebra.Homology.RegularPrincipalCompletionFiber` states
`CategoryTheory.regularPrincipalCompletionFiber`. Its only postponed theorem is
this declaration, with proof `sorry`. All helper definitions contain real data.
No accepted split, source, proof step or proof dependency is changed. The item's
statement dependencies gain three already landed definition nodes, whose recorded
interfaces the module uses.

Hypothesis and clause correspondence:

- A scheme T and its small pro-etale site: `X : AlgebraicGeometry.Scheme.{t}`,
  `AlgebraicGeometry.Scheme.ProEt.topology X`. The site has object universe `t+1`
  and morphism universe `t`; coefficient universe `max u (t+1)` contains both.
  The site is essentially small at this universe, as provided by its existing
  instances; `HasDerivedCategory.{w}` fixes the localization universe.
- A sheaf of commutative rings: `R : Sheaf ... CommRingCat.{max u (t+1)}`.
  `PrincipalCompletionFiber.Modules R` transparently abbreviates the recorded
  `ringedSiteModules` of the underlying ring sheaf. No second module category or
  abelian structure is constructed.
- A global section and its regularity: `a` is a compatible global section of the
  unit module of the underlying ring sheaf; `_ha : Mono
  (globalSectionMultiplication R a)` is precisely monicity of multiplication on R.
  There is no regularity requirement on K.
- The ordinary unbounded derived category: `DerivedCategory.{w} (Modules R)`;
  representatives are `CochainComplex (Modules R) ℤ`, with no support bound.
- Positive quotient levels and quotient transitions: the existing
  `PrincipalQuotientCompletion.Model R a` uses `principalReductionTower`, whose
  level n is the cokernel of multiplication by `a^(n+1)`, concentrated in degree
  zero, with the quotient transition induced by the identity on R.
- Derived reduction and restriction of scalars: the model's `quotientTower`
  uses `reductionTensorTower`, i.e. the total sheaf tensor of this quotient,
  already regarded as an R-module, with the representative. Its `computes`
  field requires the counit to be invertible on every K-flat representative.
  This is `Res_n(K ⊗^L_R Q_n)` in the symmetric Q_n ⊗ P presentation; no
  additional flatness or boundedness is imposed. The general sheaf restriction
  of scalars is Mathlib's `SheafOfModules.restrictScalars`, imported publicly.
- Completion C_a: `F.completion` in the existentially supplied existing `Model`.
  This model includes the total left-derived universal property of the actual
  quotient Roos functor; its K-flat computation is the augmented strict Roos
  representative of total right-derived inverse limit. Exact countable products
  on this pro-etale site, together with the recorded strict Roos derivation and
  normalization, identify these descriptions. The universal property fixes the
  pair up to its unique compatible isomorphism. The theorem asserts existence
  of F, rather than assuming an arbitrary completion functor or model exists.
- The repeated-a tower: `scalar` lifts the existing
  `PresheafOfModules.sectionsSMul`; `scalarComplex` applies it in every degree.
  `scalarTower` uses `Functor.ofOpSequence`, constantly the identity functor
  on complexes, with transition `scalarComplex R a`; it then uses the existing
  degreewise `transpose`. `scalarRoos` is exactly this functor followed by
  `roosF = Cone(1-shift)[-1]`, with no second cone convention.
- Its localization T_a: `T` together with the natural isomorphism
  `φ : scalarRoos R a ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ T`.
  This requires the actual complex functor, including its maps, to descend at
  quasi-isomorphisms. It is not an arbitrary object isomorphic separately on
  cohomology groups.
- First evaluation e_K: the natural transformation `e : T ⟶ 𝟭 _` is normalized
  by the first displayed conjunct: `φ.hom.app P ≫ e.app (Q.obj P)` equals
  `Q.map (roosEval (scalarTower.obj P) 0)`. Zero-based level 0 is the first term
  of the positive tower. `roosEval` is the unshifted product projection.
- Multiplication by a on derived objects: the natural transformation `μ` is
  normalized on every complex by the second conjunct, equal to localization of
  `scalarComplex`. Thus `e.app K ≫ μ.app K` is exactly a times first evaluation.
- The completion unit is precisely `F.unit.app K`. The existing `Model`
  requires a chain augmentation on every complex, `coordinates` equal to zero
  in the shifted coordinate and the product of the actual quotient maps in the
  other coordinate, and `unit_computes` identifying its localization with this
  same unit under the universal counit. This rules out an arbitrary lift of
  the product components.
- The triangle and its naturality: `δ : F.completion ⟶ T ⋙ shiftFunctor _ 1`
  and `Triangle.mk (e.app K ≫ μ.app K) (F.unit.app K) (δ.app K) ∈ distTriang _`
  for every derived object K. All three arrows are natural transformations
  on the derived category itself, including roofs and arbitrary quasi-isomorphic
  representatives; no naturality is limited to chain maps or chosen objects.

Recorded statement-dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `def-weil-size-convention` has no declaration; explicit universe binders,
  `EssentiallySmall` and `HasDerivedCategory` implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its triangulated structure.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, used by `Model.computes`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  via the existing total-tensor quotient tower.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`; retained as the
  recorded derived-limit convention. The actual construction uses strict Roos.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosEval`, `roosχ`.
- Added landed node `def-pur-principal-koszul-quotient-towers`:
  `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`,
  `globalSectionMultiplication`, `principalQuotient`, `principalReductionTower`,
  `reductionTensorTower`, `koszulRepresentativeQuotient` and its tensor comparison.
- Added landed node `def-pur-principal-quotient-completion-model`:
  `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel`,
  `PrincipalQuotientCompletion.transpose`, `quotientTower`, `quotientRoos`, `Model`.
- Added landed node `def-pur-sheaf-modules-hom-module`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`,
  with existing underlying `PresheafOfModules.sectionsSMul` and its naturality.

All available proof-dependency modules are imported privately. The theorem's
seven-step docstring reproduces the DAG proof, including regular Koszul reduction,
strict cone signs, the finite-sum constant-tower contraction, first-arrow factor a,
both augmentation coordinates, and naturality through K-flat roofs and refinements.

Edge cases checked before writing: K=0, the empty scheme and the zero ring remain
allowed. For a invertible, the quotient completion vanishes and the first evaluation
of the repeated-a tower is invertible, giving the expected triangle. For R=ℤ and
regular a=p, K=ℤ, the fibre is `(ℤ_p/ℤ)[-1]`, so the extra factor p in the first
arrow must be retained for the n≥1 normalization. For a=0 regularity is impossible
on a nonzero R; it is permitted on the zero ring, consistently. Nonconnective and
unbounded K, arbitrary coefficient characteristic, and the smallest positive
exponent 1 are all included. The helper scalar construction itself requires no
regularity. The source PDF was read at printed pp.22--23 (Lemmas 3.4.9 and 3.4.12).

Searches for an existing statement:

- `msearch.py ... leanfinder "The fiber of derived completion by a regular global
  section is the inverse limit of the repeated scalar multiplication tower"`:
  eight hits (ordinary `AdicCompletion` maps, `Hausdorffification`,
  `localCohomology`), none states this normalized sheaf-derived triangle.
- `msearch.py ... leansearch "Natural distinguished triangle from the repeated
  multiplication tower to a complex to derived completion by principal regular
  quotients"`: eight generic short-exact/cone/truncation triangle results, no match.
- `msearch.py ... loogle '"roos", "completion"'`: zero hits.
- `msearch.py ... grep 'completion|Roos' Algebra/Homology`: one unrelated
  idempotent-completion hit in `LeftResolution/Reduced.lean`.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for this node id, regular principal completion,
  scalar Roos and related names: no theorem states this triangle. Existing
  `RegularRoosKoszulUnit` proves a completeness/unit equivalence, and
  `PrincipalCompleteHeartKernels` cites the present mathematical lemma in its
  proof docstring; neither states it. The existing quotient-completion Model is
  reused, not duplicated. The new declaration names have no existing matches.

The inherited BLOCKED message concerned an unchanged stage-1 node. The live queue
lists this as stage 2 and the live node had no Lean record. There is no released
repair note for this item. The stage-2 handoff rule in brief-stage2 §0 applies.
No statement correction, new definition node or dependency-interface repair was
necessary.

## Second reading by NJ

Performed in this worker session, without spawning another agent, as the dispatcher
explicitly prohibits sub-agents. The maintainer's independent review is still required.
I reread the complete node and the complete module against each other. In particular,
I checked that positive indexing is n+1, that the first arrow contains multiplication
by a, that the unit is fixed on both Roos coordinates through Model.coordinates and
Model.unit_computes, and that naturality is on D(Mod(R)), not just on representatives.
I checked the full definitions of scalarTower, transpose, quotientTower, Model and
roosF, rather than treating their names as sufficient. No mathematical mismatch was
found. Compile diagnostics and final validation are recorded below after completion.

The main conclusion is transparently named `PrincipalCompletionFiber.FiberTriangle`,
with precisely the existential natural transformations and equations above. This
avoids expensive repeated elaboration on the scheme site; it imposes no extra
hypothesis. `firstEvaluation` is the actual `roosEval ... 0` chain map, named to
fix its codomain before specializing the site. All instance and universe parameters
are explicit or bound section variables; auto-implicit variables are disabled.

Validation: scompile.py compiled the full module in sandbox mode (14.7 s) and
library-module mode (8.7 s), with no errors or warnings. Earlier probes isolated
the elaboration cost to the unbundled site-specialized proposition; the transparent
FiberTriangle conclusion and explicit abbreviation universes resolved it without
changing its content or increasing any limit. All diagnostic files were removed.
