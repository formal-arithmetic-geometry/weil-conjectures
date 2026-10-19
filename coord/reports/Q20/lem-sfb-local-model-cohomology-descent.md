## Worker report

The module `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` states
`AlgebraicGeometry.ProEtale.localModel_cohomology_descent`, with one `sorry` and
no new definitions. The node's natural-language statement, dependencies and proof
are unchanged. The theorem docstring contains all six proof steps, including the
localized-site/coefficient identification, both exact-functor cohomology comparisons,
sheaf uniqueness for global vanishing, and the affine-local constructibility argument.

Hypotheses and objects, clause by clause:

- A quasi-compact scheme S is `(S : Scheme.{u}) [CompactSpace S]`. There is no
  quasi-separatedness, affineness, nonemptiness or separation assumption.
- The arbitrary commutative condensed ring Γ is
  `Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Γ]`
  and `[IsCommMonObj Γ]`. This is the existing internal-ring encoding, and does
  not restrict Γ to a continuous ring or a constant sheaf.
- R = Γ(*) is the dependency's `scalarRingObj Γ`: its underlying abelian group
  is literally evaluation at `Profinite.of PUnit`. Its multiplication and unit
  are the existing lax-monoidal evaluation construction. The coefficient ring
  Γ_T is exactly `condensedRingObj Γ T`, the pullback from the point.
- Q is in `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u+1})
  (condensedRingObj Γ S))`. Internal coefficient-module objects are the module
  category encoding used by the recorded local-model and constructibility
  dependencies. Their internal actions are precisely sectionwise module actions;
  this is not a different coefficient theory or a freely supplied equivalence.
- The finite covering family is
  `𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage S` with `[Finite 𝒱.I₀]`.
  Its members and maps are exactly `𝒱.X i` and `𝒱.f i`. A finite index type is
  equivalent to indexing by Fin n, without choosing an enumeration, and admits
  an empty family. `Scheme.proetalePrecoverage` includes the fpqc finite-refinement
  condition; joint surjectivity alone has not replaced covering.
- The integers are `(r s : ℤ) (hrs : r ≤ s)`.
- Each scalar complex is
  `K i : CochainComplex (Mod Ab.{u+1} (scalarRingObj Γ)) ℤ`.
  Internal modules in Ab are ordinary modules over R. The terms outside [r,s]
  are zero exactly by `hterms : ∀ i q, q < r ∨ s < q → IsZero ((K i).X q)`.
- `finiteConstantScalarExtension Γ (𝒱.X i)` is the already defined functor
  Γ_V tensor over the constant scalar ring with the constant sheaf of a scalar
  module. It is formed by `scalarConstant.mapMod` followed by actual extension
  of scalars along `scalarCoefficientHom`. No arbitrary map or replacement
  functor is supplied.
- Exactness of that functor is expressed by the three dependent instance
  binders `hadd`, `hlim`, `hcolim`: additive, preserving finite limits, and
  preserving finite colimits. Together these are exactly the node's assumed
  exactness (the exact-functor convention in its proof dependencies). They impose
  no flatness assumption on Γ beyond the assumed exactness on these members.
- `hmodel` is the specified derived isomorphism, using `Nonempty (A ≅ B)`:
  restriction of Q via `(CondensedRing.upperStar Γ (𝒱.f i)).mapDerivedCategory`
  is isomorphic to `DerivedCategory.Q.obj` of the termwise image of `K i`
  under `finiteConstantScalarExtension`. The pullback is the canonical
  coefficient-renamed exact inverse image, already proved exact in the upstream
  interface. On a pro-etale covering object it is localized restriction, as
  the coefficient-sections-localization dependency states. There is no new
  exactness assumption on restriction and no choice of a representing complex.
- `hfp` says `Mod.IsFinitelyPresented (scalarRingObj Γ) ((K i).homology q)`
  for EVERY i and integer q. This existing internal-module predicate is an
  isomorphism to the cokernel of `R^m → R^n` with finite m,n. For modules in
  Ab it is exactly the ordinary finite-presentation notion in
  `def-sc-finitely-presented-module` / `Module.FinitePresentation`, whose
  finite-generator/finite-relation definition was read. We use the existing
  internal encoding required by `finiteConstantScalarExtension`, without a
  duplicate finite-presentation definition and without substituting finite
  presentation over the sheaf coefficient ring.

Conclusions, clause by clause:

- The first conjunct says for EVERY integer q outside [r,s],
  `IsZero ((DerivedCategory.homologyFunctor _ q).obj Q)`.
- The second conjunct says for EVERY original i and EVERY integer q,
  `(CondensedRing.upperStar Γ (𝒱.f i)).obj (H^q Q)` is isomorphic to
  `(finiteConstantScalarExtension Γ (𝒱.X i)).obj ((K i).homology q)`.
  Thus both the original cover and its actual scalar cohomology objects are
  retained; the result is not just existence of some unrelated local models.
- The third conjunct supplies `HasFiniteConstantLocalModel Γ S (H^q Q)` and
  `IsConstantModelConstructible Γ S (H^q Q)` for EVERY q. The former is exactly
  a model on the single whole-scheme stratum S. The latter also retains the
  dependency's affine-local convention when S is not quasi-separated. The
  proof docstring explains restriction of the same scalar matrices to affine
  opens, with no extra qcqs assumption.
- The last conjunct is `constantModelBoundedConstructible Γ S Q`, membership
  in the existing full subcategory Dbc. Its definition is canonical-t-structure
  boundedness and constructibility of every cohomology module. No Tor-amplitude
  conclusion is asserted by this node.

Dependency declarations and sources read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff requirement).
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, with its existing
  imported ring-object framework: commutative condensed rings. The arbitrary
  internal Γ encoding is the one used throughout the recorded dependencies.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`,
  `coefficientPullbackIso`, `condensedPullbackHom`, `condensedPushforwardHom`.
  The published 51-module framework and `coord/pefw-upstream-framework.md` were read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
  The internal-module encoding used here is the same encoding as in the two
  local-model/constructibility dependency modules, and identifies with these
  sectionwise sheaf modules, as stated explicitly by the latter dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `.HomologySequence`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`,
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`,
  `Scheme.proetalePrecoverage`, `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `scalarSections`, `scalarRingObj`, `scalarConstant`, `scalarCoefficientHom`,
  `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover`,
  `finiteConstantLocalModel_iff_exists_cover`, and the scalar-matrix equivalence.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`;
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`:
  `Mod.IsFinitelyPresented`, its internal-module finite-free-cokernel formulation.
- `Sheaf.Paper.ConstantModelTorAmplitude` and its public defining module
  `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, its additive and finite-limit/finite-colimit
  preservation instances. The full definition and exactness proof were read.
- Proof interfaces imported: `SheafOfModules.overFunctor` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`;
  `SheafOfModules.localizedSystemExact` from
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`;
  `sfbCoefficientSectionsLocalization` from
  `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`;
  `weaklyEtale_stability` from `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`;
  `Functor.mapDerivedCategoryFactors` from
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
  `Functor.homologyFunctorIso` from
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
  `Scheme.FiniteLocallyClosedStratification` from the matching Sheaf module;
  `Topology.IsConstructible` from `Mathlib.Topology.Constructible`;
  `Precoverage.IsSiteForCoverings` from `Sheaf.CategoryTheory.SiteCoveringAxioms`.

Edge cases checked before writing:

- Empty S and an empty finite covering: no Nonempty index assumption. The sheaf
  axiom gives zero section modules for an empty covering. Local model
  hypotheses are vacuous and all cohomology vanishes, consistently with Dbc.
- Zero coefficient ring, zero modules and zero complexes: no nontriviality or
  positive-rank hypothesis. Finite presentations allow m=n=0.
- r=s, negative r,s and q=0: the interval is an inclusive integer interval, and
  the outside condition is `q < r ∨ s < q`, not a natural-number truncation.
- Empty members of a nonempty cover do not create a false nonzero hypothesis.
- A quasi-compact non-quasi-separated S is allowed. The conclusion uses the
  existing affine-local constructibility convention, with its argument retained
  in the docstring. There is no hidden quasi-separatedness restriction.
- An arbitrary (possibly non-Noetherian) scalar ring is allowed. Finite
  presentation of every scalar cohomology module is an explicit hypothesis;
  it is not inferred falsely from boundedness of the scalar complex.
- Scheme universe u, coefficient and scalar-module universe u+1 follow the
  published pro-etale framework. No equality of site object/Hom universes is
  imposed, and no special coefficient carrier or restriction on Γ is introduced.

Searches for an existing statement (2026-10-18):

- `msearch.py ... leanfinder`: "Cohomology of a sheaf complex descends from
  bounded scalar models on a finite pro-etale cover with exact scalar extension".
  Eight hits, chiefly `LightCondMod.ofSheafLightProfinite`, `Sheaf.H` and
  `Sheaf.cohomologyPresheaf`; none states this theorem.
- `msearch.py ... loogle`: `CategoryTheory.Functor.mapDerivedCategory,
  DerivedCategory.homologyFunctor`. Zero hits.
- `msearch.py ... grep`: `localModel|cohomology.*descent|finiteConstant` in
  Mathlib/CategoryTheory. Zero hits.
- `msearch.py ... leansearch`: "bounded scalar complexes on a finite cover give
  bounded constructible cohomology sheaves by exact scalar extension". Eight
  hits on scalar extension/restriction, including
  `Module.FinitePresentation.isLocalizedModule_mapExtendScalars` and
  `SheafOfModules.restrictScalars`; no match for this combined sheaf theorem.
- `rg` for `localModel|local_model|cohomology.*descent|` the item id in the
  upstream WeilConjectures tree and side `lean/Sheaf` finds unrelated etale
  descent, perfect-complex and geometric local-model statements. The exact
  item id does not occur upstream (`grep -rn` also returns no match).
- `rg` for `finiteConstantScalarExtension` finds the existing local-model
  definition and its pullback consumer; these are reused. Searching the
  proposed full theorem name in Mathlib, upstream, side Lean and
  `dag/lean_names_upstream.json` gives no collision.

Source check: the current main-20261015 paragraph (2) was opened; it is the
motivation, not an attribution of the expanded proof to the blueprint. Stacks
homology.tex lemma-exact-functor (010N), derived.tex
lemma-right-derived-exact-functor (015F), and sites-modules.tex
definition-localize-ringed-site (03DH) were opened. The six-step proof is the
node's recorded agent-written expansion.

Validation: `scompile.py Q20 lem-sfb-local-model-cohomology-descent` compiled
the sandbox and library module with no errors or warnings. No proof was filled.
No statement dispute, source correction, new node or dependency repair was needed.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
