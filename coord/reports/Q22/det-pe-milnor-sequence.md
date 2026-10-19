## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence` states all three clauses
of `det-pe-milnor-sequence` as
`AlgebraicGeometry.Scheme.ProEt.milnor_sequence`, with one postponed proof. Its
four helper declarations are transparent abbreviations for cohomology and
single-complex towers and the existing cokernel construction and its canonical
map. They construct real data and contain no postponed proofs. No other DAG node
is stated, and the item's natural-language statement and dependency lists are
unchanged.

Source read: current blueprint main-20261015,
`sec-proetale-coefficients/sk-prop-pe-milnor/det-pe-milnor-sequence.md`, all three
numbered clauses. Also read the entire DAG proof, including the cone sign and
naturality explanation, and each statement dependency's statement, recorded
interface, source signature and documentation.

Hypotheses and objects:

- `X : Scheme.{t}` is the arbitrary scheme. `topology X` is Mathlib's topology on
  the unchanged small site `X.ProEt` (object universe `t+1`, morphism universe `t`).
- `R : Sheaf (topology X) RingCat.{max u (t + 1)}` is an arbitrary ring sheaf;
  commutativity, nonzero rings and geometric restrictions are not assumed.
  `ringedSiteModules.{max u (t + 1)} R` is the recorded general-site module
  category, transparently Mathlib `SheafOfModules`. The universe contains the
  site and may be enlarged independently by `u`.
- `K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules ... R) ℤ` is an arbitrary
  unbounded tower. Its successor arrow is
  `K.map (homOfLE (Nat.le_succ n)).op`.
- The existing `towerTransitionEndomorphism` is exactly `1-T`, where
  `towerProductShift` has nth coordinate `π_(n+1) ≫ t_n`.
  The existing `WeilConjectures.integralOperationsRoos K` is
  `CochainComplex.mappingCocone` of that endomorphism, definitionally the mapping
  cone shifted by `-1`. Its products are products of complexes, computed
  termwise. The existing `integralOperationsRoosMap` is the product map on both
  summands, followed by the shift; it is not an arbitrary comparison morphism.

Clause-by-clause correspondence:

1. `q : ℤ` quantifies every cohomological degree. `milnorCohomologyTower K q`
   is precisely `K ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q`,
   including the transition maps. `milnorTowerCokernel` is the categorical
   cokernel of the existing `1-T` on the product in the sheaf category, not a
   sectionwise cokernel. `limit (milnorCohomologyTower K q)` is the recorded
   sheaf inverse limit. The simultaneous families `a K`, `b K` have exactly the
   three displayed endpoints. `∃ h, (ShortComplex.mk (a K) (b K) h).ShortExact`
   states zero composite, exactness at the middle, monicity at the left and
   epicity at the right. For every tower morphism `f`, the next conjunct gives
   both naturality squares. The left square uses the actual cokernel map of
   the product of the induced maps on cohomology; the right uses `limMap`.
   The middle uses cohomology of the actual strict Roos map.
2. `milnorSingleTower M` is `M` composed with the existing
   `HomologicalComplex.single _ (ComplexShape.up ℤ) 0`. Thus the source's
   definition `R^p lim M := H^p(Rlim M)` is rendered by
   `(integralOperationsRoos (milnorSingleTower M)).homology p`. The isomorphisms
   `e₀ M` and `e₁ M` identify it in degrees 0 and 1 with `limit M` and the
   cokernel, respectively. The first conjunct gives `IsZero` for every integer
   `p` distinct from both 0 and 1. The second conjunct records compatibility of
   both identifications with tower morphisms. No separate assertion about
   abstract right derived functors is inserted: the node defines this notation
   as cohomology of the cone.
3. The last conjunct uses exactly the same `a K` and `b K` as clause 1.
   Precomposing `a K` with `(e₁ (milnorCohomologyTower K (q-1))).hom` changes its
   left endpoint to `R^1 lim H^(q-1)(K_n)` as defined in clause 2. The displayed
   short complex is short exact. Its naturality is the two squares from
   clause 1 combined with the naturality of `e₁` already included above.

Recorded dependencies used:

- `sk-def-pe-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` in
  `Sheaf.CategoryTheory.RingedSiteModules`, retaining its Mathlib abelian
  structure.
- `def-weil-abstract-derived-category`: the existing complex/cohomology,
  cone and shift infrastructure imported by
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; cohomology of the displayed
  representing complex is used directly. No new derived category is chosen.
- `def-pur-sheaf-inverse-limit`: `CategoryTheory.Limits.limit` and `limMap`,
  from `Mathlib.CategoryTheory.Limits.HasLimits` and its imports; the module
  sheaf limits instances compute it sectionwise.
- Stated proof interfaces are imported without `public`:
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` for
  `lem-sf-derived-homology-long-exact`, and
  `Sheaf.AlgebraicGeometry.ProEtaleProductsExact` for `det-pe-products-exact`.
  `det-pe-products-derived` has no recorded declaration in the checkout and is
  therefore not imported or restated; it is a proof dependency only.

Additional existing utilities read and reused, rather than reconstructed:
`WeilConjectures.integralOperationsRoos` and
`WeilConjectures.integralOperationsRoosMap`, in
`Sheaf.Paper.IntegralOperationsWellDefined`; and
`CategoryTheory.towerTransitionEndomorphism` and
`CategoryTheory.towerTransitionEndomorphism_natural_backward`, in
`WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism` (current
published source read using `scompile.py --source`). The former module's Roos
section is generic in any abelian category with countable products, with no
prime, field or completed coefficient arguments. The helper cokernel map uses
the latter naturality theorem for its commutative square. Large-coefficient
sheafification already supplied by the imported library is used, with the
inapplicable generic successor-universe instance disabled for elaboration.
There is no file-local instance or extra mathematical hypothesis.

Edge cases checked: zero ring sheaves, zero towers and the empty scheme are not
excluded by any binder or instance. The index begins at 0 and is infinite;
positive-index conventions are reindexed by n+1. All degrees are integers,
including negative degrees and q=0 (whose left tower is H^-1). The module-tower
vanishing quantifier includes negative p as well as p≥2 and excludes exactly
0 and 1. For a constant identity tower, the endpoint formulas give the usual
limit and vanishing cokernel; for zero transitions both kernel and cokernel of
1-T vanish. No boundedness, surjectivity of transitions or K-injectivity
hypothesis was added. The sheaf limits and cokernels retain their categorical
meaning.

Searches actually run:

- msearch.py leansearch: `Milnor exact sequence for a sequential tower of
  complexes of sheaves of modules` returned Mayer--Vietoris short exactness,
  Ext exact sequences, and the general `ShortComplex.ShortExact.mk`, not this
  statement.
- msearch.py leanfinder: `Milnor short exact sequence for cohomology of the cone
  of one minus shift of a product tower of complexes` returned the general
  mapping-cone long exact sequence and derived short-exact triangles (8 hits),
  not a Milnor theorem for these sheaves.
- msearch.py loogle: `"mappingCone", "triangle"` returned 12 general cone
  triangle declarations, not the three-clause statement.
- msearch.py grep: `Milnor|Roos|derivedLimit|homotopyInverseLimit` returned only
  Mathlib's unrelated PoincareConjecture file.
- Direct rg with the same concepts in upstream WeilConjectures and side Sheaf
  found `CategoryTheory.milnor_shortExact` in
  `Sheaf.CategoryTheory.Triangulated.MilnorSequence`. Its full signature is
  specialized to abelian groups and does not state the module-sheaf or
  degree-zero-tower clauses here. The search also found and led to reuse of
  the exact generic strict Roos construction in IntegralOperationsWellDefined.
  Node-id and newly chosen declaration-name searches in upstream, Mathlib and
  the side project found no exact existing theorem or declaration clash.

No statement correction or disputed mathematical claim is needed. All theorem
proofs in this delivery are `sorry`, and the sole such theorem has the complete
natural-language proof plan in its docstring.

## Second reading by Q22

Independent second reader, 2026-10-16. I read the node and its two proof steps,
the actual Lean file, all four statement dependency nodes and their interfaces,
and the blueprint item, unit statement, unit proof and chapter introduction.
The item's source is the blueprint Markdown, not a Stacks lemma with the same
title. I additionally read the cited Stacks cone, distinguished-triangle,
cohomology and derived-category passages in `derived.tex` (014E, 014Q, 05RS,
05RU), and the module-sheaf and sectionwise-limit interfaces below. Neither the
blueprint context nor these sources impose a geometric finiteness assumption.
There is no repair note for this item and no `statement_change` to audit.

My object/hypothesis/conclusion checklist, with its Lean rendering:

1. An arbitrary scheme X and its small pro-etale site: `(X : Scheme.{t})`
   and `topology X`. I opened Mathlib `Sites/Proetale.lean`: `Scheme.ProEt`
   is weakly etale schemes over X, with all over-morphisms; its `precoverage`
   and `topology` use the quasi-compact covering condition. This is the
   `sk-def-pe-site` match, not the big site or the etale site. Verdict: exact.
2. An arbitrary sheaf of rings R and its module sheaves: the only other
   theorem binder is `R : Sheaf (topology X) RingCat.{max u (t + 1)}`.
   `ringedSiteModules` in the recorded dependency module is literally
   `SheafOfModules.{v} R`. I opened Mathlib's structure, `Hom`, abelian
   instance, and limits instances: objects have module presheaves with the
   abelian-group sheaf condition, morphisms are linear natural maps, kernels
   and limits are sectionwise, and cokernels are categorical sheaf cokernels.
   No commutativity, field, Noetherian, nonzero or constant-ring hypothesis is
   present. Verdict: exact, using the recorded category rather than a copy.
3. Any unbounded tower of complexes, indexed from zero, with transitions
   t_n: `K : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules ... R) ℤ`.
   Its successor arrow is `K.map (homOfLE (Nat.le_succ n)).op`; the functor
   includes all composites. `milnorCohomologyTower K q` composes this whole
   diagram with `HomologicalComplex.homologyFunctor`, retaining transitions.
   Verdict: exact; no boundedness, K-injectivity or surjectivity restriction.
4. T has nth coordinate t_n after projection n+1, and Rlim is Cone(1-T)[-1].
   I fetched and read the current published `TowerTransitionEndomorphism`
   with `scompile.py --source`: `towerProductShift` is the specified product
   lift and `towerTransitionEndomorphism` is its difference from the identity.
   I read the generic Roos section of `IntegralOperationsWellDefined`:
   `integralOperationsRoos` applies Mathlib `mappingCocone` to that very
   endomorphism on the product of complexes. Mathlib defines `mappingCocone`
   as `mappingCone` shifted by -1. The section's only category requirements
   are abelianness and countable products; its earlier prime and field
   variables do not occur. `integralOperationsRoosMap` is the shifted cone
   map of the two product maps. Verdict: the actual construction and its
   actual functorial map are used, not an arbitrary homotopy-limit object.
5. Clause 1, every degree and all three endpoints: `∀ q : ℤ`, followed by
   simultaneous `a` and `b` for every K. Their types are respectively
   coker(1-T on product H^(q-1)) to H^q(Roos K), and H^q(Roos K) to
   `limit (milnorCohomologyTower K q)`. The helper cokernel unfolds to
   Mathlib `cokernel`; it is not a cokernel of sections. The conjunct
   `∃ h, (ShortComplex.mk (a K) (b K) h).ShortExact` says zero composite,
   mono, exactness at the middle and epi, hence includes both zero endpoints.
   Verdict: every part of the displayed short exact sequence is present.
6. Clause 1, naturality: for every `f : K ⟶ L`, the next conjunct gives
   both commuting squares. I checked the map of the left endpoints:
   `milnorTowerCokernelMap` is `cokernel.map` of the componentwise product
   maps; its square follows from the existing transition naturality theorem
   in the correct orientation. The middle map is homology of the strict
   Roos map; the right map is `limMap` of the cohomology transformation.
   Verdict: natural in the whole tower, not only objectwise exactness.
7. Clause 2, modules in degree zero: `milnorSingleTower M` is composition
   with Mathlib `HomologicalComplex.single ... 0`. The simultaneous
   isomorphisms `e₀ M` and `e₁ M` have sources H^0 and H^1 of its Roos
   complex and targets `limit M` and `milnorTowerCokernel M`. The first
   conjunct gives `IsZero` in every integer degree other than 0 and 1.
   The second conjunct spells out the natural identifications for every
   module-tower morphism. The source defines R^p lim as this cohomology, so
   an abstract right-derived-functor construction is not a missing premise
   or conclusion here. Verdict: all three cases are rendered correctly.
8. Clause 3, the same sequence rewritten: the final conjunct precomposes
   `a K` with `(e₁ (milnorCohomologyTower K (q - 1))).hom` and retains
   the identical `b K`. Its left object is therefore precisely the defined
   R^1 lim of the H^(q-1) tower. It asserts short exactness; its two
   naturality squares follow from the already asserted squares for a, b
   and e₁. Verdict: the consequence concerns the sequence of clause 1,
   rather than a separately chosen unrelated sequence.

Dependency verification: the cohomology of a representative agrees with the
recorded abstract derived category by Mathlib
`DerivedCategory.homologyFunctorFactors`; I opened its signature as well as
`DerivedCategory`, `Q` and `HasDerivedCategory`. The inverse limit uses the
recorded Mathlib `limit`, whose sheaf-module evaluation preserves limits;
positive indexing in that dependency is reindexed by n+1. For the proof
imports I opened `HomologySequence.δ`, `exact₁`, `exact₂`, `exact₃`, and
`ProEt.products_exact`. They have the required general abelian-category and
arbitrary ring-sheaf interfaces, respectively. `det-pe-products-derived` is
still without a recorded module, so omitting its proof import is appropriate;
it is not needed to type this statement. The existing Roos helpers supply
real cone data; their named naturality proof is not data chosen from an
underdetermined existence statement. No new definition node or dependency
repair is required by this delivery.

Edge cases: X may be empty, R may be the zero ring sheaf, K or M may be
zero, transitions may be zero or identities, and q may be 0 or negative.
The p quantifier includes all negative degrees and all p at least 2, and
excludes exactly 0 and 1 from vanishing. The tower index is the fixed
nonempty countable type ℕ, so an empty indexing set is not a case of this
node. Its initial level 0 is included. No characteristic is specified or
excluded. Site objects remain in t+1 and arrows in t; `max u (t+1)` supplies
an arbitrarily enlarged coefficient/module universe without equating the
site universes. The needed abelian and countable-limit instances are
inferred, not extra hypotheses of the theorem. The instance attribute
selects the already imported large-coefficient sheafification infrastructure.

Independent searches, using different formulations from the first worker:

- LeanSearch through `msearch.py`: "The cohomology of a sequential derived
  inverse limit fits into the natural Milnor short exact sequence" returned
  eight inverse-system, sequential-product and group-cohomology results;
  none states this theorem.
- LeanFinder through `msearch.py`: "cohomology of sequential homotopy inverse
  limit of complexes in abelian category with exact products kernel cokernel
  short exact sequence" returned eight HomComplex, group-cohomology and
  factorization results; none is a match.
- Loogle through `msearch.py`: `"mappingCocone"` returned twelve mapping
  cocone constructions and triangle declarations. I opened its definition;
  these supply the construction, not the three-clause theorem.
- Direct `rg` searches in Mathlib, upstream `WeilConjectures` and project
  `lean/Sheaf` for Milnor, Roos, derivedLimit and homotopyInverseLimit found
  the abelian-group Milnor theorem and generic Roos/strict-tower machinery.
  I read `CategoryTheory.milnor_shortExact`: its coefficient category is
  `AddCommGrpCat` and it lacks this module-tower calculation. I also read
  `roosComplex_quasiIso`, `ringedStrictTowerHomotopyLimit` and the Roos
  acyclic-resolution interface; none states the present theorem. Searches
  for all five new declaration names, including `dag/lean_names_upstream.json`,
  found no collision. The existing generic Roos construction is already
  reused, and the four helpers only name its endpoints and induced maps.

H5/H6/H8/H9: the helpers contain real data, and the sole theorem is left
entirely `sorry` as required for stage 2. Its proof docstring follows both
node proof steps: cone exact sequence; products/cohomology and the 1-T
coordinate formula; kernel as inverse limit; naturality including the cone
signs; the two-term degree-zero calculation; and substitution for clause 3.
All five declarations have source/blueprint docstrings. All universe and
term variables are explicitly bound, `autoImplicit` is false, and no line
exceeds 100 characters. I checked programmatically that `lean.statement`
equals the full theorem signature verbatim and that `lean` is the only
changed node field.

Mismatches found: none. I preserved the Lean and node as written and added
this independent reading. Compilation and delivery preflight are recorded
below after running the required wrappers.

Validation: the second reader ran `scompile.py Q22 det-pe-milnor-sequence`
on the sole delivered module. Both its sandbox check and library-module
compilation passed, with no errors or warnings. No global build was run.
The required `deliver2.py Q22 det-pe-milnor-sequence --no-push` then printed
`OK (dry run)` and confirmed that the delivery passes preflight and compiles.
