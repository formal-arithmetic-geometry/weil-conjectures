## Worker report

The module `Sheaf.Paper.IntegrationTransposeBaseChange` states the ordinary unbounded
small-etale integration-transpose assertion. Its four postponed theorems cover naturality,
unique counit normalization, transport of the actual adjunction (including both actual-map
triangles), and base change with conditional invertibility. All proofs are `sorry`.
Seven helper definitions contain explicit data, with no postponed data choices. The
naturality field of `integrationTransposeNatTrans` refers to the named naturality theorem;
its components are the explicit Hom transposes, so this does not hide any choice of data.

The previous worker's reported refusal confused a stage-1 landing with a stage-2 statement.
The current node has `reviewed.result = pass` from Q63, but no `lean` record or
`reviewed_lean`, and Q63's report explicitly says no Lean was written. The sandbox was empty.
This delivery adds the first Lean statement; it neither re-splits that DAG proof nor changes
its mathematical statement. There is no repair note for this item.

Hypothesis-by-hypothesis correspondence:

- A finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  Schemes have universe `u`, as required by the recorded ModuleCat-valued small-etale API.
  This is the existing coefficient universe, not a new size equality hypothesis.
- The four schemes are `X X' Y Y' : Scheme.{u}`. The node's Noetherian hypotheses are
  `[IsNoetherian X]`, `[IsNoetherian Y]`, `[IsNoetherian Y']`. The explicit instance
  `[IsNoetherian X']` is redundant: X' is of finite type over the Noetherian Y', by
  base change from the finite-type f. Thus every square in the node is covered.
- The morphisms are `f`, `f'`, `g`, `g'` and `sq : IsPullback g' f' f g`.
  This permits arbitrary Noetherian-source base change g, with no flatness or finite-type
  hypothesis on g. Finite type of f is `[LocallyOfFiniteType f]` and `[QuasiCompact f]`;
  separatedness is `[IsSeparated f]`, and compactifiability is `[HasCompactification f]`.
  The explicit `[HasCompactification f']` and `[QuasiCompact f']` are likewise inherited
  from f by the Cartesian square; choices of compactification do not restrict it.
- Ordinary D(T_et,A) is exactly the dependency's `DerivedCategoryModule A T`.
  `rightDerivedLowerShriek (ModuleCat A) f` is F, and the analogous functor for f' is F'.
  The existing chosen-compactification definition is Di_! followed by Rr_*.
- `R`, `R'` are arbitrary actual right adjoints, specified with `adj : F ⊣ R`,
  `adj' : F' ⊣ R'`; units and counits are these adjunctions' actual `.unit` and `.counit`.
  They are not replaced by right adjoints chosen from an unrelated existence assertion.
- Every f*, g*, g'* in the file is `.leftDerivedFunctor` of the existing `upperStar`.
  The canonical `leftDerivedUpperStarIsoMapDerivedCategory` identifies it with the exact
  termwise inverse image. This is a coordinate identification, not an added hypothesis.
- `integrationExchangeIso A sq` is C: it conjugates the recorded proper/open exact
  exchange `unboundedEtaleCompactSupportBaseChange` by precisely those identifications.
  Its inverse exists by the existing `unboundedEtaleCompactSupport_baseChange` theorem;
  no invertibility hypothesis is imposed on the caller, and no arbitrary map is supplied.
- W, W', and the isomorphism l are the displayed `W`, `W'`, `l` binders. The trace maps
  `t`, `t'` target the existing derived tensor unit, i.e. the constant A complex.
  The hypothesis `ht` is `C_W ≫ F'.map l.hom ≫ t' = g*.map t ≫ unitIso.hom`.
  The last canonical unit identification is the node's understood A_Y' identification.
- The projection map is the already landed `compactProjectionMapCoeffFirst A f K W`.
  It is built from the proper counit map, inverse open tensor comparison, and canonical
  symmetries giving the coefficient-first ordering. `hP` and `hP'` assert exactly its
  invertibility for every input on each base. They impose no condition on W itself.

Clause-by-clause correspondence:

- G0 is `integrationTwistedFunctor A f W`, the composite of f* and tensor-on-the-right
  by W. Its data and maps use `derivedTensorRight`, not a new tensor structure.
- c_K is `integrationCounit A f W t hP K`: the inverse of that exact projection map,
  `derivedTensor.obj K` applied to t, and the existing `derivedTensorRightUnitor`.
  `@inv` uses the supplied hP K explicitly. Thus it is precisely the prescribed c.
- gamma_K is `integrationTranspose A f R adj W t hP K`, i.e. `adj.homEquiv` of that c.
  The primed gamma uses the very same definitions specialized to f', R', adj', W', t'.
- a_K is `(integrationTensorBaseChangeIso A sq W W' l K).hom`. Its three factors are
  the recorded monoidal inverse-image comparison, inverse canonical pullback-square
  isomorphism in the first tensor argument, and l in the second argument. Each factor
  is an actual isomorphism. No free tensor comparison is a hypothesis.
- e_K is `integrationExceptionalExchange A sq R R' adj adj' K`, defined by `adj'.homEquiv`
  of `C.inv.app (R.obj K) ≫ g*.map (adj.counit.app K)`.
- The first conjunct of `integrationTranspose_baseChange` is
  `g'*.map gamma_K ≫ e_K = a_K ≫ gamma'_(g*K)`, in Lean's diagrammatic order.
  Its second conjunct says that, if every gamma and every gamma' is invertible,
  the specified e_K is invertible. It does not assert that arbitrary mates preserve isos.
- `integrationTranspose_naturality` states naturality for every K, L, v : K ⟶ L.
  It applies separately to both families. `integrationTransposeNatTrans` bundles that
  precise family; its components remain the specified transposes.
- `integrationTranspose_unique` says `F.map b ≫ epsilon_K = c_K ↔ b = gamma_K` for
  every candidate b. Substituting b = gamma_K yields the normalization, and the reverse
  implication proves uniqueness, without an extra existence assumption.
- `integrationTranspose_transport` takes a natural isomorphism gamma with exactly that
  natural transformation as its hom. Its transported adjunction is the concrete Mathlib
  construction `adj.ofNatIsoRight gamma.symm`. The first group of equations gives its
  counit as `F.map gamma_K ≫ epsilon_K` and as c_K. The next group gives its unit as
  `eta_M ≫ gamma.inv.app (F.obj M)`. Its last two groups are exactly the left and right
  triangle equations written on those actual maps, not merely an existential adjunction.
- Every input throughout is in the unbounded derived category. No boundedness,
  constructibility, finite-Tor-amplitude, invertible-characteristic, or pro-etale condition
  occurs in the theorem or helper signatures.

Dependency declarations read and used (including transitive public imports):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `DerivedCategoryModule` from its
  public Coefficients import; the recorded `DerivedCategory.torsionCohomology` is not a
  hypothesis of this node.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleCompactSupportBaseChange`, `unboundedEtaleCompactSupport_baseChange`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `mateEquiv_counit`; objectwise
  transposes are the corresponding `Adjunction.homEquiv`. These supply the mate convention.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification` ensures the adjunctions exist;
  the statement preserves any supplied actual adjunctions.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `isIso_proper_projection_formula_reordered`, the proper factor of the projection.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionIso`, its open factor.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`,
  `derivedTensorRight`; `TensorStructure`: `derivedTensorRightUnitor`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`; the same exact inverse image is realized by `upperStar`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField` and its existing
  `WeilConjectures.Compactification.Defs` import: `HasCompactification`, `Compactification`.
  The separate field-case existence clause is not assumed for arbitrary g.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarTensorIso`, `leftDerivedUpperStarTensorNatIso`,
  `leftDerivedUpperStarUnitIso`, `leftDerivedUpperStarIsoMapDerivedCategory`;
  the public composition interface supplies `derivedSquareUpperStarIso`.
- The already landed proof dependency `lem-asd-compact-projection-exchange`
  supplies `compactProjectionMapCoeffFirst_baseChangeMap` only as the geometric input to
  proof step 2. The map definition itself is now recorded independently by
  `def-pur-coefficient-first-compact-projection` with `existing: true`.
- Remaining proof leaves are `Adjunction.eq_unit_comp_map_iff`,
  `Adjunction.homEquiv_naturality_right_square_iff`, `Adjunction.mkOfHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`, and `mateEquiv_counit` above.
  The proper projection-map dependency is imported by the projection modules already.

The complete proof is distributed into the docstrings corresponding to the node's six
steps: projection naturality and Hom transpose; projection/exchange followed by trace;
comparison of the two actual transposes; conditional inverse cancellation; transport of
Hom bijections; and the two explicit triangles. All four sorry declarations belong to
this one node and appear in `lean.declarations`. The repair adds a definition-only DAG attachment to an existing map, described below.
The natural-language item statement and its proof are unchanged.

Edge cases checked before writing: g = identity (comparison reduces to the identity
pullback identification), f = identity (ordinary tensor/trace transpose), W = W' = 0 and
zero inputs (zero transposes, with invertibility still conditional), empty schemes, and
the zero coefficient ring. In none is a trace assumed invertible. Inverse symbols only
refer to hP, canonical comparison isomorphisms, or the explicitly supplied gamma iso.
Arbitrary unbounded W and K remain valid input types. The Noetherian pullback instances
above exclude no node case. The geometric square comparison has orientation g'* f* to
f'* g* after its inverse, as checked against the full upstream signature.

Searches actually made:

- `msearch.py` LeanFinder: "Projection formula base change integration trace adjunction
  transpose naturality" returned linear/algebraic trace base-change and transitivity
  facts (`LinearMap.trace_baseChange`, `Algebra.trace_trace`, etc.), not this statement.
- `msearch.py` Loogle: `CategoryTheory.Adjunction, "ofNatIsoRight"` returned
  `Adjunction.ofNatIsoRight` and its unit/counit/Hom-equivalence formulas; these are
  constituent transport operations, not the integration/projection/exchange assertion.
- `msearch.py` Mathlib grep: `integration.*[Tt]ranspose|[Tt]ranspose.*integration` gave
  no hits. The tool's search log retains the actual results.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` with that same pattern and the exact
  item tag found specialized pro-etale/vector integration uses and TensorTraceTranspose,
  not the present arbitrary ordinary-etale square theorem. The exact blueprint-tag search
  gave no module for this item. I read CompactProjectionExchange, the upstream
  LowerShriekProjectionExchange and TensorTraceTranspose to distinguish the existing
  canonical operations from this assertion: the first two give the projection square;
  the last restricts to specialized coefficient/constructibility data and a tensor mate.

No statement fault or STATEMENT-DISPUTED issue was found. The mistaken prior stage label
was resolved from the node and Q63 report; it did not justify abandoning the stage-2 work.


## New nodes

`def-pur-coefficient-first-compact-projection` records the exact existing definition
`AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst` in
`Sheaf.AlgebraicGeometry.CompactProjectionExchange`, line 136, with `existing: true`.
It introduces no module or duplicate definition. The finite commutative coefficient ring
is the surrounding `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`; its schemes, morphism,
compactification and arbitrary inputs are the declaration's `X`, `Y`, `f`,
`[HasCompactification f]`, `Q`, `M`. Its source and target are respectively
`Q ⊗ᴸ Rf_!M` and `Rf_!(Lf*Q ⊗ᴸ M)`. The three factors of its body are exactly the source
signed symmetry, `((projectionMap _ f).app M).app Q`, and `Rf_!` of the target signed
symmetry. The upstream `projectionMap` specializes `projectionMapOfCompactification` to
the chosen compactification; that map uses the proper counit projection, inverse open
comparison and pullback composition, in precisely this order. No exchange theorem is
used in this construction. In particular no assertion about invertibility was added.
The identity, zero-object, empty-scheme and zero-ring cases are all allowed by this body.

Searches for this definition were run afresh: LeanSearch query
"coefficient first compact support derived projection map" returned eight unrelated
support/calculus or presentation facts, starting with `HasCompactSupport.deriv`;
LeanFinder query "canonical projection map tensor compact support direct image coefficient first"
returned eight unrelated compactly-supported-functions/direct-sum tensor facts, starting with
`CompactlySupportedContinuousMap.compLinearMap`; Mathlib grep
`compactProjectionMapCoeffFirst|projectionMapOfCompactification` returned no hits.
The exact `rg` over `lean/WeilConjectures` and `lean/Sheaf` found the existing definition
and its consumers, and the upstream right-coefficient construction. The DAG grep and
`blueprint_refs.py search coefficient-first` found no independent exact definition node.
The broader blueprint projection search was also read: `sk-def-sf-exchanges` gives the
right-coefficient convention. `def-pur-finite-site-tensor-projection` instead attaches
its projection to a pro-etale coefficient-specialized interface and lies downstream of
this item. These are not exact independent attachments for the present general map.
The ancestor command returns `cor-pur-vector-bundle-purity`, recorded with this item
prepended to `via`. The search results are recorded in the new node and search log.

## Second reading by NU

Repair of L's H2 return at immutable head `a10a832a7d8f`: the saved packet's first dry run
passed mechanically, but the returned dependency classification still needed repair.
I read the item statement and `IntegrationTransposeBaseChange.lean` again, checked the
unchanged hypotheses and clauses against the correspondence above, and inspected the
full body of `compactProjectionMapCoeffFirst` plus the upstream compactification map.
The four theorem statements and seven helper constructions retain exactly their saved
signatures and bodies. The only item changes against current main are its Lean record
and addition of the new definition node to `stmt_deps`. In particular the theorem
`lem-asd-compact-projection-exchange` was removed from the saved packet's `stmt_deps`
and retained verbatim in `proof_deps`. Its conclusion is used only in proof step 2.
The new node records the existing map separately, following the return's existing:true
alternative. No dependency module, statement correction, new sorry or new data is needed.
Each cited prerequisite was checked for a path back to this item; the new definition's
prerequisites do not introduce such a path. The same-module import remains public because
it supplies the definition, while its theorem remains a proof dependency in the DAG.
This is the worker's self-check; the maintainer performs the independent review.
