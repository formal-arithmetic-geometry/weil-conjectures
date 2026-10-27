## Worker report

The item is stated by `AlgebraicGeometry.AlgebraicSpace.cohomology_powers_rees_finite`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceCohomologyPowersReesFinite`. It asserts
existence of the specified ideal-power sheaves and actions and finite generation for
that precise Rees action. Its only postponed proof is this named theorem, with the
four source proof steps in its docstring. No data definition uses `sorry`.

The helper definition node records `IdealPowerReesCohomologyData`, a type of fully
normalized presentations of the objects the item introduces. The theorem constructs
such a datum; no such datum is assumed. No selection from a mere existence theorem
is made. The datum records maps by their exact section formulas, so it does not
replace canonical multiplication or the cohomology action by arbitrary maps.

Hypotheses and clauses, checked individually:

- A commutative Noetherian ring: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
  No nonzero-ring or characteristic assumption appears.
- An arbitrary ideal: `I : Ideal A`, without finite-generation as a separate hypothesis.
- The proper map to the affine base: `X : AlgebraicSpace (Spec (CommRingCat.of A))`,
  `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A))))`, `hf : MapIsProper f`.
  This is a map of spaces over Spec A to its representable terminal space. Its chart
  structure maps are exactly the maps to Spec A already in X. `MapIsProper` is the
  conjunction separated, finite type and universally closed, not a curve condition.
- F is a sheaf on the existing small etale ringed site: `F : X.Modules`.
- Quasi-coherence: `hF : F.IsQuasicoherent`, the recorded Mathlib predicate.
- The other coherence clause: `hfinite` quantifies over every chart T, assuming that
  its scheme is affine and its coordinate ring `Γ(T, ⊤)` is Noetherian, and asserts
  `Module.Finite Γ(T, ⊤) Γ((X.schemeRestriction T).obj F, ⊤)`. Quasi-coherence identifies
  this restriction on an affine with the sheaf associated to its module of sections.
  This is precisely finite generation on every Noetherian affine etale chart; no
  chosen chart or atlas, global finite-generation hypothesis, or extra Noetherianity
  assumption on X has been added.
- Fixed nonnegative cohomological degree: `q : ℕ`, including zero.
- `J^r F` and its inclusion: the datum has `obj r`, `inclusion r`, `injective r T`, and
  `range_eq r T`. The range is exactly the sections locally in the O-module span of
  `a_T • t`, for `a ∈ I^r`. Expanding products of local generators of `I O_X` gives
  the node's locally generated J-power product. This explicitly includes r=0. Since
  1 belongs to I^0, its inclusion has all of F as range, identifying this power with F.
  Local membership is stated using an actual covering sieve and every arrow in it,
  not a global sectionwise image or a quotient of global sections.
- Pullback of base scalars: `idealPowerChartScalar X T`, used without redefinition,
  is the actual coordinate map through the chart's morphism to Spec A.
- The O-linear maps lambda: `multiply k r a : obj r ⟶ obj (r+k)` is a morphism of
  module sheaves. `multiply_inclusion` is exactly the displayed equality after
  inclusion in F on every chart and every section. Injectivity fixes the map uniquely.
  The ring elements are the actual subtype `↥(I^k)`, with no arbitrary coefficient set.
- Actual additive-sheaf cohomology: `idealPowerCohomologyFunctor X q` is restriction
  along the published small affine etale model, then Mathlib `SheafOfModules.toSheaf`,
  then Mathlib `Sheaf.functorH`. The restriction model has the published equivalence
  of module categories and actual regular-function section rings. Cohomology of
  underlying additive sheaves is invariant under this site comparison. No substitute
  functor is quantified over. `HasExt.standard` fixes an adequate size u+1 explicitly,
  adding no assumption or equality between the site and coefficient universes.
- The A-action induced by the structural map: `scalarModule r` with
  `scalar_normalization` identifies multiplication by every `a ∈ I^0 = A` with the
  cohomology of the sectionwise structural scalar map. This determines the A-action.
  `HEq` here only transports the codomain indexed by r+0 to the one indexed by r.
- L is the induced cohomology map: every occurrence is literally
  `(idealPowerCohomologyFunctor X q).map (multiply k r a)`.
- A-linearity: `linear` requires that map to commute with every b in A. Additivity is
  already part of its codomain `AddCommGrpCat` morphism. `scalar_normalization` also
  gives exactly L(0,r,a)(x)=ax.
- B is the recorded Mathlib `reesAlgebra I`, not the image algebra on X.
- The underlying additive group of M is Mathlib's dependent `DirectSum ℕ` of these
  actual cohomology groups. No replacement of the underlying groups is made.
- The B-module structure is `reesModule`. `convolution` specifies its action on EVERY
  polynomial and EVERY finite-support vector by a double sum of coprojections in
  degrees r+k. Taking the degree-d component gives exactly the node's sum over
  k+r=d. Polynomial and direct-sum supports make both summations finite. The use
  of r+k in the coprojection agrees with k+r by commutativity of natural addition.
- Finite generation is `@Module.Finite ... d.reesModule`, explicitly using the very
  module structure in that datum, not another inferred module instance.
- The last degree-zero clause is also explicitly `degree_zero`: algebraMap A B a
  acts on the r-th summand by its specified `scalarModule r` action.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `etaleForget`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`, with its
  separated/finite-type/universally-closed definitions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently reused
  by the published `X.Modules`; no copy of its module category is made.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` records the site's covering convention;
  its retained Mathlib cohomology component is `Sheaf.H`/`Sheaf.functorH` in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. The general covering predicate
  is not an additional hypothesis for this already fixed etale site.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the recorded
  `SheafOfModules.IsQuasicoherent` specialization and its slice instances, imported
  publicly through `AlgebraicSpaceSmallRingedModel`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.RingTheory.ReesAlgebra`: `reesAlgebra` and its coefficient membership.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerQuotients`:
  `idealPowerChartScalar`, the existing structural scalar map.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallEtaleModel`,
  `smallEtaleModelTopology`, `smallStructureRings`, `smallModuleRestriction`, and
  `smallModuleEquivalence` (its specified restriction is an equivalence).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`.

Proof-only imports retain the recorded modules for the Zariski/etale quasi-coherent
comparison, module operations, universal right-derived delta-functor, finite type
of the Rees algebra, and locally Noetherian schemes. The proof dependencies
`lem-sfb-space-qcoh-kernels-colimits` and `lem-sfb-space-graded-cohomology-finite`
have no Lean record on the read base, so there is currently no module to import for
them. They are proof dependencies only; this statement does not assume either result.

Edge cases checked before drafting: the zero ring and empty space are admitted;
no nonemptiness is assumed. For I=0, positive powers have locally zero range, hence
are zero sheaves; degree zero remains F. For I=A, every power identifies with F and
the action shifts copies of its cohomology by polynomial degrees. The zero sheaf
and zero cohomology groups give the zero direct sum. Exponents k=0 and r=0 and
q=0 all occur; `HEq` handles the harmless r+0 indexing equality. Zero polynomials
and zero vectors have empty supports, giving the zero sum. Zero elements of I^k
are included and the normalization forces their multiplication maps to be zero.
The Ext size u+1 accommodates all these objects without a new size hypothesis.

Searches: `msearch.py` LeanFinder queried proper algebraic-space ideal-power
cohomology finiteness; LeanSearch queried the same statement; Loogle queried
`reesAlgebra, Module.Finite`; grep queried `reesAlgebra|idealPower` in Mathlib
AlgebraicGeometry. Rees finite-type lemmas and algebraic local cohomology appeared,
not this proper-space cohomology statement. The final searches for the new notion
are recorded with their actual returned names and digests in its node. Direct
searches of `lean/WeilConjectures` and `lean/Sheaf` found the scheme-only Rees and
cohomology results, the existing quotient tower, generic local-power sections, and
small site model. They do not supply this normalized algebraic-space datum or
finiteness assertion. An exact id search in WeilConjectures returned no declaration.
`tools/blueprint_refs.py search 'ideal power Rees cohomology'` returned zero nodes;
DAG searches distinguished the existing products/quotients from the missing datum.

No statement correction, unusable dependency repair, or STATEMENT-DISPUTED issue
was needed. The item statement, proof and proof dependencies are unchanged.

## New nodes

`def-sfb-space-ideal-power-rees-cohomology-data` defines the normalized presentation
of the power subsheaves and their induced actions described above, following the
paragraph preceding 08AW and its graded module structure. Its module supplies the
real composite `idealPowerCohomologyFunctor` and the full structure
`IdealPowerReesCohomologyData`. The latter does not assert existence, and no object
or action is chosen from an unproved existence assertion. The theorem in the item
constructs precisely that datum and proves its Rees-module finiteness. The search
found no existing owner for this package. Existing structural scalars, site model,
cohomology, modules, and Rees algebra are imported and reused. Every notion cited
in this node is an existing definition node; it has the item's chapter, unit and
blueprint provenance, with `import_flags: []`.

The item also cites the already landed scheme restriction and representable
scheme-space nodes, since they are used to render the coherence hypothesis and
the affine base as a target space. No existing dependency node is changed.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
