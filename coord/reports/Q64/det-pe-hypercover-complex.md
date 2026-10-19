## Worker report

Item: `det-pe-hypercover-complex`; group Q64; stage 2; 2026-10-17.

The module `lean/Sheaf/AlgebraicGeometry/ProEtale/HypercoverComplex.lean` states
`AlgebraicGeometry.Scheme.ProEt.hypercover_complex_natural_iso`. It asserts existence
of a natural isomorphism from the right derived abelian section functor, restricted
to bounded-below complexes, to the explicitly constructed alternating section total.
All theorem proofs are `sorry`. All construction data are compositions of existing
functors. There is no statement correction and no STATEMENT-DISPUTED claim.

I read the full target JSON (including its seven proof steps), its current blueprint
source `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-hypercover/det-pe-hypercover-complex.md`, and Stacks proetale.tex,
`lemma-compute-cohomology` (Tag 09A2), including the surrounding construction. The
source's first proof display has RΓ(X_proet,E), although the lemma and its final
proof display correctly use RΓ(U,E). This is a source typo, not a node fault.
The original six statement dependencies' JSON records and full declaration source
were read. No repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Scheme X: `(X : Scheme.{t})`. The small pro-etale site is the existing `X.ProEt`
  with `topology X` and `precoverage X`, exposed by the recorded
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and the hypercover dependency.
  Its object universe remains t+1 and its morphism universe remains t.
- A sheaf of rings R: `(R : Sheaf (topology X) RingCat.{u})`. This is not restricted
  to commutative rings, constant rings, finite rings or any particular characteristic.
  Modules and abelian groups use the common larger universe `max u v (t+1)`, exactly
  the size convention of the recorded general-universe Grothendieck interface.
  The otherwise arbitrary v permits further enlargement; it restricts no coefficients.
- Object U: `(U : X.ProEt)`. No quasi-compactness, quasi-separatedness, affineness
  or contractibility is imposed on U.
- An augmented simplicial object W over U: `(W : SimplicialObject (Over U))`.
  Both the augmentation and all simplicial identities, including degeneracies, are
  intrinsic data. The underlying term is `(W _⦋r⦌).left`.
- The hypercover condition is rendered exactly as in the dependency's recorded
  `exists_proetale_hypercover_single_affine`: `hzero` says its degree-zero singleton
  augmentation covers U; `hmatching` gives a limiting proper-face cone in `Over U`,
  a covering matching map, and its equations against EVERY proper-face projection.
  The latter equations specify the canonical matching map rather than an arbitrary
  arrow to the same limit object. Relative limits in `Over U` retain the augmentation;
  degree-one matching is W_0 ×_U W_0. These are the matching-cover clauses, without
  the existence dependency's additional qcqs assumptions or affine conclusions.
- Every W_r weakly contractible: `hweak` is
  `(topology X).IsWeaklyContractible.{max u v (t+1)} (W _⦋r⦌).left` for every natural r.
  This uses the recorded `sk-def-pe-weak-contractible` definition, without a private
  projectivity predicate. The definition quantifies over locally surjective set-sheaf
  maps; the standard locally-surjective/epi equivalence gives precisely the node's
  epimorphism-on-sections meaning in the chosen coefficient universe.
- Complex K of R-module sheaves: objects of
  `CochainComplex.Plus (ringedSiteModules.{max u v (t+1)} R)`. This uses the recorded
  module-sheaf abbreviation, hence exactly Mathlib `SheafOfModules`, with actual
  semilinear restrictions and sectionwise linear morphisms.
- An integer a with K^b=0 below a: Mathlib `CochainComplex.plus` is DEFINED as
  `∃ a : ℤ, K.IsStrictlyGE a`; `isStrictlyGE_iff` says its terms below a are `IsZero`.
  Thus `Plus` packages precisely the node's strict termwise boundedness, including
  negative a. This does not replace termwise boundedness by cohomological boundedness.
  Any K with any supplied bound a is an object of this full subcategory. Using all
  bounds at once also makes naturality apply to complexes with different bounds.
- C^{r,b}=K^b(W_r): `hypercoverAbelianSections` forgets only to the existing underlying
  abelian presheaf using `SheafOfModules.forget` and `PresheafOfModules.toPresheaf`,
  then precomposes with `(W ⋙ Over.forget U).rightOp`. Consequently its degree r
  object is the underlying abelian group of K^b(W_r), and all operators are its
  actual restrictions. No section object or map is chosen by existence.
- Horizontal differential δ=Σ(-1)^i d_i^*: `hypercoverAbelianRows` composes that
  functor with `AlgebraicTopology.alternatingCofaceMapComplex`. Its source definition
  `AlternatingCofaceMapComplex.objD` is exactly the sum over `Fin (r+2)` of
  `(-1 : ℤ)^i.val • X.δ i`. `embeddingUpNat.extendFunctor` makes every negative
  horizontal degree zero. The helper theorem `hypercoverAbelianRows_additive` is
  the additivity assertion in step 1 of this node's own proof; its full proof plan
  is in its docstring. It adds no hypothesis to the main statement.
- Signed vertical differential and total: `hypercoverAbelianTotal` applies the rows
  degreewise, then `HomologicalComplex₂.flipFunctor`, putting r first and b second,
  and finally the EXISTING `HomologicalComplex₂.totalFunctor ... (ComplexShape.up ℤ)`.
  For this shape the horizontal sign is one and the vertical sign is (-1)^r.
  Thus it is the coproduct over r+b=q of the specified C^{r,b}, with differential
  δ+(-1)^r d_K. Negative r summands are zero by extension. If b<a, evaluation of
  a zero module sheaf is zero. The remaining diagonal indices are exactly
  0≤r≤q-a and b=q-r, yielding the displayed finite direct sum canonically; the
  construction retains the full diagonal with its zero summands, as Mathlib total
  does. This is the standard coproduct identification, not an assertion that
  infinitely many zero summands are definitionally absent. No new totalization is
  implemented and no unbounded descent assertion is made.
- RΓ(U,-) is the right derived functor of additive evaluation to Ab:
  `hypercoverAbelianEvaluation` is precisely the existing module evaluation followed
  by `forget₂ ... AddCommGrpCat`. The left functor of the isomorphism is
  `Plus.ι ⋙ DerivedCategory.Q ⋙
  (hypercoverAbelianEvaluation X R U).rightDerivedFunctorOfQuasiIsoResolutions
  (moduleQuasiIsoKInjectiveResolutions X R)`.
  This is the RECORDED right-derived universal pair, not an arbitrary replacement
  functor or an unproved existence assumption. Its resolution hypothesis comes from
  the existing general-universe Grothendieck/K-injective interface. The definition
  uses the named proof interface from `det-pe-wc-sections-derived`; that landed node
  was added to stmt_deps to cite this actual dependency. Its affine theorem is NOT
  applied and introduces no affineness assumption here.
- The comparison is in D(Ab): the right functor is
  `Plus.ι ⋙ hypercoverAbelianTotal X R U W ⋙ DerivedCategory.Q`, with Ab values in
  the same common universe. The two `HasDerivedCategory` binders choose arbitrary
  localization morphism universes wA and wB, as the recorded derived-category
  definition requires; neither assumes a finiteness, exactness or boundedness
  property. Both can always be instantiated with `HasDerivedCategory.standard`.
- Existence and naturality: `Nonempty (leftFunctor ≅ rightFunctor)` means existence
  of one NATURAL isomorphism, with an invertible comparison at every bounded-below
  complex and naturality for every coefficient chain map. Since the left functor
  factors through Q, these comparisons identify the total functor with a functor
  inverting quasi-isomorphisms; the naturality therefore passes to roofs/derived
  morphisms, as step 7 of the node explains. This is stronger than merely choosing
  unrelated objectwise isomorphisms in exactly the way requested by “natural”.

Dependency declarations and source modules actually used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the existing site
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, and category presentation.
- `Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence`:
  `AlgebraicGeometry.exists_proetale_hypercover_single_affine`, whose signature supplies
  the exact matching-cover formulation; its imported
  `Sheaf.CategoryTheory.ProperFaceMatchingObject` defines
  `CategoryTheory.SimplicialObject.properFaceDiagram` and `ProperFaceCategory`.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`:
  `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived`:
  `AlgebraicGeometry.Scheme.ProEt.moduleEvaluation_additive` and
  `moduleQuasiIsoKInjectiveResolutions`. The latter is the existing canonical proof
  of the universal resolution hypothesis, using
  `SheafOfModules.isGrothendieckAbelianOfUniverses` from
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` and
  `Abelian.HasKInjectiveResolutions.exists_isKInjective` from
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- Mathlib: `DerivedCategory` and `DerivedCategory.Q` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  `CochainComplex.Plus` and `Plus.ι` in `CochainComplexPlus`;
  `AlgebraicTopology.alternatingCofaceMapComplex`;
  `ComplexShape.embeddingUpNat.extendFunctor`;
  `HomologicalComplex₂.flipFunctor` and `totalFunctor`.

All already-recorded proof-dependency modules are imported without `public`, including
`BoundedBelowInjectiveResolution`, `ProetaleSiteProperties`, the noncommutative
`RingedHypercoverInjectiveAugmentationRing`, `BoundedBelowAugmentation`,
`BoundedBelowTotalComparison`, the module forgetful theorem, and the Mathlib
locally-surjective/epi and K-injective derived-Hom interfaces. The two missing-local
bounded-below comparison sources were read with `scompile.py --source`, which resolved
the current published sources successfully. No import cycle is introduced.

Construction helpers: the six recorded declarations all belong to the target module.
The helpers spell out the construction C and Tot that the item's own statement defines,
and the additive proof is exactly its step 1. They are authorized same-notion helpers,
not independent new notions. The existing commutative module-valued hypercover total
cannot be applied to RingCat coefficients; it is not copied or redefined. All actual
presheaf, coface-complex, extension and totalization constructions are Mathlib's.
No new DAG node or dependency-record repair is needed.

Edge cases checked:

- q<a: no nonzero diagonal summand survives, even when a is negative.
- q=a: only r=0, b=a can survive, and its vertical sign is +1.
- K=0: both derived evaluation and every total section term are zero.
- Identity/constant hypercover: alternating restrictions are the usual coface sums;
  matching conditions allow it, and the statement has no nondegeneracy assumption.
- Empty scheme, empty U, zero coefficient ring, disconnected weakly contractible terms:
  no nonemptiness, domain, connectedness or characteristic hypothesis excludes them.
- Hypercover terms need not be affine. The weak-contractibility hypothesis quantifies
  over maps of sheaves; it does not ask a disconnected term to split into one member
  of a covering family.
- Different strict bounds for source and target of a chain map: Plus contains both;
  a common minimum bound is used in the proof, not imposed on the statement.
- Independent site/coefficient sizes: t, u, v, wA and wB are explicit; no SmallCategory
  instance on X.ProEt, no site/morphism universe equality, and no arbitrary small
  test-object universe is assumed.

Searches (the launcher preserved full search results in searches.jsonl):

1. `msearch.py ... leanfinder` — “A bounded below complex of sheaves of modules has
   derived sections computed by the alternating total complex on a weakly contractible
   hypercover”: 8 hits, mainly Sheaf.H/cohomologyPresheaf and one-hypercover sheaf
   conditions; no exact theorem.
2. `msearch.py ... loogle` —
   `CosimplicialObject.alternatingCofaceMapComplex, HomologicalComplex₂.total,
   SheafOfModules.evaluation`: 0 hits (the first expected name is unknown; the source
   confirms the actual name is AlgebraicTopology.alternatingCofaceMapComplex).
3. `msearch.py ... grep` — `hypercover|alternatingCoface`, subdirectory
   `CategoryTheory/Sites`: one-hypercover site API, no bounded-below total computation.
4. `msearch.py ... leansearch` — “Derived sections are naturally isomorphic to the
   total complex of abelian sections on a weakly contractible hypercover”: 8 hits,
   including total.mapIso, HasDerivedCategory and injective-resolution right-derived
   objects; no exact statement.
5. `rg` in Mathlib's `AlternatingFaceMapComplex`, `TotalComplex`, `CochainComplexPlus`,
   module-sheaf source, project `WeilConjectures`, and `lean/Sheaf`: located and read
   the constructions used above. The closest project theorem is
   `AlgebraicGeometry.Scheme.ProEt.hypercover_computes_boundedBelow_complex`, module
   `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`. It assumes a
   COMMUTATIVE ring sheaf and returns D(R(U)-Mod) via resolution comparison; it is
   not the node's arbitrary-ring, D(Ab), recorded-RΓ natural isomorphism.
   The nearby `hypercoverTotal` has the same commutativity restriction, so cannot
   supply this node's total for a general sheaf of rings.
6. `rg` of `det-pe-hypercover-complex` in the named upstream tree and of
   `hypercoverAbelian` in the upstream name registry, source, Mathlib and project
   found no existing declaration. The only existing target-id reference in Lean
   is a proof docstring of the downstream bounded-continuity module.

Validation: the delivered module passed `scompile.py Q64 det-pe-hypercover-complex
<module>` on 2026-10-17: both the sandbox and library checks were clean, 2.5 s and
2.8 s respectively, with no error or warning. The module has no auto-bound variables,
no local notation or local instances, and every line is at most 100 characters.
The exact main signature is recorded verbatim in the node's lean.statement. The node
copy differs only in lean and the added landed statement dependency noted above.
The independent second reader has not read this delivery yet and will supply its
own second-reading report; this worker does not impersonate that reader.

## Second reading by Q64

I read the node JSON, its blueprint statement and proof, the Stacks source at
`proetale.tex`, Tag 09A2 (`lemma-compute-cohomology`), and every recorded
statement dependency before checking the Lean file. The item is a statement node;
there is no `statement_change`, repair note, or disputed-statement flag.

The node's objects and hypotheses correspond as follows.

- The scheme `X` is `(X : Scheme.{t})`; the site is the existing `X.ProEt`, with
  object universe `t + 1` and morphism universe `t`.
- The ring sheaf `R` is `(R : Sheaf (topology X) RingCat.{u})`. The module
  category is `ringedSiteModules.{max u v (t + 1)} R`; no commutativity,
  finiteness, characteristic, or universe equality is added.
- The site object `U` is `(U : X.ProEt)`, and the augmented simplicial object is
  `(W : SimplicialObject (Over U))`; augmentation and simplicial identities are
  therefore part of `W`.
- Weak contractibility is `hweak`, quantified over every `r : ℕ` and using the
  recorded `IsWeaklyContractible` in the coefficient universe.
- The degree-zero covering clause is `hzero`, namely
  `Presieve.singleton (W _⦋0⦌).hom ∈ (precoverage X) U`.
- The matching-cover clause is `hmatching`: for each `r` it supplies a cone over
  `properFaceDiagram W (r + 1)`, a map `μ`, `Nonempty (IsLimit c)`, the covering
  presieve, and the equation against every proper-face projection. This retains
  the canonical matching-map equations and adds no affine or qcqs data.
- A bounded-below complex of `R`-modules is represented by the source category of
  `CochainComplex.Plus.ι`; `Plus` is the existing strict termwise lower-bound
  construction, so it covers every integer bound `a`, including negative `a`.
- `hypercoverAbelianSections` evaluates the underlying module sheaf on every
  `W_r`, and `hypercoverAbelianRows` uses Mathlib's alternating coface complex,
  giving `δ = Σ (-1)^i d_i^*` and zero extension in negative horizontal degrees.
- `hypercoverAbelianTotal` flips the rows and applies the existing total functor;
  its differential is the stated `δ + (-1)^r d_K`, and its diagonal is the
  coproduct over `r + b = q`. On `Plus` the lower bound makes this the finite
  range `0 ≤ r ≤ q - a` (with an empty diagonal when `q < a`).
- `hypercoverAbelianEvaluation` is the additive section functor to
  `AddCommGrpCat`; the left side is its recorded right derived functor after
  `DerivedCategory.Q`, restricted along `Plus.ι`.
- The right side is the total functor followed by `DerivedCategory.Q`, again
  restricted along `Plus.ι`. The independent `HasDerivedCategory` binders
  (`wA` and `wB`) impose no extra finiteness or universe assumptions.
- `Nonempty (left ≅ right)` is one natural isomorphism, hence gives the required
  objectwise derived comparison and naturality in every coefficient chain map.

The conclusion is rendered by
`AlgebraicGeometry.Scheme.ProEt.hypercover_complex_natural_iso`; no clause is
omitted or changed. The explicit finite diagonal in the node is represented by
the existing total construction together with the strict lower-bound subcategory,
rather than by a private totalization. All six helper declarations are
constructions or the additivity statement for this same notion, and every theorem
proof remains `sorry`.

Edge cases checked: `q < a` gives an empty nonzero diagonal; `q = a` leaves only
the `r = 0` term; negative bounds are allowed; the zero complex and zero ring are
admitted; empty schemes and empty site objects are not excluded; identity or
constant hypercovers satisfy the stated form; no affine, connectedness,
nonemptiness, or characteristic assumption is present; and coefficient, site,
index, and derived-category universes remain independent where the node allows
them. Different lower bounds for source and target complexes are handled by the
full `Plus` category and are not silently identified.

For the one-definition-per-notion check I searched the named upstream tree,
Mathlib, and the project with `rg` for `det-pe-hypercover-complex`,
`hypercoverAbelian`, `hypercover`, `alternatingCoface`, and the theorem name;
the launcher search log (`searches.jsonl`) records LeanSearch, Loogle/LeanFinder,
and grep searches. The closest declaration is
`AlgebraicGeometry.Scheme.ProEt.hypercover_computes_boundedBelow_complex` in
`Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`, but it assumes
a commutative ring sheaf and lands in a module-valued derived category, so it is
not this node and was not duplicated. No Mathlib or upstream declaration states
this arbitrary-ring, derived-abelian-group natural isomorphism.

No mismatch was found, so no Lean, node, or dependency repair was needed. The
module compiled cleanly with the required wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q64 det-pe-hypercover-complex
lean/Sheaf/AlgebraicGeometry/ProEtale/HypercoverComplex.lean` (sandbox 2.3 s,
library 3.1 s; no errors or warnings).
