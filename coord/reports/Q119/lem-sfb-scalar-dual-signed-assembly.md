## Worker report

The module `Sheaf.Algebra.Homology.ScalarDualSignedAssembly` states the single
 theorem `CategoryTheory.scalarDual_signed_assembly`, with proof `sorry`.
It assembles the supplied natural comparison under an arbitrary additive functor
into the canonical signed comparison of cochain complexes. No definitions, helper
nodes, dependency repairs, or changes to the mathematical node were necessary.
The source is Stacks Project, sites-cohomology.tex, section-hom-complexes (0A8X),
with the degree-reversal convention of lemma-dual-perfect-complex (08JJ).
The arbitrary additive-functor argument is explicitly the node's agent-written
argument, not an assertion that 08JJ states this generalization.

Hypotheses and clauses, in their order in the node:

- A site small in the module universe is `{C : Type u} [Category.{u} C]`
  and `(J : GrothendieckTopology C)`. The coefficient ring is
  `(R : Type u) [CommRing R]` and the ring sheaf is `(B : Sheaf J CommRingCat.{u})`.
  This is the stipulated size convention; no nonempty-site hypothesis is imposed.
- The category of B-module sheaves is `ringedSiteModules.{u}` on the ring-forgetting
  image of B. The functor is `T : ModuleCat.{u} R ⥤ ringedSiteModules ...` with
  `[T.Additive]`. No exactness, linearity over R on sheaf morphisms, finite generation,
  projectivity, or boundedness is assumed.
- The supplied B-linear sheaf maps are the binder `η`, with source
  `T.obj (ModuleCat.of R (Module.Dual R V))` and target
  `SheafOfModules.homObj (R := B) (T.obj V) (SheafOfModules.unit ...)`.
  The unit is the coefficient sheaf as its own module. Their naturality is exactly
  `hη`: `η W ≫ homObjMap (T.map f) (𝟙 _) = T.map (ofHom f.hom.dualMap) ≫ η V`.
  Lean's `≫` composes from left to right, reversing the printed order of the
  node's ordinary composition symbols, without changing the equation.
- Every integer cochain complex is quantified as `F : CochainComplex (ModuleCat R) ℤ`.
  Its scalar total dual is the existing `CochainComplex.moduleHomComplex F`
  with target `((CochainComplex.singleFunctor ... 0).obj (ModuleCat.of R R))`.
  The initial existential family `τ F q` gives its canonical R-linear coordinate
  isomorphisms to `ModuleCat.of R (Module.Dual R (F.X (-q)))`.
  The first conjunct specifies their actual projection to `z.v (-q) 0 (neg_add_cancel q)`
  followed by `singleObjXSelf.hom`; thus τ cannot be an arbitrary isomorphism.
  The second conjunct gives their differential formula using
  `-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap`, exactly -(-1)^q times
  precomposition, including negative integers q.
- `T.mapHomologicalComplex (ComplexShape.up ℤ)` applies T termwise. The target is
  the dependency's `signedSheafDualComplex` with coefficient unit module.
  The family `κ` consists of morphisms between these actual complexes, so its
  differential compatibility is part of the chain-map type. Its first conjunct
  fixes `(κ F).f q = T.map (τ F q).hom ≫ η (F.X (-q))`.
  The following conjunct quantifies every competing chain map κ' with those same
  components and asserts `κ' = κ F`, expressing the required uniqueness.
  The `@id` terms merely make the definitionally equal component Hom types explicit;
  they do not choose an identification or insert a hypothesis.
- The next conjunct separately asserts the displayed coordinate differential equation:
  `η (F.X (-q)) ≫ (-q.negOnePow • homObjMap (T.map (F.d ...)) (𝟙 _))`
  equals `T.map (ofHom (-q.negOnePow • ...dualMap)) ≫ η (F.X (-(q + 1)))`.
- Contravariant naturality quantifies every `f : F ⟶ G` and supplies its actual
  precomposition chain maps `g` on scalar duals and `h` on signed sheaf duals.
  Their components are characterized by τ and `ModuleCat.ofHom (f.f (-q)).hom.dualMap`
  for g, and `SheafOfModules.homObjMap (T.map (f.f (-q))) (𝟙 _)` for h.
  The naturality square is `(T.mapHomologicalComplex ...).map g ≫ κ F = κ G ≫ h`.
  These component specifications force the canonical precomposition maps;
  identity and composite compatibility follow from their components and functoriality,
  so no arbitrary maps replace contravariant naturality.
- The isomorphism clause assumes only `∀ r : ℤ, IsIso (η (F.X r))` and concludes
  both `IsIso (κ F)` and `IsIso ((@DerivedCategory.Q ... (HasDerivedCategory.standard _)).map
  (κ F))`. This is a chain-level isomorphism and its actual localization in D(B),
  without requiring a derived functor of T or replacing it by per-degree isomorphisms.
- For every `a b : ℤ`, the last implication assumes precisely
  `∀ r, r < a ∨ b < r → IsZero (F.X r)` and concludes, whenever
  `q < -b ∨ -a < q`, the conjunction `IsZero` of the q-th terms of both
  `T(F^∨)` and `D(TF,B)`. It includes all a,b and does not assume `a ≤ b`.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, no declaration; rendered by
  the explicit universe u and the standard localization universe.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `CategoryTheory.Precoverage.IsSiteForCoverings`.
  Imported as recorded; for the statement's associated topology the ambient objects
  are Mathlib `GrothendieckTopology` and `Sheaf`, as that dependency's note specifies.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation for Mathlib `SheafOfModules`, including its abelian category.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj` and `SheafOfModules.homObjMap`; their full signatures retain
  the coefficient sheaf and give the localized-site internal Hom, not external Hom.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, whose terms are module-valued homogeneous cochains
  and whose differential is the linear `HomComplex.δ_hom`.
- `WeilConjectures.Algebra.Homology.HomComplexToSingle`:
  `CategoryTheory.signedSheafDualComplex`, with its exact signed precomposition differential.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
  The remaining Mathlib imports supply termwise additive prolongation, scalar duals,
  and the small-site sheafification/coefficient instances. All proof dependencies
  already occur among these imports.

Edge cases checked before finalizing the statement:

The zero ring R, the zero coefficient sheaf B, the zero functor, the zero complex,
empty sites, unbounded complexes, and nonprojective terms are not excluded by a binder.
For the zero complex, additivity sends its zero objects to zero objects. When a>b,
every integer lies outside [a,b], and every integer lies outside [-b,-a]; the last
conjunct therefore asserts vanishing in every degree, as required. For a=b only one
degree survives. With Z --2--> Z in degrees 0,1, the dual differential in degree -1
is +2, agreeing with -(-1)^(-1), while a differential originally in degrees -1,0
has its dual in degree 0 with sign -1. No boundedness is used in the assembly,
naturality, or isomorphism clauses. No mathematical statement fault was found.

Searches (the launcher records exact results in searches.jsonl):

- `msearch.py ... leanfinder "A natural module dual comparison under an additive functor
  to module sheaves assembles into a signed cochain map natural in complexes and
  invertible when the comparisons are invertible"`: eight results, including
  `Functor.mapCochainComplexSingleFunctor`, mapping-cone prolongation isomorphisms,
  and `groupCohomology.inhomogeneousCochainsIso`; no supplied-internal-dual assembly.
- `msearch.py ... loogle "CochainComplex.HomComplex.Cochain.toSingleEquiv"`: eight results,
  including `toSingleEquiv`, its inverse and linear compatibility lemmas. These provide
  the scalar projection but not the comparison to internal sheaf duals under arbitrary T.
  The source definition and its docstring were read.
- `msearch.py ... grep "mapHomologicalComplex|toSingleEquiv|signedSheafDual"
  Algebra/Homology`: 25 reported results, generic prolongations and Hom cochain
  coordinates, not the node's full statement.
- `rg` of `scalarDual_signed_assembly|scalar.dual.*assembly|lem-sfb-scalar-dual-signed-assembly`
  in both live `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration.
  A broader `scalarDual|[Ss]igned.*[Aa]ssembly|signedSheafDualComplex|moduleHomComplex`
  search found the recorded total-Hom and signed-dual definitions and unrelated
  precomposition/derived-adjunction interfaces; none states this comparison.

Validation: scompile.py compiled both the private sandbox name and the final library
module name cleanly (17.3 s and 26.7 s respectively). The only theorem proof is sorry.
The initial elaboration failures at component equalities were repaired by explicit
`@id` type annotations; no timeout limit was increased and no mathematical statement
was changed. The node copy differs from the read-only repository only in `lean`.

## Second reading by Q119

I reopened the full node and the final Lean signature for a separate clause-by-clause
reading, summarized above. The dispatcher explicitly forbids starting other agents;
this is a worker self-check, and the maintainer supplies the independent review.
In particular, I checked the orientation of hη and of the contravariant square,
canonical projection rather than an unconstrained coordinate choice, the exact
negative-integer sign, the distinction between an actual chain isomorphism and
per-degree isomorphisms, and both vanishing conclusions for an empty interval.
No clause was dropped or extra mathematical hypothesis introduced. The only changes
to the saved draft were an elaboration transparency setting and explicit component
Hom types. No dependency or mathematical node correction is being proposed.
