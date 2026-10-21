## Worker report

The module Sheaf.AlgebraicGeometry.ProEtaleAmbientOperationsScalarLinearity states
AlgebraicGeometry.Scheme.proEtaleRingDerivedOperations_scalarLinearity, with one `sorry`
and no other declarations. The node changes only in `lean`.

Clause-by-clause correspondence:

- The arbitrary commutative scalar ring is `(A : Type v) [CommRing A]`; its universe is
  independent of the schemes' universe, so this includes large scalar rings and
  noninjective coefficient maps.
- The scheme morphism is `{U V : Scheme.{u}} (f : U ⟶ V)`. The published `ProEt.topology`
  is the small pro-etale site with object universe u+1 and morphism universe u.
- The arbitrary coefficient ring sheaves are `RV` and `RU`, valued in
  `CommRingCat.{u + 1}` according to the published coefficient convention. They are
  not assumed constant, finite, torsion or complete.
- The specified identification is `c`, the isomorphism from the published ring-sheaf
  inverse image of RV to RU.
- The maps into global sections are `aV` and `aU`, ring homomorphisms into
  `RingCat.sectionsSubring`. This is the ring of all compatible families of sections,
  hence exactly the global-section ring, including on the empty scheme. No auxiliary
  choice of sectionwise action is input.
- Compatibility of c with A is `hc`. It says that on every W of V's site, the coefficient
  map adjoint to c carries the restriction of aV(a) to the restriction of aU(a) on W_U.
  By the inverse/direct-image adjunction this is precisely A-algebra compatibility of c.
  In particular it is not merely an assumption that the final functors are linear.
- The node instructs us to give module and derived categories the induced structures.
  The existential `lU` and `lV` provide the module-category `Linear A` structures.
  The first two conjuncts fix their scalar multiplication on every morphism, object W
  and element x to `(aU a).val W • h.val.app W x` and the V analogue. Morphisms of module
  sheaves are determined sectionwise, so these equations specify the entire Hom action.
  An A-module structure with its fixed additive group is determined by its scalar action;
  the normalization therefore leaves no arbitrary alternative linear structure.
  Their existence is part of equipping the categories, as requested in the node.
- Inside the instance lambda, the derived `Linear A` structures are synthesized from
  exactly these lU and lV using `DerivedCategory.instLinear`, not additional existential
  derived structures. The lambda explicitly applies these instances and contains no let,
  private notation, or locally declared instance. It keeps the statement readable outside
  the file and avoids postulating the existence of an unspecified action.
- The operations are exactly `proEtaleRingDerivedPullback f RV RU c` and
  `proEtaleRingDerivedDirectImage f RV RU c`. The dependency defines these as the exact
  termwise derived pullback and K-injective right derived direct image, respectively,
  on `DerivedCategory (proEtaleRingModules ...)`.
- For each operation, `.Additive` is the clause F(s+t)=F(s)+F(t), and `Functor.Linear A`
  is the clause F(a*s)=a*F(s), quantified over all parallel morphisms by the class fields.
  There are no cohomological bounds, derived-completeness or constructibility premises.

Dependency declaration/source readings:

- def-weil-pbc-proetale-operations records
  Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations. Its public imports expose the
  full arbitrary-ring-sheaf construction, not just its named constant specialization.
  Read the full module, plus the signatures, bodies and docstrings in ProEtaleOperations
  for proEtaleRingModules, proEtaleRingDirectImageMap, proEtaleRingModuleDirectImage,
  proEtaleRingDerivedPullback, proEtaleRingDerivedDirectImage, their factorization and
  representative clauses, and the normalized adjunction in
  Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction. This recorded dependency
  is usable as it stands, so no duplicate or dependency repair is needed.
- def-weil-linear-category is Mathlib.CategoryTheory.Linear.Basic, CategoryTheory.Linear:
  the fixed preadditive Hom groups have Module A structures with bilinear composition.
- lem-weil-linear-abelian-derived-category is
  Mathlib.Algebra.Homology.DerivedCategory.Linear: DerivedCategory.instLinear,
  instLinearCochainComplexIntQ, instLinearHomotopyCategoryIntUpQh,
  instLinearShiftFunctorInt. Read the entire file; the localization construction is the
  instance used by the theorem's conclusion.
- def-weil-linear-functor is Mathlib.CategoryTheory.Linear.LinearFunctor,
  CategoryTheory.Functor.Linear, together with Functor.Additive from
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor. Read their class signatures and
  docstrings: Linear is scalar preservation; Additive supplies the separate sum clause.
- The proof-only dependency lem-cbc-exact-linear-derived-functor is
  Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
  CategoryTheory.Functor.instLinearDerivedCategoryMapDerivedCategory; its module is
  imported without `public`, as required.
- The sectionwise action already exists as SheafOfModules.homModule/homLinear in
  WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule. Read their construction,
  which transports the global-section action on presheaf morphisms; also read
  PresheafOfModules.sectionsSMul and sectionsSMulHom in the imported InternalHom module.
  These are construction ingredients, not a second definition in this delivery.

Source checks: opened literature/stacks-project/dga.tex at
`definition-functor-linear-categories` (09MK), sites-modules.tex at
`lemma-adjoint-push-pull-modules` (03D3) and `lemma-flat-pullback-exact` (04JC), and
derived.tex at `lemma-K-injective` (070I). The combined theorem is explicitly
agent-supplied in the node; no claim that a single tag states it was introduced.
Its four-step adjunction proof is retained in the theorem docstring.

Edge cases checked mathematically before writing: f=id, U or V empty whenever a morphism
exists, A=0 (forcing zero coefficient rings where applicable), zero module/complex,
a=0 and a=1, nonfaithful A-actions, nonconstant ring sheaves, and complexes unbounded
in both directions. Module actions and adjunction calculations work in all cases.
No flatness assumption on the scheme morphism is needed: the coefficient identification
makes the module inverse image exact. The statement does not assume that a resolution
choice is A-linear. No statement dispute or correction was necessary.

Searches for an existing exact statement:

- msearch.py leanfinder: `Derived functors of sheaves of modules are linear over scalar
  rings` returned eight hits, including the exact-functor derived linearity instance,
  the induced derived structures, shifts, and the abelian sheaf-module category.
  These supply ingredients but not the combined arbitrary ring-sheaf operations theorem.
- msearch.py loogle: `CategoryTheory.Functor.Linear, CategoryTheory.Adjunction` returned
  CategoryTheory.Adjunction.extLinearEquiv, an Ext comparison for exact linear functors,
  not the required theorem.
- msearch.py grep: `linear|map_smul` in Algebra/Homology/DerivedCategory returned 23 hits,
  principally ExactFunctor.lean and Linear.lean. The former proves only the exact
  termwise pullback ingredient.
- msearch.py leansearch: `Derived pullback and pushforward of modules over sheaves of
  rings preserve scalar multiplication` returned eight hits for ordinary sheaf pullback,
  pushforward and sectionwise scalar operations; no combined unbounded theorem.
- rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `proEtaleRingDerivedOperations_scalarLinearity`, `proEtaleRingDerived.*[Ll]inear`, and
  the node id returned no existing statement. Broader Hom-action searches found and
  reused homLinear. The existing scalarLocalizationCoefficientLinear helper is restricted
  to SmallCategory C; no copy or transport of that helper is needed here because the
  canonical action is specified in the theorem itself on the original small pro-etale site.

Validation: scompile.py compiled the sandbox and actual library module with exit 0,
no errors or warnings (7.9 s and 6.9 s). Explicit `autoImplicit false`, named universes u,v,
and all binders are retained. The only postponed proof belongs to this DAG node.

## Second reading by NO

A second pass in this worker session reopened the node and the final Lean file. No other
agent was started, as required by the dispatcher brief; independent maintainer review
remains the delivery's next step. The pass matched the ring, scheme map, coefficient
sheaves and identification binders to the first sentence, `aU/aV/hc` to the two scalar
structures and their compatibility, and all six conjuncts to the prescribed module
structures and two additive linear operations. In particular, the two existential
structures are only module-category structures fixed sectionwise; the derived structures
are Mathlib's induced ones, so this does not weaken the node to arbitrary structures or
constant coefficients. `hc` uses the adjoint coefficient map on every site object and
keeps the same specified c. Both operation directions and both Additive clauses were
checked against their signatures. No mismatch was found and no node change was needed.
