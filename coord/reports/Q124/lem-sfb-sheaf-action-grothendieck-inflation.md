## Worker report

The module Sheaf.CategoryTheory.SheafActionGrothendieckInflation states
CategoryTheory.InternalActionSite.sheaf_action_grothendieck_inflation. It constructs
restriction of actions directly and reuses the existing action category without a
second definition. Its six declarations are listed in lean.declarations. The main
theorem and its construction's naturality obligation have sorry proofs, each with the
source, blueprint tag, and complete natural-language proof. All data in the definitions
are real sectionwise data. ActionForgetExact and ActionInflationExact are Prop-valued
packages spelling out the conclusion, rather than additional mathematical assumptions.

Hypothesis and clause correspondence:

- Compatible coefficient/site universes: explicit universe u, C : Type u,
  SmallCategory C, and GrpCat.{u}, CommRingCat.{u}, and module values in u.
  The action category has objects in u+1 and homs in u. Grothendieck structure is
  IsGrothendieckAbelian.{u}. No independent smaller coefficient universe is used.
- A small site with finite limits: J : Precoverage C, hJ : J.IsSiteForCoverings,
  and HasFiniteLimits C; its sheaves use J.toGrothendieck. The site axiom is the
  recorded declaration, including existence of covering pullbacks as in Stacks 00VH.
- The commutative unital ring sheaf: S : Sheaf J.toGrothendieck CommRingCat.{u};
  baseRing forgets only commutativity when forming module sheaves. The ring has
  trivial action: LinearAction takes values in R(U)-linear endomorphisms and never
  applies a group action to coefficients.
- The group sheaf K: K : Cᵒᵖ ⥤ GrpCat.{u} and hK gives its underlying-set sheaf
  condition. The same binders L and hL supply any other group sheaf.
- The category E_K(R): the existing EquivariantSheaf, whose underlying object is
  an EquivariantPresheaf with a module-sheaf condition. LinearAction.act is a monoid
  homomorphism to Module.End, encoding unit, associativity, additivity, and R-linearity.
  LinearAction.naturality is the restriction equation. Morphisms are the existing
  equivariant linear natural maps. Their inherited preadditive structure is sectionwise
  addition in the existing homGroup, inherited by the full subcategory.
- Grothendieck abelianness with that specified addition: existential Abelian structures
  aK and aL, with aK.toPreadditive and aL.toPreadditive explicitly equal to the inherited
  Preadditive instance; @IsGrothendieckAbelian uses those exact abelian structures.
  This states colimits, a generator and AB5 via the dependency's Mathlib class.
- U_K: exactly the existing forgetSheaf. ActionForgetExact.additive records its
  sectionwise addition. Its createsKernels and createsCokernels fields use
  CreatesLimit/CreatesColimit of parallelPair f 0, with no replacement forgetful map.
- Kernel formula: sectionwiseKernel says ordinary module-sheaf evaluation preserves
  the underlying kernel diagram. Together with creation this gives the sectionwise
  kernel with the unique induced action and kernel map.
- Cokernel formula: sheafifiedCokernel identifies the underlying cokernel with
  PresheafOfModules.sheafification (𝟙 S.obj) of the underlying presheaf cokernel.
  Presheaf cokernels are sectionwise. Together with createsCokernels this gives the
  induced action and universal cokernel map, including its sheafification.
- Exactness and zero detection: ActionForgetExact.finiteLimits, finiteColimits,
  exact_iff on every ShortComplex, and zero_iff. Consecutive ShortComplex.Exact is
  precisely the recorded exact-sequence convention, hence covers arbitrary complexes.
- Any morphism θ : L ⟶ K: a natural transformation of group-valued functors, i.e.
  a restriction-natural family of group homomorphisms. It need not be surjective.
- Inflation construction: restrictLinearAction.act X is (a.act X).comp (θ.app X).hom.
  inflateSheaf keeps M.obj.val, M.property, and f.hom.val verbatim. Its action is
  therefore l ↦ θ_X(l) acting on the original module, at every section.
- Additive exact inflation and preservation of displayed kernels/cokernels:
  ActionInflationExact.additive, finiteLimits, finiteColimits, and exact. Finite-limit
  and finite-colimit preservation includes the kernel/cokernel diagrams, with their
  arrows. The actual functor fixes underlying objects/maps, so the induced action on
  each displayed kernel and sheafified cokernel is the θ-precomposed action.

Dependencies read and used:

- def-weil-size-convention: metatheoretic convention, expressed by the explicit universe.
- Sheaf.CategoryTheory.SiteCoveringAxioms:
  CategoryTheory.Precoverage.IsSiteForCoverings.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently SheafOfModules and its existing morphisms.
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic:
  CategoryTheory.IsGrothendieckAbelian, read with its full class and universe signature.
- Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification:
  PresheafOfModules.sheafification, specialized along the identity coefficient map.
- Sheaf.CategoryTheory.InternalActionSitePresentation: LinearAction,
  EquivariantPresheaf, EquivariantSheaf, forgetSheaf, baseRing and the inherited
  equivariantPreadditive, all in CategoryTheory.InternalActionSite. These are now
  owned by def-sfb-internal-equivariant-module-sheaves, the new definition node
  in stmt_deps. The presentation theorem remains only in proof_deps.
- Proof imports: WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
  (SheafOfModules.grothendieckAbelian_with_localized_generator);
  Sheaf.Paper.ExactFamilyDetection (CategoryTheory.exact_family_detection);
  Mathlib.CategoryTheory.Adjunction.Limits (the equivalence-preserves-limits/colimits
  declarations); Mathlib.Algebra.Homology.ExactSequence (the exactness convention).
  Abelian is supplied by the public Grothendieck-category import. The still unstated
  lem-sfb-equivariant-module-sheafification-reflector has no import; its compatibility
  is already available in Presentation.adjunction, baseComparison and base_unit.
  No construction waits on that proof dependency.

Edge cases checked before writing: K or L trivial has the unique unital action; θ
can have any kernel/image; nonabelian section groups are allowed; no invertibility or
surjectivity assumption was added on θ. With the zero ring every section module is
zero; neither the definitions nor the theorem requires Nontrivial. An empty base
category or empty covers introduce no excluded object or section. Finite-limit
hypotheses are exactly the node's, and no finite-limit structure on the action site
is assumed. The main theorem applied with L=K and θ the identity yields the K-only
assertions, so packaging both group instances does not strengthen the universal claim.

Existing-statement searches:

- msearch.py leanfinder, "Sheaves of modules with an internal group action form a
  Grothendieck abelian category and restriction of group actions is exact": eight hits
  for ordinary sheaf/condensed module abelianness and Grothendieck structure. None gives
  the internal sheaf-group actions, forgetful creation/detection, or exact inflation.
- msearch.py loogle, '"SheafOfModules", "IsGrothendieckAbelian"': ordinary
  PresheafOfModules.instIsGrothendieckAbelian and SheafOfModules.instIsGrothendieckAbelian,
  neither the action-category assertion.
- msearch.py grep, 'equivariant|inflation' in Algebra/Category/ModuleCat: zero hits.
- rg of lean/WeilConjectures/CategoryTheory for equivariant/inflation/InternalAction
  and rg of the exact node id in lean/WeilConjectures: no matching general statement.
  Existing point-fiber actions are actions of one external group, not this internal
  sheaf-group action category.
- rg of lean/Sheaf found InternalActionSitePresentation, reused verbatim, and condensed
  specializations, which do not already state this general small-site assertion.

There is no statement correction and no STATEMENT-DISPUTED fault. The earlier Q10
review is a stage-1 split review; the live node had no lean record. This delivery adds
that missing stage-2 record and its actual module, rather than resubmitting an unchanged
stage-1 node.

Validation: scompile.py compiled both the isolated sandbox form and the named module
against the live published library, cleanly with no warnings. No global build, direct
live-library edit, or direct git operation was run.


## New nodes

def-sfb-internal-equivariant-module-sheaves records existing:true ownership of
LinearAction, EquivariantPresheaf, Equivariant, homGroup, the category and additive
instances, EquivariantSheaf, forgetPresheaf, inclusion, forgetSheaf and baseRing in
Sheaf.CategoryTheory.InternalActionSitePresentation. Its source is the item's
agent-formulated categorical input to paragraph (3) of the direct-images proof.
The full definitions were read in the existing module: the new node states the
monoid action and its restriction equation, the equivariant linear-map subgroup,
the inherited sectionwise addition, the full subcategory satisfying the module
sheaf condition, and the literal underlying-object/map forgetful functors.
It also records forgetting commutativity of the coefficient sheaf. The existing
code allows any group presheaf; its sheaf-group specialization is exactly the
category used by the item. No extra theorem or new Lean module is introduced.

The repair searches were msearch.py LeanSearch for "Category of sheaves of modules
with natural linear actions of a sheaf of groups and equivariant morphisms"
(eight ordinary module-sheaf/category results), Loogle for '"SheafOfModules",
"Action"' (zero hits), and Mathlib grep for
'EquivariantSheaf|LinearAction|equivariantPreadditive' (zero hits). The raw JSON
results are retained in mathlib_searches. Project rg found the exact existing
InternalActionSitePresentation declarations; upstream rg found only external
point-fiber group actions. DAG rg found the presentation theorem's helper list,
but no owning definition node. blueprint_refs.py search equivariant had 44
matches and no separate owner; ancestor of the item returned None. Thus the new
node registers the existing definitions without repeating them.

## Second reading by Q124

Repair self-check, with the current node, its five original definition dependencies,
the saved Lean module, and the new ownership node open: the returned H2/theorem
stmt_dep fault is repaired by replacing the added theorem dependency with
def-sfb-internal-equivariant-module-sheaves. The live five stmt_deps are retained;
lem-sfb-internal-action-site-presentation remains in proof_deps. The current
read-clone node has been used as the base, retaining only the saved lean record
and the authorized new definition dependency. All original statement, source,
proof and proof_deps fields remain equal to that base.

The explicit universe, finite-limit site, group-sheaf conditions and commutative
ring sheaf binders still give every hypothesis. LinearAction and the new owner
supply the action, its laws, restriction naturality and trivial coefficient
action. EquivariantSheaf and equivariantPreadditive supply the category and its
specified addition. The two existential Abelian structures require exactly that
addition and Grothendieck structure. ActionForgetExact supplies creation of
kernels/cokernels, evaluation of kernels, sheafified underlying cokernels,
exactness and zero detection. inflateSheaf literally retains the modules and
maps and precomposes each action by the given natural group homomorphism;
ActionInflationExact supplies additivity and exactness, including preservation
of kernel and cokernel diagrams. Trivial K/L, zero coefficients and arbitrary
non-surjective group-sheaf morphisms remain admitted. There is no mathematical
statement change. The review's cokernel-comparison advisory is recorded: its
Nonempty isomorphism field is accompanied by creation of the cokernel diagram;
this ownership repair preserves the already accepted interface.

The new node's record lists only existing definitions and instances, with the
EquivariantSheaf signature copied verbatim, and no file field. No dependency
module is needed. This is the worker's self-check; the maintainer's independent
stage-2 review remains the independent reading.
