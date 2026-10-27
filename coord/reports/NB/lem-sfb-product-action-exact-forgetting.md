## Worker report

The module `Sheaf.CategoryTheory.ProductActionExactForgetting` states
`Profinite.CondensedAction.ProductForgetting.exists_datum`. Its sole theorem has
`by sorry`; its docstring contains all seven accepted proof steps. All helper
constructions have real data. The structures are specifications of the asserted
normalized data; nothing is selected from the postponed existence theorem.
The natural-language statement, source, proof and proof dependencies are unchanged.

Source read: the current blueprint `literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and the item's
seven-step agent-extracted auxiliary calculation. The blueprint paragraph reduces
open direct-image preservation to the coefficient theorem; it does not itself state
this auxiliary categorical result. The node already records the combined external
reference as WANTED, and the module preserves that provenance. Also read
`sites-modules.tex`, labels lemma-extension-by-zero (03DI), lemma-j-shriek-flat
(03EV), lemma-sheafification-tensor (0GMW), and the recorded Lean interfaces for
exact derived factorization and the unbounded cohomology isomorphism criterion.
No statement fault or STATEMENT-DISPUTED claim was found.

Hypothesis and clause correspondence:

- Arbitrary commutative condensed R: `(R : Profinite.CondensedRing.{u})`
  and `[IsCommMonObj R.X]`. No presentation by a topological ring is assumed.
  `Modules R` is the recorded internal module category, not ordinary-ring
  `CondensedMod` and not an abstract action of the group of global sections.
- The size convention is explicit `universe u`: profinite test objects and groups
  have size u, coefficient sections have size u+1, internal modules and action
  objects have size u+2. The full ordinary derived localizations use
  `HasDerivedCategory.{u + 2}` and integer-indexed complexes, with no boundedness.
- G is a topological group with `CompactSpace`, `T2Space`, and
  `TotallyDisconnectedSpace`. J is a topological group. `hJ` is the disjunction
  of these three profinite properties and `Nonempty (J ≃ₜ* Multiplicative ℤ)`.
  Mathlib's topology on the multiplicative type tag of ℤ is the discrete integer
  topology. Using continuous group isomorphism admits every copy of Z_disc;
  it does not replace Z_disc by an arbitrary discrete group.
- The three action categories are exactly `ActionModule R G`, `ActionModule R J`,
  and `ActionModule R (G × J)`, using their existing local-parameter action.
  `Datum` supplies three Abelian structures. Each `ActionProperties.addition`
  requires its inherited addition to equal `actionPreadditive`;
  `grothendieck` and `enough` express Grothendieck abelianness and enough injectives.
  These are conclusions, not assumed Abelian or injective structures.
- Underlying kernels and sheafified cokernels: `ActionProperties.kernels` and
  `cokernels` preserve the finite limits/colimits under `forgetAction` followed
  by the recorded `sectionModuleFunctor`. `sectionKernels` explicitly preserves
  the kernel parallel pair after every section evaluation. `sheafCokernels`
  identifies the underlying module cokernel with ordinary module sheafification
  of the presheaf cokernel. Thus 'cokernel' does not mean the usually incorrect
  unsheafified pointwise quotient.
- Trivial-J inflation is the existing `inflate (ContinuousMonoidHom.fst G J)`;
  `inflationAdditive`, `inflationLimits`, `inflationColimits` express its exactness.
  `invariants : ProductInvariants R G J` is the already recorded normalized
  invariants specification: its image condition quantifies over every profinite
  base change and every kernel parameter, its inclusion is sectionwise injective,
  its residual action is (g,1), and its adjunction transposes restrict codomain
  and compose inclusion. No second fixed-section definition is introduced.
- U_J is `forgetFirst R G J`, defined literally as inflation along the inclusion
  `ContinuousMonoidHom.inr G J`. U_0 is the existing `forgetAction` on G-actions.
  `forgetting` and `plainForgetting` assert `ExactForgetting` for these precise
  functors. Its fields assert additivity, preservation of finite limits and
  colimits, reflection of isomorphisms, and preservation of injective objects.
- Derived conservativity is reflection of isomorphisms by the canonical
  `U.mapDerivedCategory`. This is the Mathlib termwise exact-functor localization
  on the full unbounded ordinary derived categories. The localizations are
  universally quantified, rather than assuming an arbitrary candidate functor
  or a comparison without a canonical map.
- Exact left adjoints: `induction : Induction R G J` and
  `plainInduction : PlainInduction R G` give functors, additivity, preservation
  of finite limits and colimits, and the specified adjunctions to U_J and U_0.
  Their `tensorIso` fields are natural isomorphisms with the actual tensor
  functor `tensorLeft (freeGroup R G)`. This pins maps as well as objects to
  tensoring the original morphism; no unrelated left adjoint is substituted.
- The action field of `Induction` says `(a,j)([g] tensor m) = [ag] tensor jm`
  after transport by that tensor comparison. Its `transpose` evaluates an
  induced equivariant map at `[1] tensor m`; `untranspose` extends a retained
  equivariant map by `[g] tensor m ↦ (g,1) f(m)`. Both equalities hold for every
  profinite S and continuous local g. `PlainInduction` has these same clauses
  with the ordinary internal module in place of the retained action.
- `freeGroup` is the existing `InternalBar.free` applied to the represented
  profinite object G via `uliftYoneda`. `generator` is its actual adjunction
  unit at a continuous map S→G. It is not chosen from an existence theorem.
  `extendedUnit` is literally module sheafification of
  `extensionByZeroPresheaf` applied to the unit module of `R.over G`.
  `extensionIso` identifies it with the free module and `extensionGenerator`
  sends the free adjunction's generator to the same direct-sum injection
  followed by sheafification. `flat : ObjectProperty.flat (freeGroup R G)`
  uses the existing internal exact-tensor predicate, requiring exact tensoring
  on either side, equivalent here by symmetry.
- Preservation of bounded-below injective resolutions is explicit in
  `ExactForgetting.resolutions`: for the actual quasi-isomorphism K→I, the
  actual termwise image map remains a quasi-isomorphism, each image term is
  injective, and every supplied lower degree bound b is retained. Taking K
  to be an object in degree zero gives precisely an injective resolution;
  the formulation also allows shifted bounded-below resolutions.

Dependency declarations and imports read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its action and
  compatible morphisms; `Modules R` is the recorded specialization.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `sectionModule`,
  `ActionModule`, `actionPreadditive`, `forgetAction`, `inflate`, `Fixed`,
  `ProductInvariants`, including the full signatures and docstrings.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRings`, `sectionRingSheaf`, `sectionModuleFunctor`,
  `sectionModuleEquivalence`, preserving underlying section maps.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`: the existing `free`,
  `freeAdjunction`, `onSections`, `pureTensor`. The free adjunction is owned by
  `def-sfb-condensed-free-module-adjunction`; no bar-resolution theorem is used
  to select a free object.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: the existing relative
  tensor `Mod.monoidalCategory`, `Mod.tensorObjπ`.
- `Sheaf.CategoryTheory.SheafTensorStructure`: the recorded sheaf tensor structure.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`: comparison infrastructure
  for the existing internal tensor and `Modules R` abelian structure. Its theorem
  remains the existing tensor comparison, not a newly chosen tensor definition.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  existing `cochainModulesMonoidal` localization tensor; no site universes equated.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: publicly exports the existing
  `CategoryTheory.ObjectProperty.flat` internal exact-tensor predicate.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, and ring `Sheaf.over` for localization.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf` and its direct-sum section construction.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `IsGrothendieckAbelian`; `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
  (reexported by Resolution): `Injective`, `EnoughInjectives`;
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`.
  `PreservesInjectiveObjects` comes from the corresponding `Preserves` module.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `ExactFunctor`: `mapDerivedCategory` and its canonical
  localization factorization, and the triangulated/shift structures.
- All already-stated proof dependencies are imported: the two sheaf-action
  infrastructure modules, Grothendieck enough injectives, extension-by-zero flatness,
  sheafification/tensor comparison, right-adjoint preservation of injectives,
  and `DerivedCategory.HomologySequence.isIso_iff`. Proof-only imports are plain;
  interfaces used by the statement are public. Flatness and tensor comparison
  imports use the upstream WeilConjectures modules, avoiding their retired twins.

The item's statement dependencies gain six already-landed nodes used explicitly
by this interface: `def-sfb-condensed-free-module-adjunction`,
`def-weil-presheaf-modules-sheafification`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`def-sfb-modobj-relative-tensor`, `det-def-sfb-sheaf-tensor-structure`, and
`lem-pe-internal-section-tensor-comparison`. These are existing notions, not new
nodes or dependency repairs. This is the permitted addition of landed interfaces;
no existing dependency is removed.

Edge cases checked: G=1 gives the represented singleton and the regular module;
J=1 gives the ordinary induction with the same formulas. The discrete infinite
cyclic J is not required compact or represented in the site. Only G enters
`Profinite.of G`. For empty test S, the unique empty continuous map is allowed;
there is no nonempty-test hypothesis. The zero ring makes all tensor symbols zero,
without any nontrivial-ring hypothesis. Zero modules, arbitrary lower bounds and
unbounded source complexes are allowed. There is no finite-group, discrete-module,
finite-coset, bounded-derived or topologically presented coefficient restriction.

Searches actually run on 2026-10-24 using `msearch.py NB` for this item:

- LeanFinder: “Forgetting a commuting profinite group action on internal condensed
  ring modules has an exact free induction left adjoint and is conservative on
  unbounded derived categories”. Eight hits, including `Condensed.profiniteFree`,
  `Condensed.freeForgetAdjunction`, light condensed free adjunctions and locally
  constant adjunctions. Read `Mathlib/Condensed/Module.lean`: these concern ordinary
  coefficient rings and are not an internal-condensed-ring action theorem.
- Loogle: `CategoryTheory.Functor.ReflectsIsomorphisms,
  CategoryTheory.Adjunction, Condensed.freeForgetAdjunction`: zero hits.
- Mathlib grep: `free.*[Ii]nduction|[Pp]roduct.*[Aa]ction|preservesInjectiveObjects`
  in CategoryTheory: 15 hits, including Action/Limits and the general preservation
  of injectives API. None is the product-action theorem. Read the relevant
  `Preadditive/Injective/Preserves.lean` signatures.
- LeanSearch: “Internal modules over a condensed ring forgetting commuting profinite
  action exact induction left adjoint conservative unbounded derived”. Eight hits;
  ordinary-ring free adjunctions, ModuleCat and TopModuleCat forgetful adjunctions;
  none states this internal action theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf`, by the item id,
  `ProductInvariants`, induction, exact forgetting and injective preservation.
  Also ran the prescribed `grep -rn` for the item id in WeilConjectures: no match.
  Existing `CondensedSplitCosetInduction` and `CondensedTensorInductionAdjunction`
  were read: their subgroup input is profinite and cannot cover a discrete infinite
  cyclic retained factor. `CondensedProductActionInflation` covers only profinite
  factors and omits exact induction and derived conservativity. The sibling
  `lem-sfb-condensed-action-injective-restriction` has no Lean record and likewise
  only profinite factors, with additional K-injective assertions. No exact match.
  The new declaration namespace was checked in both project roots: no collision.

Validation: `scompile.py` compiled the complete module cleanly in both sandbox
and library modes. The first compile diagnosed only elaboration issues: the
extension-by-zero and sheafification module universes needed explicit parameters,
and derived/resolution fields needed the same supplied Abelian structures. These
were repaired without mathematical hypotheses. Final declarations bind all
universes and variables with `autoImplicit false`; no warning remains. Only
`exists_datum` is postponed. Dry-run and delivery results follow from the prescribed
`deliver2.py` gate.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
