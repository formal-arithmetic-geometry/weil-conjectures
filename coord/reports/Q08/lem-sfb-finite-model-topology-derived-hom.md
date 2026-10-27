## Worker report

This delivery states `lem-sfb-finite-model-topology-derived-hom` in
`Sheaf.Paper.FiniteModelTopologyDerivedHom`, namespace
`AlgebraicGeometry.ProEtale.FiniteModelTopologyHom`. Every theorem has proof `sorry`;
all helper definitions contain actual constructions. Canonical maps are defined in
`Sheaf.Paper.FiniteModelTopologyComparisonMaps`, owned by the new definition node
`def-sfb-finite-model-topology-comparison-maps`. The primary theorem is
`finiteModelTopologyDerivedHom`. Its docstring includes all eight DAG proof steps.
The item's natural-language statement and proof are unchanged; its statement
dependencies gain only that definition node.

The previous attempt concerned the stage-1 review by NW. That review is present, but
there is no Lean record on this item. This delivery supplies its stage-2 statement;
it does not attempt another stage-1 split. The preserved sandbox was empty.

Hypotheses, objects and clauses:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The base field, positive prime
  characteristic and distinct coefficient prime are `{k : Type u} [Field k]`,
  `(p : ℕ) [Fact p.Prime] [CharP k p]`, and `hpℓ : p ≠ ℓ`.
- `X : Scheme.{u}` and `a : X ⟶ Spec (CommRingCat.of k)` with
  `LocallyOfFiniteType a`, `QuasiCompact a`, `IsSeparated a` mean precisely a
  separated finite-type k-scheme. The setting dependency is represented by explicit
  binders, as its own record directs; compactification data are not needed here.
- The existing algebraic-closure convention is `PadicAlgCl ℓ`, with its extended
  norm, and `E : PadicAlgCl.FiniteIntermediateField ℓ` is any finite intermediate
  field, with the inherited norm. This is the same algebraic-closure model used by
  the recorded coefficient dependencies. It imposes no completeness assumption.
- C is `Profinite.padicAlgClRingObj ℓ`, the sheaf of continuous functions valued in
  a finite intermediate field. B is `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`.
  The latter is the coefficient-universe-zero specialization of the recorded
  `continuousMapRingObjOfUniverse` construction, definitionally the same sheaf.
  They are distinct constructions. The map is the existing
  `NormAlgclComparison.coefficientInclusion`; its pullback is `inclusionOnScheme`.
- The site is exactly `Scheme.ProEt.topology X`, with objects in universe u+1 and
  morphisms in u. The abelian sheaves and internal modules have coefficients in
  u+1. No site-universe equality is imposed.
- A is `condensedRingObj (Profinite.continuousMapRingObj E) X`. The K,N binders
  are in `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) A)`;
  this is ordinary unbounded localization, not a complete subcategory.
- `hK` and `hN` use exactly `constantModelBoundedConstructible`, with finite
  constant scalar presentations, not the more general local-finite-presentation
  predicate. No Tor-amplitude or site-perfectness assumption is used.
- `CondensedRing.internalScalarExtension` is the existing total left derived
  scalar extension. `toUnion` and `toNorm` name its S_C and S_B specializations.
  `scalarAdjunction` is a typed reference to the existing derived
  extension/restriction adjunction gives the unit. `reassociation` is the unique
  comparison of left adjoints to the specified composed restriction functor;
  its adjunction-unit normalization is multiplication of scalar factors.
- `finiteHom` names D, `unionHom` and `normHom` name the displayed scalar-extended
  Hom objects. These are direct specializations of the recorded derived Hom.
  D is the actual object
  `((CondensedRing.derivedHom (Profinite.continuousMapRingObj E) X).obj (op K)).obj N`.
  The primary theorem's first two conjuncts give its finite-constant-model
  bounded constructibility and its stratified-lfp bounded constructibility.
- The third conjunct, `QlbarInternalHom.Continuous X ℓ E K`, is the full existing
  strict-representative continuity predicate, not just a comparison of abstract
  endpoints. Unfolding its recorded definition quantifies over every representative
  P of K under the exact section-module equivalence, every coefficient-small
  filtered category I, and every strict diagram with a common termwise lower
  bound. Its conclusion is `QuasiIso (colimit.post M (homFixed ... P))`, the
  actual evaluation-induced map on exact termwise sheaf colimits of functorial
  Hom representatives. Thus it gives the derived isomorphism, not only separate
  isomorphisms of its cohomology objects.
- `homComparison` is phi for a coefficient morphism. It is the tensor-Hom mate
  of the inverse of `CondensedRing.internalScalarTensorIso`, so it is the specified
  scalar-extended evaluation transpose. The native adjunction uses K tensor D; the symmetric Koszul
  braiding identifies it with the displayed D tensor K convention. The published
  tensor comparison is the bifunctor-derived lift of the ordinary uniquely
  scalar-unit normalized monoidal structure. Full signature checks confirmed that
  both `internalScalarExtension` and `internalScalarTensorIso` omit the source
  section's unused exactness variable. They therefore apply directly to C to B
  without a flatness assumption. The Hom mate here uses those exact declarations.
- The next two conjuncts assert `IsIso` of these actual phi_C and phi_B maps in
  their respective derived internal-module categories. `homComparison_naturality`
  supplies their naturality under precomposition in K and postcomposition in N.
- `restrictionMate`, `globalize`, `restrictionComposition`, `restrictTowerMap`,
  `towerHomComparison` and `evaluationRoute` are generic composites of the imported
  adjunction, restriction, Hom, reassociation and sections maps. Their full data
  are written out before specializing to E,C,B; there is no assumed comparison.
- `coefficientComparison` is the C-linear m_V: the scalar unit for C to B followed
  by `reassociation`. On K-flat models its formula is z tensor v to c_X(z) tensor v.
  `finiteCoefficientComparison` restricts this map to A and applies the canonical
  comparison for the two successive exact restrictions. This is the A-linear m_D
  of the statement; it is not an arbitrary map between scalar-extended objects.
- `sections` forgets the internal module action exactly, then applies the ordinary
  total right derived functor of abelian sheaf global sections. `restrictionSections`
  is the canonical composition isomorphism of the exact forgetful functors,
  followed by derived global sections. It supplies the prescribed identifications
  before and after coefficient restriction. `finiteCoefficientComparison_sections`
  states their square for the actual m_V. The primary theorem asserts invertibility
  both in the C-linear presentation and for R Gamma of the A-linear m_D.
- `inducedHom` applies J to evaluation, transposes, and transports its two inputs
  with the canonical JS_C to S_B reassociations. `globalHomComparison` inserts
  the scalar unit and takes sections using `restrictionSections`. It is the actual
  Psi induced by J, not a freely supplied morphism or an existential isomorphism.
- The primary theorem's penultimate conjunct is exactly
  R Gamma(phi_C) followed by Psi equals R Gamma(m_D) followed by R Gamma(phi_B),
  using the canonical coefficient-forgetting identifications. Its last conjunct is
  `IsIso` of Psi in the unbounded derived category of abelian groups.
- `scalarExtendedEvaluation` is the equality before taking sections: after
  reassociation, J(phi_C) followed by the actual induced Hom map is phi_B.
  `evaluationRoute` is exactly this composite, expanded in its definition.
  Both evaluation transposes are B tensor_A evaluation by the definition of
  `homComparison`. This states equality of actual maps, not just their endpoints.
- `globalComparison_naturality` gives both Psi's contravariant/covariant naturality
  and m_V's naturality. Naturality holds for all derived arrows of these inputs;
  it does not require the arrows themselves to have finite models.
- `sectionRingComparisons` applies the recorded exact, underlying-sheaf-preserving
  `ModuleObjectRingedComparison.forward` to the two phi maps and to the equality
  of their scalar-extended evaluation maps. Thus it retains the same actual
  comparisons in the section-ring model. The imported normalized derived
  tensor-Hom comparison identifies these with the section-ring Hom and evaluation.
  Global sections are the same after the equivalence's canonical comparisons,
  because the underlying abelian sheaves and maps are preserved.
- No flatness of C_X to B_X, site-perfectness, completeness of the closure, or bound
  on the cohomological dimension of the base field is a binder anywhere.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the explicit finite-type setting convention and
  `CondensedRing.isMonoidalClosed_boundedConstructible` (proof input).
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, their finite-valued
  presheaf construction; `...Condensed.FiniteSubextension` supplies
  `PadicAlgCl.FiniteIntermediateField` and `padicSubfieldRingObjToPadicAlgCl`.
- `Sheaf.Topology.ContinuousMapCondensedRing`: the universe-polymorphic
  continuous-function ring sheaf; `Sheaf.Topology.ProfiniteCondensedRing`:
  `Profinite.CondensedRing`, retaining the same continuous-map constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`; the existing
  `...ChangeOfCoefficients.coefficientMap` is its action on maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its internal action,
  regular module, action-compatible maps and restriction functor.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the arbitrary-resolution total right-derived convention; on these Grothendieck
  categories the published `Functor.rightDerivedFunctor` is used directly.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction`, exact restriction and its
  specified units; `...LeftDerivedFunctor.Monoidal.leftDerivedTensorComparison`
  is the general K-flat tensor comparison without exactness of extension.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `IsConstantModelConstructible`.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` reexports the
  original general `boundedConstructible` predicate, which is the one used here;
  its separate discrete-coefficient specialization is not substituted for it.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`, `derivedTensorHomAdjunction`, and the existing native
  relative derived tensor and closed structure.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, its cocone and canonical
  map; `Mathlib.CategoryTheory.Filtered.Basic.IsFiltered`; and
  `Mathlib.Algebra.Homology.HomologicalComplex.CochainComplex` through the
  existing strict continuity predicate.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  the unbounded R Gamma/H0 convention. Here the result is kept in D(Ab), before H0.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence`, through the exact
  `ModuleObjectRingedComparison.forward` of
  `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`.

Every stated proof dependency is imported, privately where used only in the proof.
These include `DerivedSectionsScalarCoherence`, `InternalSectionTensorComparison`,
`AdicConstructibilityPredicateComparison`, `ConstructibleInternalHomContinuity`,
`ScalarInternalHomAdjunction`, `QlbarInternalHomCoefficientComparison`,
`ModuleObjectRingedSiteDerivedComparison` and `RingedDerivedMonoidalComparisons`.
The norm-topology cohomology module is public because its actual coefficient maps
are used in the statement. The norm internal-Hom base-change proof node has no
recorded Lean declaration in the read snapshot, so there is no module to import
for that proof-only input. Likewise finite-type-over-Noetherian is a Mathlib leaf.
No missing notion is replaced with an assumption.

Edge cases checked before writing:

- Empty X: every internal module object and map is zero; all conclusions have the
  required zero or unique isomorphism interpretation, with no nonempty X binder.
- K or N zero, shifts of zero, and negative cohomological degrees: ordinary
  unbounded derived objects and relative Hom retain these cases.
- E equals Q_ell, K=N=A, and a geometric point: the coefficient comparison reduces
  to the actual finite-valued-to-continuous coefficient inclusion on derived sections;
  it does not assert that the coefficient sheaves themselves are isomorphic.
- A constant one-object filtered diagram and a zero diagram: continuity is the
  identity/zero comparison on the prescribed representatives. Empty diagrams are
  excluded only by the mathematical definition `IsFiltered`, as in the node.
- No uniform cohomological bound on k is used. Characteristic p is positive prime
  and distinct from ell, exactly as in the setting.

Searches:

1. `msearch.py` LeanFinder: “Derived global Hom of bounded constructible finite
   p-adic coefficient sheaves unchanged from finite-subextension valued coefficients
   to continuous norm algebraic closure coefficients”. Eight hits: BDeRham,
   BDeRhamPlus, LightCondensed.ihom_map_val_app, Condensed.profiniteSolid,
   InfiniteGalois.finGaloisGroupFunctor_map_proj_eq_proj, Condensed.profiniteFree,
   LightCondensed.ihomPoints_symm_comp, InfiniteGalois.algEquivToLimit. None states
   this derived Hom topology comparison or the specified map equality.
2. `msearch.py` Loogle: `"DerivedCategory", "hom"`. Twelve hits, all localization,
   essential-surjectivity, shift and single-functor facts; none compares these rings.
3. `msearch.py` grep:
   `(Condensed|Proetale).*(internalHom|internal_hom)|(internalHom|internal_hom).*(Condensed|Proetale)`.
   Zero hits in Mathlib.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the coefficient-topology and
   Qlbar/NormAlgcl internal-Hom terminology found the existing comparison inputs
   used above, but no declaration stating this item. Exact searches for the item
   id, `FiniteModelTopologyHom`, `finiteModelTopologyDerivedHom` and
   `finite_model_topology` found no existing declaration. The upstream declaration
   index also has no exact item or proposed-name match.
5. The blueprint paragraph and all statement-dependency statements/Lean records
   were read, along with the declarations and docstrings in their recorded sources.
   Current server source of `LeftDerivedFunctor.Monoidal` was also read using
   `scompile.py --source`; it confirms the general tensor API has no exactness binder.
   In addition, `#check @CondensedRing.internalScalarExtension` and
   `#check @CondensedRing.internalScalarTensorIso` confirmed that the published
   specializations have no exactness binder either (diagnostic file removed).

## New nodes

`def-sfb-finite-model-topology-comparison-maps` defines the actual evaluation
transpose, coefficient-tower reassociation, A-linear coefficient inclusion, and
J-induced derived global Hom map required by the item's own statement and proof
steps 7–8. Its module has real definitions only, with no postponed theorem or data.
The theorem and its naturality/evaluation/section-ring companions remain in the
item's module. This gives these canonical arrows one owning definition node;
it does not introduce a new tensor, internal Hom, scalar extension, or R Gamma.
The source is the item's agent topology-comparison obligation, with constituent
constructions from Stacks 07A4, 08J9, 0D6D and 0D6E.

Searches for this definition: LeanSearch's canonical K-flat scalar-extension and
global-Hom query returned ordinary ModuleCat scalar adjunction and dual transpose
facts; LeanFinder's scalar-tower derived-Hom query returned light-condensed underived
Hom and ordinary ModuleCat change-of-rings facts; the Mathlib regex search returned
unrelated topology statements. The exact search responses are recorded in the new
node's `mathlib_searches`. Searches of both project source trees for the proposed
map names found no exact declaration. The existing Qlbar evaluation comparison has
an explicit exactness binder and does not define the C-to-B global Hom arrow.
`lem-sfb-scalar-internal-hom-tower-coherence` concerns section-ring scalar-Hom models,
not these native coefficient-topology maps; `lem-sfb-internal-scalar-mate-transitivity`
concerns pushforward mates and has no Lean attachment. The imported scalar tensor,
scalar adjunction and module equivalence declarations are reused.

The whole-blueprint search `scalar topology Hom` returned
`cor-galois-lisse-representations`, `def-weil-pbc-adic-coefficient-datum`,
`sk-def-sf-operations`, and `sk-def-sp-scalar-extension`; none defines these arrows.
`blueprint_refs.py ancestor` reports no blueprint ancestor for the existing agent
obligation, so the new node retains that null ancestor and prepends the item to its
existing provenance chain. Its chapter and unit match the item.

No statement correction or disputed mathematical claim is proposed. This remains
an agent-created obligation with exact literature proof wanted, as the source record
explicitly says; the Lean docstring does not attribute it directly to the blueprint.

Validation: the prescribed `scompile.py` compiled both delivered files separately
against the live published library, including their real module names. The map
module finished in 40.1 seconds and the theorem module in 54.1 seconds, with no
errors or warnings. There are 25 real helper definitions in the definition module
and six named theorem statements with `sorry` in the item module. Diagnostic files
have been removed. The prescribed `deliver2.py --no-push` dry run passed both
preflight and compilation (reviewable dry-run commit `84bc4fd2d6b`). The delivery
command repeats those checks before pushing the packet for independent review.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
