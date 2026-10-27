## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidModuleDescentTensorCokernel` states
`CategoryTheory.groupoid_module_descent_tensor_cokernel`, with `sorry` as its whole
proof. Its docstring gives all eight proof steps. The original statement is unchanged.
Two already-landed definitions are added to stmt_deps: the groupoid module and the
scheme-groupoid quotient presentation. The pullback-tensor statement is also added because its uniquely normalized
construction occurs in the signature. A new definition node owns section-universe
chart restriction and the normalized scheme section/unit helpers. The big-fppf
equivalence remains solely a proof dependency.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; `U R : Over S` and `s t : R ⟶ U`
  retain their S-structures. `e`, `i`, `c` are the given scheme maps. Their laws are
  `P.groupoid : Scheme.IsGroupoid ...`. No flatness, finiteness, smoothness, DM,
  algebraicity, or finite-generation assumption occurs.
- The quotient X and canonical object a are `F`, `a` and
  `P : SchemeGroupoidQuotientPresentation ... F a`. This existing definition says
  exactly that F is the fppf stackification: its arrows are the presenting arrows,
  composition is c, and every object lifts fppf locally. It retains a and the
  particular arrow two-isomorphism; it is not an arbitrary equivalent category.
- Modules on X are `ringedSiteModules (moduliSmallRings F P.stack.1)`; quasi-coherence
  in `ModuliSmallQCoh` is Mathlib `SheafOfModules.IsQuasicoherent`, i.e. local
  presentations by arbitrary small free modules, with all linear maps.
- Scheme modules are the already-landed `Scheme.GroupoidModule`. Its `moduleObj`,
  `quasiCoherent`, `unit`, and `cocycle` give all the stated data and equations.
  It stores `beta : t*M ≅ s*M`; the node's delta is exactly `beta.symm`. Inverting
  its cocycle yields delta_c = delta_first after delta_second. `Hom` retains every
  intertwining module map, and its identity and composition are underlying ones.
- `E` is the categorical equivalence, `j` identifies its underlying functor with
  actual restriction `groupoidDescentAtlas`. `moduliChartModuleRestriction`
  evaluates on the chart's open subschemes, on both objects and maps.
- The equivalences `b M T x` identify Gamma(T,x*E(M)) with the literal value of M
  at a(x). Their clauses specify scalar linearity, naturality in module maps,
  restriction along every special scheme arrow, transport along every original
  groupoid arrow, and agreement with j on opens. Thus E is the restriction and
  its datum is induced by P.arrows, not just an abstract equivalence.
- The existential `hQ : ObjectProperty.IsMonoidal ...` asserts that the ambient
  structure module and ambient tensor products are quasi-coherent. Mathlib's full
  monoidal subcategory inherits the very same associators, unitors and symmetry.
- The existential monoidal and symmetric structures on the datum category are
  constrained by `h0`, `hMN`: their underlying module is exactly O_U and M tensor N;
  their beta is exactly `groupoidDescentUnitBeta` and `groupoidDescentTensorBeta`.
  The forgetful tensorator and unit are precisely the equality comparisons, so
  the structure is the underlying module tensor structure, not an arbitrary one.
- The functors forgetting the datum, restricting to the atlas, and E are `Braided`;
  hence their invertible tensorators respect associativity, both unit constraints,
  and symmetry. `NatTrans.IsMonoidal j.hom` identifies their tensor comparisons.
  The unit and local pure-tensor formulas normalize the atlas comparison canonically.
- For every map f, `hK` asserts that its cokernel formed in all module sheaves is
  quasi-coherent. The isomorphism k identifies E of that ambient cokernel with the
  cokernel of the underlying map on U, and the equation on cokernel.π identifies
  their cofork maps. These imply the full-subcategory cokernel universal property;
  equivariance of E of π and its cokernel universal property determine the induced
  descent datum uniquely. No exactness/flatness of s* or t* is assumed or claimed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` and fppfPrecoverage.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`, full laws.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`: `Scheme.GroupoidModule`, its
  unit/cocycle comparisons, Hom, and forgetToModules (beta convention read in full).
- `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`:
  `SchemeGroupoidQuotientPresentation`, `schemeGroupoidPresentationArrow`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliFppfTopology`,
  `moduliSchemeForget`, `moduliStructurePresheaf`, `moduliStructureSheaf`,
  `moduliModuleRings`, `IsQuasicoherentModuliAlgebra` and their section universes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: its public Mathlib
  `SheafOfModules.IsQuasicoherent` is used for local presentations; its QCoh
  specialization concerns algebraic spaces and is deliberately not substituted for
  stack quasi-coherence. The scheme specialization uses the same Mathlib predicate
  publicly exposed by `Sheaf.AlgebraicGeometry.CoherentFiniteType`.
- `Sheaf.CategoryTheory.RingedSiteModules`: the transparent ringedSiteModules alias.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: tensorPullback,
  tensorPullbackSectionAdjunction, tensorPullbackSectionComp and tensorPullbackSectionId.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: existing tensor
  localization and its inherited upstream `SheafOfModules.monoidalCategory`,
  symmetricCategory, tensorObjIsoSheafification; the localized tensor is retained.
- `Sheaf.AlgebraicGeometry.StackModuleRestriction`: moduliChartModuleRestriction,
  moduliSmallRings, ModuliSmallQCoh and stackModulePullbackUnit,
  stackModuleSectionPullback, stackModuleOpenSection. The last three are actual
  constructions directly from tensorPullbackSectionAdjunction, not from the big-fppf
  comparison theorem.
- `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`: the full comparison
  theorem, retained as a plain proof-only import.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`: module_pullback_tensor,
  whose pure-tensor normalization fixes groupoidDescentPullbackTensor.

All recorded proof-dependency modules available in the source are imported, with
proof-only imports plain and actual signature dependencies public. The unrecorded
stackification-module-equivalence and convention node have no module to import.
The missing section-universe chart interface is owned by the new definition node
`def-sfb-stack-module-restriction`. The preexisting stack-algebra node is untouched.

Sources read: Stacks stacks-sheaves.tex proposition-quasi-coherent (06WT), including
the entire section formula and the quotient-prestack arrow direction; lemma-qc-colimits
(06WN)(1),(2), including the slice argument; lemma-compare-quasi-coherent (0GQD).
The SchemeGroupoidModule docstring and actual formulas fix composition and beta
orientation. These sources are present locally; no internet fetch was needed.

Searches actually run with msearch.py (NV, this item):

- leanfinder, `quasi coherent module descent scheme groupoid quotient stack tensor cokernel`:
  eight generic local-presentation/module-colimit hits, no descent equivalence.
- loogle, `SheafOfModules, CategoryTheory.Equivalence, Scheme.IsGroupoid`:
  zero hits, unknown identifier Scheme.IsGroupoid in the search service.
- grep, `groupoid.*[Mm]odule|[Mm]odule.*[Gg]roupoid|quotient.*[Ss]tack`:
  zero Mathlib hits.
- leansearch, `Pullback functor sheaves of modules on ringed spaces with independent module universe`:
  eight generic pullback/adjunction hits. These were inspected for universe handling.
- rg over lean/WeilConjectures and lean/Sheaf for groupoid/module and quotient/stack:
  found and reused SchemeGroupoidModule, SchemeGroupoidQuotientPresentation, and
  the downstream affine algebra-descent consumer; no existing exact theorem.
- grep of the item id in lean/WeilConjectures: no matches.

Edge cases checked: empty schemes and empty indexing sets (no nonemptiness binder),
zero modules/maps and identity maps, identity groupoid (unit law reduces to identity
pullback), a nonflat groupoid (only cokernels, not kernels, are asserted), arbitrary
ranks and presentations, positive characteristic, and arbitrary independent total-
category object and arrow universes. The scheme section universe is the same as
Scheme.Modules and is not equated with either total-category universe. Inverting
beta preserves all morphisms and gives the node's stated delta convention.

## New nodes

`def-sfb-stack-module-restriction` owns `StackModuleRestriction.lean` and its 24
recorded declarations. Its primary definition is `moduliChartModuleRestriction`.
For every fibred category F over S-schemes and based scheme chart a, it evaluates
modules on chart opens, on objects and all morphisms, with the canonical regular-
function scalar comparison. The existing stack-algebra interface has lifted
coefficients in max (u+1) v w; scheme/groupoid modules have section universe u.
This node supplies the same unlifted regular rings, local-presentation predicate,
canonical localization tensor, symmetry, and ambient cokernels without equating
those universes. The coefficient identification is valuewise ULift.ringEquiv.

The new node also owns `stackModuleSectionPullback`, `stackModuleOpenSection` and
`stackModulePullbackUnit`. Their real data are respectively the normalized
adjunction unit with restriction to top, its open-subscheme version, and
leftAdjointUniq followed by pullbackObjUnitIso. No data are postponed. Every
supporting postponed theorem has this new owner in its source/proof docstring;
the node explicitly states the associated sheaf, sheafification, slice, tensor
localization and cokernel obligations. The sheafification docstrings specify the
small cofinal fppf refinement by affine finitely presented covering pieces.

New-node searches (2026-10-24), with exact outputs stored in mathlib_searches:

- leansearch: `Restriction of sheaves of modules on a fibred fppf site to scheme charts with unlifted structure coefficients`;
  eight generic module restriction/change-of-rings hits, no full interface.
- leanfinder: `Unlifted structure sheaf on a fibred category and restriction to a scheme chart`;
  eight regular-function/open-restriction hits; restrictFunctorΓ is reused.
- msearch grep: `moduliSmall|moduliOpenChart|moduliChartModuleRestriction|stackModuleSectionPullback`;
  zero Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for the new helper names: no published
  declarations. A DAG search for chart module restriction found no owning node.
- blueprint_refs.py search `chart module restriction`: zero blueprint nodes;
  ancestor of the item is None, retained with its complete inherited via chain.

## Returned delivery repaired

1. H13: restored `def-sfb-stack-quasi-coherent-algebra.json` byte-identical to
   current side-live, retaining Q113's StackQuasiCoherentAlgebra module, primary
   IsQuasicoherentModuliAlgebra and all 38 declarations. No existing dependency is
   rebound. The needed 24-declaration interface now has the independent definition
   node above, added to the item's stmt_deps.
2. H2: removed lem-sfb-scheme-big-fppf-quasicoherent-equivalence from stmt_deps and
   changed its import to plain proof-only. Replaced all three uses of its plain
   helpers with the new definition-owned constructions above, directly from
   def-pc-module-pullback. The dependency remains in proof_deps unchanged.
3. The accepted module_pullback_tensor construction and dependency are retained.
   The mathematical statement, j/b normalizations, beta inverse convention,
   coherent canonical tensor clauses, ambient cokernel clause and all independent
   universes remain as independently reviewed at d78c5e477fcd.
4. Advisory: all four sheafification/local-bijectivity docstrings now explicitly
   mention the small cofinal fppf refinement.

## Author verification

Author self-check; the maintainer's independent mathematical review is still required. Reopened the node,
its dependencies and both files after compilation. Checked each correspondence
above against the actual signature, with special attention to source/target order,
all module maps, ambient rather than abstract QCoh cokernels, and canonical tensor
comparisons. Found and fixed: the first tensor statement only asserted braided
functor structures without pure-tensor normalization; explicit atlas unit and
pure-tensor equations now fix the canonical comparison. The forgetful tensorators
are fixed by equality comparisons, preventing an arbitrary transported tensor
structure. Added open-section normalization to make b agree with j. No statement
correction or STATEMENT-DISPUTED flag is required.

Repair self-check: compared the new definition ownership and every helper use with
the return; all existing stack-algebra consumers retain their original record.
No original mathematical statement, proof step or proof dependency was changed.
The new-node statement describes precisely the constructions and supporting
obligations in StackModuleRestriction, and its stmt_deps are its exact bracket
citations. Compilation and the maintainer preflight are rerun for both files.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
