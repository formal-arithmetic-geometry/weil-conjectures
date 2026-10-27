## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem` defines the category
`AlgebraicGeometry.AlgebraicSpace.CoherentAdicSystem`, its quotient construction,
completion functor, termwise pullback diagrams, proper-support predicate and bounded
component kernel/cokernel predicate. The natural-language statement is unchanged.
The only node changes are its Lean record and three added, already-landed definition
dependencies: `def-sfb-space-ideal-power-products`,
`def-trf-space-module-scheme-restriction`, and
`def-sfb-space-absolute-quasi-separated`. No new node or dependency repair is needed.

Clause-by-clause reading:

- The base is `{S : Scheme.{u}}`; spaces are `AlgebraicSpace S` and modules are the
  existing `X.Modules`. All universe and term variables are explicitly bound.
  The ring and module section universe remains `u`, with the existing larger etale
  site object universe. No new equality between universe levels is assumed.
- Locally Noetherian means the category parameter
  `∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
  Quasi-compactness is `CompactSpace (Point X.obj.obj)`, equivalently the finite
  subcover condition for opens. Quasi-separatedness is the recorded
  `IsAbsolutelyQuasiSeparated X`, the affine scheme-test criterion for the absolute
  diagonal. These three parameters are required by `CoherentAdicSystem`.
- The ideal `J : QuasiCoherentIdeal X` is the existing quasi-coherent subobject of
  the structure module, with `J.val.arrow` its monic inclusion. There is no chosen
  ideal presentation, arbitrary replacement map or second quasi-coherence predicate.
- `adicPowerSections J M n T` uses `idealPowerSubsheafSections J.val.arrow M
  (fun _ ↦ Set.univ) n T`. This gives precisely the section family of the locally
  generated module subsheaf J^n M. It uses products and finite sums on charts and
  covering-sieve local membership, so it is a sheaf submodule, rather than just the
  sectionwise span. At n=0 its sections are all sections of M.
- Positive indexing is `op n` = level n+1. `IsCoherentAdicSystem` first requires
  site quasi-coherence and `RingedSpace.IsCoherent` of every chart restriction
  `((X.schemeRestriction T).obj (F.obj (op n)))`. Thus coherence includes the exact
  existing finite-type and finite-type-kernel condition, not merely finite type.
- Its second conjunct is `AdicPowerKills J (n+1) (F.obj (op n))`. This says every
  section of J^(n+1) times the level n+1 module vanishes, on every etale chart.
- Its third conjunct gives an isomorphism from the ordinary quotient of the level
  n+2 module by J^(n+1) to the level n+1 module. The equation with
  `(adicQuotientModel J).projection` identifies its composite with the actual
  transition `F.map (homOfLE (Nat.le_succ n)).op`.
- The category is the full subcategory of `ℕᵒᵖ ⥤ X.Modules`. Its arrows are all
  natural transformations: adjacent naturality says t_n followed by a_n equals
  a_(n+1) followed by s_n, in diagrammatic Lean composition. The other naturality
  equations follow from these by composing adjacent transitions. Identity and
  composition are componentwise by the inherited functor-category construction.
- `AdicQuotientModel` records a functor on all module sheaves, its quotient
  projections, annihilation of the local ideal-product sections, and factorization
  through each projection for EVERY target and EVERY annihilating map, uniquely.
  Its `transition` and `naturality` fields normalize all diagram maps. These are
  exactly ordinary sheaf cokernel quotients, including their maps, rather than an
  arbitrary inverse system with abstractly isomorphic terms.
- `adicQuotientModel_exists` states existence together with uniqueness of the
  natural isomorphism commuting with every projection. `adicQuotientModel` chooses
  from that normalized universal property. This is the contract's permitted choice
  of a universal object, not a data choice from mere existential nonemptiness.
- `coherentAdicCompletionDiagram` has terms M/J^(n+1)M, quotient transitions and
  the induced maps of quotients. `coherentAdicCompletion` restricts its source to
  the full category of modules satisfying site quasi-coherence and every chart's
  coherence, and has codomain `CoherentAdicSystem`. Its only additional proof
  obligation is the named `coherentAdicCompletionDiagram_isAdic` theorem.
- `coherentAdicPullbackDiagram g` is postcomposition with the dependency's actual
  `moduleTensorPullback g`. Its terms, transitions and induced maps are therefore
  g* applied componentwise. It does not assert an extra preservation theorem.
- In the relative proper-support clause, work over `Spec (.of A)`, with the
  structural arrow `f` to its represented terminal space. The explicit hypotheses
  `MapIsSeparated f` and `MapIsFiniteType f` match the stated context. This presents
  an A-space directly and requires no unrelated map from Spec A to another base.
  `CoherentAdicHasProperSupport` requires a closed immersion `i : Z ⟶ X`,
  `MapIsProper (i ≫ f)`, and `Q : Z.Modules` with `Q.IsQuasicoherent` and
  `Q.IsFiniteType`, together with a module isomorphism
  `(moduleDirectImage i).obj Q ≅ F.obj (op 0)`. This is exactly the proper closed
  carrier condition on M_1 from the Quot dependency.
- `CoherentAdicKernelCokernelKilled K a` starts with `∃ t : ℕ, 1 ≤ t ∧ ∀ n`.
  For every ordinary `KernelFork (a.app (op n))` which is limiting and every
  ordinary `CokernelCofork` which is colimiting, its vertex is killed by K^t.
  These universal properties are in ALL module sheaves. They express the ordinary
  sheaf kernels and cokernels up to their canonical unique isomorphisms; they do
  not assume the kernel in the adic category is computed termwise. Existence of
  these ambient sheaf kernels and cokernels holds on the small ringed model in
  the unchanged section universe.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`, and `IsRepresentableWith`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  specialization of Mathlib `SheafOfModules`; the category and its linear maps
  are inherited, not redefined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the slice
  sheafification instances supporting Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  `moduleDirectImage`, and `moduleTensorAdjunction` (the last fixes the pullback's
  tensor normalization).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` and
  `WeilConjectures.AlgebraicGeometry.Coherent`: the recorded upstream
  `RingedSpace.IsCoherent`. The upstream module is imported explicitly so the
  public declaration is available even with the older published intermediary.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsFiniteType`, and `MapIsProper`.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotient.properSupport`
  gives the exact closed-carrier convention reproduced for the system's first level;
  its imported `schemeSpace` provides the represented affine base.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`.
- The added definition owners supply `idealPowerSubsheafSections` and
  `idealSectionImage` in `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`,
  `schemeRestriction` in `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`,
  and `IsAbsolutelyQuasiSeparated` in its namesake module. All were read in source.

Source reading: Stacks `spaces-more-morphisms.tex`, section-existence-proper,
its two object conditions and compatible morphisms, the Functoriality paragraph,
equation-completion-functor, the proper-support paragraph, and
remark-inverse-systems-kernel-cokernel-annihilated-by condition (1). The scheme-only
upstream `WeilConjectures.AlgebraicGeometry.CoherentFormalModule` was also read;
it cannot be reused for spaces because its carrier and ideal are respectively
`Scheme` and `Scheme.IdealSheafData`, on the Zariski site. Its positive indexing
agrees with this module. The example CompactObject module is now withdrawn; its
node's recorded signature and the current module-mode conventions were followed.

Edge cases checked before and after writing:

- J=0: all positive quotients recover M and adic transitions are isomorphisms.
- J=O_X: annihilation forces every level to be zero; the quotient diagrams are zero.
- J nilpotent, e.g. (epsilon) in k[epsilon]/epsilon^2: powers and quotients stabilize
  at the correct level; no reducedness hypothesis is present.
- Empty X and empty scheme charts: local membership uses covering sieves and the
  sheaf axiom; the zero sheaf, completion and proper empty carrier are included.
- The first diagram index is 0 but means n=1; the object's annihilation exponent
  is never zero. The helper power convention includes exponent zero separately.
- K=0 makes the bounded condition automatic; K=O_X requires ordinary component
  kernels and cokernels to vanish. A single t precedes EVERY component index.
- Identity and zero maps, zero modules, identity pullback and general nonflat
  pullback diagrams all remain defined with no extra coherence/exactness premise.
- Proper support is imposed on the first term only, and includes the zero module.

Searches (all through the prescribed search wrapper or direct read-only rg):

1. LeanFinder: "Category of coherent adic inverse systems of module sheaves on a
   Noetherian algebraic space" returned eight hits (CondensedMod, LightCondMod,
   scheme module category/limits and condensed limits); none is this category.
2. Loogle: "SheafOfModules, AdicCompletion" returned zero hits.
3. Mathlib grep: "coherent.*adic|adic.*coherent|idealPower" returned five local
   cohomology ideal-power-diagram hits; these are diagrams of ring ideals, not
   coherent systems on algebraic spaces.
4. LeanSearch: "Category of coherent inverse systems of sheaves with transitions
   modulo ideal powers" returned eight hits, including `localCohomology`,
   `idealPowersDiagram`, generic quasicoherent data and condensed constructions;
   no exact match.
5. rg in both project roots for coherent/adic and formal-system terminology found
   the scheme-only `CoherentFormalModule` and its consumers, plus the already-used
   algebraic-space ideal-power, restriction, coherence and module operations.
   rg for this node id in `lean/WeilConjectures` returned no hit.
6. rg in Mathlib and both project roots for every proposed declaration name found
   no conflict. No already-landed declaration defines this algebraic-space category.

Validation: the complete module compiles through scompile.py under its real module
name and the wrapper's isolated sandbox name. No errors or warnings remain. There
are two named postponed theorems, each with this node's blueprint marker, a precise
source and a complete natural-language proof. Every definition has real data or
selects a uniquely normalized universal object; no data field is filled by sorry.
No statement fault or dispute was found.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
