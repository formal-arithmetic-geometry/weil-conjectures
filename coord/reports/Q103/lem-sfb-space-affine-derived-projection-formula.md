## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineDerivedProjectionFormula` states
`AlgebraicGeometry.AlgebraicSpace.space_affine_derived_projection_formula`, with
`sorry`. The companion definition module constructs the canonical scalar projection
arrow. Nothing is proved.
The definition module has the auxiliary postponed theorem `affineScalarChart_naturality`, the
functoriality of the structural map on affine étale charts; its source and full
proof are in its docstring. All definitions have real data. The two postponed statements belong respectively
to the item and the new
definition node and are listed in their owning `lean.declarations`.

The node statement, source, proof, proof dependencies and accepted stage-1 split
are unchanged. Its statement dependencies gain already landed interfaces used by
the statement; these carry the precise small ringed model, derived QCoh category,
space morphism properties and existing scalar/native tensor constructions.
The normalized structural scalar datum and canonical mate are recorded in the
new definition node `def-sfb-affine-scalar-projection-data`. Its module reuses
the scalar realization and native tensor helpers already listed in their
existing owning nodes. There is no dependency-interface repair or statement correction.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Commutative ring A, with the specified sizes | `A : CommRingCat.{u}`; explicit `u`, `w`, and the generic functor universes; `autoImplicit false` |
| Algebraic space over Spec A and morphism to Spec A | `X : AlgebraicSpace (Spec A)` and `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A)))`; this is the terminal representable space over the base |
| Flat on étale scheme charts | `hflat : MapIsFlat f`, the recorded all-compatible-étale-chart test |
| Quasi-compactness | `hqc : MapIsQuasiCompact f.hom.hom`; over the affine target this is quasi-compactness of X |
| Quasi-separatedness | `hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)` |
| Small étale structure sheaf and module category | `X.smallStructureSheaf` and `X.SmallModules`, via the recorded affine-chart skeleton and its specified equivalence with `X.Modules` |
| Unbounded derived categories | `HasDerivedCategory.{w} (ModuleCat.{u} A)` and `HasDerivedCategory.{w} X.SmallModules`; these select localization sizes, not boundedness or resolution hypotheses |
| E with quasi-coherent cohomology | `E : X.DerivedQCoh`; its defining predicate transports every cohomology sheaf back through `smallModuleEquivalence` |
| N is any A-module | `N : ModuleCat.{u} A`; no flatness, finiteness or boundedness binder |
| F_N = O_X tensor_A N | `affineScalarSheaf`, the existing `scalarConstantRealization` for the actual structural coefficient map; this sheafifies the constant module then extends scalars |
| Structural coefficient map | `affineScalarChart` uses `Scheme.ΓSpecIso` and the actual chart structure morphism; `affineScalarRingMap` is its sheafification lift |
| Maps F_N → F_N' | `affineScalarSheafMap`, the existing change-of-rings map on the constant module homomorphism |
| F_N quasi-coherent | First conjunct: `(X.smallModuleEquivalence.inverse.obj (affineScalarSheaf A X N)).IsQuasicoherent` for every N |
| N ↦ F_N exact | The existential record supplies H, its specified objects/maps, `H.Additive`, `PreservesFiniteLimits H`, and `PreservesFiniteColimits H` |
| Derived pullback of N[0] is F_N[0] | `affineProjectionDerived = H.mapDerivedCategory`; `affineProjectionSingleComparison` is the exact-derived functor's canonical degree-zero isomorphism followed by the specified object equality |
| Γ with the structural A-action | G is identified with actual compatible chart sections by `sections`; `sections_smul` fixes a acting through `affineScalarChart`; `sections_add` and `sections_map` fix addition and functoriality |
| Γ is the scalar-pullback right adjoint | `adjunction` and `transpose` fix the ordinary adjunction by the formula g(b tensor n) = b times the section associated to n |
| RΓ is the unbounded right derived functor | `affineProjectionRGamma = G.rightDerivedFunctor`, computed by the recorded K-injective resolutions; `derivedAdjunction` uses precisely this functor |
| Derived adjunction is the canonical one | `derivedTranspose` fixes it by localization of the ordinary chain transpose and the actual right-derived computation map |
| Derived tensor uses K-flat resolutions | `affineProjectionTensor` aliases `RingedDerivedNative.monoidal`; `tensorRepresentative` fixes the pullback tensor comparison using canonical localization tensorators on K-flat representatives |
| Ordinary tensor comparison | `tensor_formula` specifies (b tensor m) tensor (c tensor n) ↦ bc tensor (m tensor n), using the existing sheafification generators |
| Canonical projection arrow | `affineDerivedProjectionMap` is the adjunction unit followed by RΓ of the specified pullback-tensor comparison, then the counit tensored with `affineProjectionSingleComparison` |
| Displayed source and target in D(A) | The map has source `RΓ(E) ⊗ singleFunctor A 0 N` and target `RΓ(T_X(E, singleFunctor X 0 F_N))` |
| Projection is an isomorphism | Second conjunct: `IsIso (affineDerivedProjectionMap A X d E.obj N)` for every E and N |
| Natural in E and every N → N' | Final conjunct is the simultaneous square for arbitrary `e : E ⟶ E'` and `n : N ⟶ N'`, using actual maps of RΓ, degree-zero inclusions and scalar extension |
| Relation to the f-projection mate | The scalar adjunction is the composite through Spec A. The theorem proof docstring uses the affine étale derived equivalence and the projection-composition identity to identify its counit mate with the node's f-projection morphism |

`AffineScalarData` and `AffineProjectionData` are normalized presentation records,
not extra assumptions on the theorem. Their existence is a conclusion. In
particular, the formula does not quantify over an arbitrary map or arbitrary
natural isomorphism and call it canonical. Ordinary tensor generators, structural
sections, chain transposes and K-flat representatives fix all comparisons.
There is no choice of data from an uncharacterized existence theorem.

The derived tensor is the existing native localization tensor, not a new tensor
construction. The scalar functor, exact localization, right derived functor,
complex adjunction, ordinary tensor and localized tensor are all existing APIs.
The small site keeps the section universe u and is equivalent to the original
site whose objects live in u+1; no equality of those original universes is imposed.

Dependency declarations read and used (including public transitive interfaces):

- `def-weil-size-convention`: `None` — `None`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace` — `AlgebraicGeometry.AlgebraicSpace`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Scheme`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules` — `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic` — `DerivedCategory`.
- `def-trf-space-quasi-coherent-module`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` — `AlgebraicGeometry.AlgebraicSpace.QCoh`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat` — `AlgebraicGeometry.Flat`.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` — `SheafOfModules.cochainModulesMonoidal`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` — `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift` — `CochainComplex.mapBifunctor`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Spec`.
- `def-pur-ringed-site-zeroth-hypercohomology`: `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses` — `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`.
- `def-weil-pbc-ringed-topos-morphism`: `Sheaf.CategoryTheory.RingedToposMorphism` — `CategoryTheory.RingedToposMorphism`.
- `def-sfb-space-small-ringed-model`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel` — `AlgebraicGeometry.AlgebraicSpace.smallModuleEquivalence`.
- `def-sfb-space-derived-module-calculus`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules` — `AlgebraicGeometry.AlgebraicSpace.derivedDirectImage`.
- `def-sfb-space-morphism-properties`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` — `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.
- `def-coef-ringed-tensor-hom-model`: `Sheaf.Paper.CoefficientRingedTensorHomModel` — `WeilConjectures.CoefficientTensorModels`.
- `def-sfb-constant-module-coefficient-transport`: `Sheaf.CategoryTheory.SiteConstantModuleHom` — `CategoryTheory.constantModuleHomRingIso`.
- `lem-sfb-scalar-dual-evaluation-descent`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent` — `SheafOfModules.exists_scalarDualEvaluationDescent`.
- `lem-sf-ringed-derived-native-tensor`: `Sheaf.Algebra.Homology.RingedDerivedTensorNative` — `CategoryTheory.RingedDerivedNative.symmetry_square`.

The scalar realization additionally uses its owning module's public
`scalarConstantRealizationMap` and `scalarConstantGenerator`. Native tensor uses
its owning module's `monoidal`, `lax`, and existing categorical K-flat predicate.
The helper functors use `Functor.mapHomologicalComplex`,
`Functor.mapDerivedCategoryFactors`, `Functor.mapDerivedCategorySingleFunctor`,
`Functor.rightDerivedFunctor`, `Functor.rightDerivedFunctorUnit`,
`Adjunction.mapHomologicalComplex`, `Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`,
and `Functor.LaxMonoidal.μ`. The module imports each already recorded proof
prerequisite without `public`, as the stage-3 proof plan requires. The still
unrecorded qcqs right-adjoint prerequisite is used only in the natural-language
proof; it supplies no object or hypothesis to the statement.

Source checked: `literature/stacks-project/spaces-perfect.tex`, Tag 08IN,
`lemma-cohomology-base-change`, including the flat-pullback paragraph preceding
`lemma-check-quasi-coherence-on-covering` (lines 4662–4721 in the read checkout).
The seven-step proof in the node is retained in the main theorem docstring:
chartwise scalar sheaves and flat exactness; ordinary and derived scalar
adjunction; affine étale derived dictionary; coproduct preservation; exact mate
and its unit; generation of D(A); specialization and composition of counit mates.

Edge cases checked on the statement:

- A is the zero ring: no nonzero-ring or nonempty-spectrum hypothesis occurs.
- X is empty: no nonempty-chart or nonempty-section condition occurs; the scalar
  and section categories and zero projection map have their ordinary meanings.
- N = 0: included in all clauses, with the canonical zero-object isomorphism.
- N is nonflat or infinitely generated: no such restrictions are introduced;
  only the structural map X → Spec A is assumed flat.
- E is unbounded in both directions: all complexes are indexed by ℤ and there
  is no cohomological bound. K-injective/K-flat machinery is unbounded.
- Identity structure morphism and arbitrary homomorphisms N → N': included;
  degree-zero comparison and tensor representatives retain the ordinary unit
  normalization and no assumption on a coefficient map is imposed.

Searches (performed before introducing the interface):

- `msearch.py ... leanfinder "flat quasi compact quasi separated algebraic space derived global sections projection formula tensor A module"`: eight hits about affine scheme limits and pullbacks, no projection-formula match.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace, DerivedCategory"`: no hit, unknown AlgebraicSpace identifier in that index.
- `msearch.py ... grep "projectionFormula|projection_formula" AlgebraicGeometry`: no hit.
- `rg` of derived/projection/scalar names in `lean/WeilConjectures` and
  `lean/Sheaf`, and grep of this node ID upstream: no exact algebraic-space
  affine-base statement. Scheme and abstract ringed-topos projection formulas
  have different objects or hypotheses.
- DAG text search and `tools/blueprint_refs.py search` for scalar realization
  and native derived tensor found the recorded theorem-module helper
  constructions; those are reused rather than copied into new definition nodes.
- `tools/blueprint_refs.py ancestor` reports None for the inherited created.item
  chain, as the accepted split report already records. The inherited blueprint
  linkage is preserved.

No mathematical statement fault or disputed statement was found. Initial compile
repairs concerned chart indices, section-type coercions and colimit instances.
The large presentation record was split into ordinary and derived records to
avoid elaboration timeouts. No compile time limit or global build was changed.
Only scompile.py is used for compilation; the launcher scripts are unmodified.

## Second reading by Q103

The dispatcher expressly prohibits starting other agents and says there is no
lead to ask. Accordingly this section records a separate clause-by-clause second
pass by the same worker; it does not claim another worker reviewed the file.
The maintainer's independent review remains the external second reader.

I reread the unchanged node, its seven proof steps, the source and the Lean
statement together. The pass checked especially: every module N is quantified,
E is the recorded full derived QCoh subcategory, quasi-separatedness is the
relative diagonal, Γ carries the structural A-action, the degree-zero comparison
is an actual derived isomorphism, and the projection is the counit-defined map.
The ordinary/derived presentation record is asserted to exist, not assumed.
It includes representative normalizations and does not include invertibility of
the projection as a field. The result separately asserts that invertibility.

Mismatches found and repaired during this pass: use the existing small-model
module category to avoid an unintended site-universe equality; bind the four
generic functor universes explicitly; pin the derived tensor comparison on
K-flat representatives rather than using a bare natural isomorphism; retain
simultaneous naturality for E and arbitrary module homomorphisms. No source
hypothesis, coefficient restriction or bound was added. All public helpers have
source/blueprint docstrings, every postponed theorem has a proof docstring, and
every delivered declaration is listed in its owning node record.

## New nodes

`def-sfb-affine-scalar-projection-data` owns
`Sheaf.AlgebraicGeometry.SpaceAffineProjectionData`. It defines the actual
structural coefficient map from A on each affine étale chart, the existing
scalar sheaf specialization, the normalized scalar adjunction and derived
comparison records, and their explicit counit projection mate. Its source is
Tag 08IN with the tensor/adjunction normalizations of Tags 03EK, 06YT and 0B56.
It asserts no existence of those records and no projection invertibility.
The item asserts their existence under flatness and the projection formula.
The helper naturality theorem is a named proof obligation of the structural
map, with the complete functoriality proof in its docstring.

Searches: LeanFinder on “Algebraic space over affine scheme scalar extension
global sections adjunction normalized projection formula morphism” returned
eight scheme normalization and Spec–Gamma naturality results; none is this
interface. Loogle on “CategoryTheory.Adjunction, ModuleCat” returned twelve
ordinary adjunctions (including extend/restrict scalars and tilde/Gamma),
none on the algebraic-space small model with the derived normalizations.
Mathlib grep on “AffineProjectionData|affineScalarSheaf|affineDerivedProjectionMap”
returned zero hits. The same rg search over WeilConjectures, Sheaf and the DAG
returned zero hits. Blueprint search “affine scalar projection” returned zero.
The exact search records are included in the new node. The existing scalar
realization and native tensor are reused, not restated.

The split into a construction module and theorem module also gives each
compiler invocation less work; no timeout limit is raised. The second pass
checked both modules and this new definition node together: the construction
contains no projection-formula assumption, the item cites it, and the
canonical arrow, hypotheses and naturality square are unchanged.

Performance validation: profiling identified automatic `SizeOf` generation on the
large categorical records. Scoped `genSizeOf false` suppresses only those unused
automatically generated functions. No mathematical field or normalization is removed,
and no runtime or heartbeat limit is raised. Diagnostic profiler options are removed.

Final scompile.py check: both delivered files compile cleanly with no warnings.
The definition module took 45–49 seconds per check, and the theorem module
3–6 seconds, all under the unchanged 60-second per-file limit.

Preflight packaging repair: add the standard empty `import_flags` to the new
definition node, as the live schema requires; record an actual LeanSearch query
(eight Spec/Gamma results, no match) in addition to Loogle and grep; spell each
DAG citation separately so its dependency is visible to the checker. The item
uses the scalar/native helpers through the new definition node.
