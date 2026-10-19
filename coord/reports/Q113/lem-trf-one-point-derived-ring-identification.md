## Worker report

The module `Sheaf.TraceFormula.OnePointDerivedRingIdentification` states
`CategoryTheory.one_point_derived_ring_identification`. Its conclusion is the
Prop-valued record `CategoryTheory.OnePointDerivedRingIdentification`; its only
postponed proof is the named theorem. All categories, tensor products,
localizations and scalar-extension comparison predicates are existing ones.
No definition has postponed data.

Repair of returned head `21ac0ebe8940` (H2): the saved packet passed the
initial required dry run (commit `88e0026695`). Its Lean module is retained byte
for byte. The repair adds the existing-definition ownership node
`def-trf-singleton-site-operations` and replaces the packet-added theorem
`lem-weil-pbc-singleton-site-module-comparison` in `stmt_deps` by this definition
node. The theorem is not used through a chosen witness. No mathematical
statement, proof, proof dependency or dependency module is changed. The wrapper
rebases the packet onto current main in its own temporary worktree.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| The category has one object and only its identity | Existing `singletonSite = Discrete PUnit`; there is no arbitrary site parameter. |
| Only the maximal sieve covers | Existing `singletonTopology = ⊥`. |
| A commutative ring A | `(A : Type u) [CommRing A]`, with explicitly declared universe `u`. |
| The constant ring sheaf with value A | Existing `singletonRingSheaf A`; its functor is constant with value `CommRingCat.of A`. |
| Sheaves of modules over that ring | `singletonModuleCategory A`, the specialization of `ringedSiteModules` and Mathlib `SheafOfModules`. |
| Evaluation is an exact equivalence | `equivalence` supplies `e`, requires `e.functor = singletonEvaluation A`, and preservation of every `ShortComplex.ShortExact`. |
| Inverse assigns the one-object sheaf | The same field requires `e.inverse = singletonConstantModuleSheaf (R := A)`. |
| Ordinary and sheaf tensor agree, on morphisms too | `tensor : singletonTensorComparison A`: its comparison sends the sheaf pure tensor to the same ordinary pure tensor, and its second equation gives naturality in both linear maps. |
| Direct-sum total tensors agree | `totalTensor` compares the evaluated `CochainComplex.mapBifunctor F G (MonoidalCategory.curriedTensor _)` with the total tensor of the evaluated complexes, for every integer-indexed pair. This is the direct-sum total complex, including its signed differential. |
| Cohomology agrees | `cohomology` compares evaluation of `F.homology n` with homology of termwise evaluation, for every `F` and every integer `n`. |
| Quasi-isomorphisms agree | `quasiIso` is an iff for each chain map, using termwise evaluation on that same map. |
| K-flat complexes agree | `kFlat` is the iff between `CochainComplex.IsKFlatIndependentCoefficients` and `(HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).kFlat` of the evaluated complex. |
| Equivalence on homotopy categories | `homotopy` supplies an equivalence whose functor is exactly `(singletonEvaluation A).mapHomotopyCategory (.up ℤ)`. |
| Equivalence on derived categories, compatible with localization | `localization` supplies localization structures and `singletonDerivedLocalizationCompatible A hA hM`; this predicate supplies `D` and `DerivedCategory.Qh ⋙ D.functor ≅ evaluation.mapHomotopyCategory _ ⋙ DerivedCategory.Qh`. |
| Every homomorphism f:A→A' | `scalarExtension : ∀ (B : Type u) [CommRing B] (f : A →+* B), ...`. |
| Termwise sheaf change of rings is ordinary extension | The supplied additive `E` has its objects and maps prescribed by `singletonSheafExtensionObj/Map`; `s : E ⋙ singletonEvaluation B ≅ singletonEvaluation A ⋙ ModuleCat.extendScalars f` gives the natural identification, and `singletonScalarUnitCompatible` fixes its pure-tensor formula. Mapping complexes or homotopy categories applies this same comparison termwise. |
| Universal total left derived pairs correspond | `singletonDerivedScalarComparison f E s r a` supplies `LS`, `LM`, their natural counits `eS`, `eM`, both `IsLeftDerivedFunctor` assertions, and a comparison `c` through the localization equivalences `DR`, `DS`. Its displayed counit equation intertwines `c`, `eS`, `eM` with the termwise scalar comparison and localization comparisons. |
| Derived change of rings becomes ordinary derived scalar extension | The same predicate fixes the ordinary functor being derived on both sides, so the universal pairs are those of sheaf change of rings and `ModuleCat.extendScalars f`. This is not an arbitrary functor comparison. |
| Same K-flat resolution computations and derived-to-ordinary counit | The predicate requires invertibility of the same counits on K-flat representatives and their compatibility equation. For any K-flat resolution `q:P→K`, the computation is the counit at `P` composed with the inverse image of `q`; thus the equation identifies these computations as well. |
| No flatness or boundedness restriction | There is no such binder; all complexes are `CochainComplex ... ℤ`, and `f` is an arbitrary ring homomorphism. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` (transparent arbitrary-ringed-site module category).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, using the existing localized sheaf tensor.
  This module is now imported explicitly; no monoidal structure is copied.
- Mathlib `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift` and its pure-tensor formula.
  These underlie ordinary tensor and the existing comparison predicates.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the universal acyclic-total-tensor test.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, specialized to module-complex quasi-isomorphisms.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Qh`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`:
  `LinearMap.baseChange`, whose map is `a ⊗ x ↦ a ⊗ f x`;
  `ModuleCat.extendScalars` bundles the same scalar extension for arbitrary ring maps.
  The recorded convention uses `B ⊗[A] M`; symmetry identifies the node's `M ⊗[A] B`.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `CategoryTheory.Functor.leftDerived_from_resolvingClass`, read with all its hypotheses
  and universal-counit conclusion; imported as a proof dependency.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; imported as the current
  derived-change-of-rings interface used in the stated proof.
- The existing-definition node `def-trf-singleton-site-operations` records
  `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`, which provides the exact site,
  topology, constant sheaf, evaluation, inverse, ordinary change of rings, restriction,
  tensor comparison, unit normalizations, localization comparison and universal
  derived-pair comparison. I read those predicates and the full signature/docstring of
  `CategoryTheory.singleton_site_module_comparison`. The present statement retains
  its canonical interfaces and explicitly states the total-tensor/cohomology clauses.
  The older theorem does not explicitly state these two clauses and therefore is
  not recorded as an exact existing match for the full item.

Edge cases checked against definitions and quantifiers: zero rings are allowed by
`CommRing`; the zero module and zero complexes are included. Empty direct sums are
zero and evaluation preserves them as an additive equivalence. No boundedness is
used in the direct-sum total-complex construction. Identity ring maps and
non-flat maps (e.g. the quotient of integers modulo a prime) are included. The
K-flat test quantifies over every acyclic complex, not merely bounded ones.
Localization uses the existing size `u+1` suitable for these categories, without
assuming small Hom sets in universe `u`. Rings and modules can be chosen in any
ambient `u`, so there is no cardinal bound on the mathematical objects.

Searches (the saved `searches.jsonl` was retained and read):

- `msearch.py ... grep 'one.point|singletonSite|derived.*scalar' CategoryTheory/Sites`:
  8 generic site/sheaf hits in Mathlib, no complete statement.
- `msearch.py ... leanfinder 'terminal one point site sheaf modules evaluation derived scalar extension ordinary modules'`:
  8 hits, led by `SheafOfModules.evaluation`; no full derived identification.
- The saved Loogle phrase query found no match because `evaluation` was unqualified.
  I repaired the search with `msearch.py ... loogle 'SheafOfModules.evaluation'`:
  12 hits, evaluation and its limits/finite/quasicoherence APIs, no full statement.
- `rg` for `one_point_derived_ring_identification`,
  `OnePointDerivedRingIdentification`, and the item blueprint id in the upstream
  `WeilConjectures` and project `lean/Sheaf` returned no existing declaration.
- `rg` for `one.point|singletonSite|derived.*scalar` in upstream `CategoryTheory`
  and project `TraceFormula` found incidental one-point text and unrelated scalar
  comparisons; the canonical project singleton construction was found in
  `Sheaf.ProperBaseChange.SingletonSiteModuleComparison` and reused.
- DAG search for `singleton_site_module_comparison|SingletonSiteModuleComparison`
  identified the landed dependency `lem-weil-pbc-singleton-site-module-comparison`.

Source check: opened `literature/stacks-project/sites-modules.tex` at
`definition-sheaf-modules` (03CW), `derived.tex` at `section-homotopy` (05RN), and
`definition-unbounded-derived-category` (05RU). The punctual specialization and
transport of the universal pairs are the explicit construction in the node's
proof; no statement correction is needed.

Validation: the saved module passed the prescribed `scompile.py`. After the
self-check repairs, both sandbox and library-name compilation passed again
(4.1 and 4.0 seconds), with no diagnostics. All variables and universe parameters
are explicitly bound, and the sole theorem proof remains `sorry`.

## Second reading by Q113

This is the worker's self-check, not a claim of an independent review. I compared
each clause against the table above and read the imported comparison predicates.
I found and repaired the saved record typo, the missing explicit homotopy clause,
the obsolete tensor helper, and the theorem docstring. The definition is a
proposition bundling the asserted comparisons, with no chosen or postponed data.
For the returned H2 point, I reopened the item, the new definition node and
all existing singleton declarations. Every singleton name in the item is a
plain definition/abbreviation or its supporting instance, and is listed by the
new definition owner. No call to `singleton_site_module_comparison` or `.choose`
occurs in the item. Its exact equivalence, pure tensor and morphism formulas,
unbounded total tensors, cohomology, quasi-isomorphism iff, K-flat iff, homotopy
and localization comparisons, pinned scalar extension, universal counits and
K-flat unit normalization remain as rendered in the table. The existing-source
signatures have all universes bound (`u` and localization universe `u+1`).
The new definition node introduces no theorem, no assumption that its predicates
hold, and no new Lean construction. Its ordinary scalar unit uses `1 ⊗ m`,
equivalent by symmetry to the source convention `m ⊗ 1`. Zero rings, zero
modules, identity and non-flat ring maps remain admitted. The two private
imports noted as advisory are retained as the stated proof-dependency imports
required by stages/2-statements.md §3.7. No dependency module is delivered.

## New nodes

`def-trf-singleton-site-operations` records existing definitions and supporting
instances in `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`, excluding
its comparison theorem. Its source is the punctual site of Stacks 00X9, the
module/tensor/change-of-rings definitions 03CW/03CZ/03EK, localization 05RU and
the universal-pair and K-flat counit conventions 05S9/06XN/06YY/07A6. No new
module or declaration is required: `lean.existing = true`. The primary signature
`abbrev singletonSite : Type` is verbatim. The declarations list also contains
the constant ring sheaf and ring map, module category, evaluation and constant
module functors, extension object/map and pure tensors, restriction and
ordinary unit, tensor and unit predicates, induced homotopy comparisons and
derived-localization/derived-scalar predicates. The final predicate includes
both universal derived pairs, the counit square, restriction-localization
normalization, the two K-flat unit equations and the all-object unit square.

The new node's clauses map to the existing declarations as follows:

| Definition clause | Existing declaration(s), in `CategoryTheory` |
| --- | --- |
| Identity singleton site and maximal-cover topology | `singletonSite`, `singletonTopology` |
| Constant ring, underlying value and ring map | `singletonRingSheaf`, `singletonRingValue`, `singletonRingMap` |
| Module category, evaluation, inverse constant functor | `singletonModuleCategory`, `singletonEvaluation`, `singletonConstantModuleSheaf` |
| Evaluation additive and zero-preserving structures | `singletonEvaluationAdditive`, `singletonEvaluationPreservesZeroMorphisms` |
| Sheaf extension on objects/maps and pure sections | `singletonSheafExtensionObj`, `singletonSheafExtensionMap`, `singletonExtensionTmul` |
| Scalar restriction and additive structures | `singletonSheafRestriction`, `singletonRestrictionAdditive`, `singletonExtendScalarsAdditive` |
| Ordinary unit and its pure tensor formula | `singletonOrdinaryUnitMap`, `singletonOrdinaryUnitFormula` |
| Tensor and scalar/unit predicates | `singletonTensorComparison`, `singletonScalarUnitCompatible` |
| Termwise comparisons on homotopy categories | `singletonExtensionHomotopyComparison`, `singletonRestrictionHomotopyComparison` |
| Derived localization and normalized universal pairs | `singletonDerivedLocalizationCompatible`, `singletonDerivedScalarComparison` |

Fresh LeanSearch returned 8 hits, including `SheafOfModules.evaluation`,
`CategoryTheory.constantSheaf` and `constantSheafAdj`; LeanFinder returned 8
hits, including evaluation and module sheaf units. Neither gives the
singleton-specific operations. Mathlib grep for
`singletonSite|singletonEvaluation|singletonDerivedScalarComparison` in
`CategoryTheory` returned 0 hits. Upstream `WeilConjectures` has no such hit;
project `lean/Sheaf` locates the exact definitions in the singleton module.
DAG grep finds only their theorem-node record, with no definition owner;
`blueprint_refs.py search singleton` gives 4 unrelated blueprint matches.
The queries and raw hit summaries/digests are recorded in the new node's
`mathlib_searches`. This is definition ownership of existing code, as requested
by the maintainer, rather than a second definition.

The maintainer's note about the already landed
`lem-trf-pseudocoherent-rhom-flat-base-change` is recorded for coordination:
that consumer can cite this same definition node. It is not edited by this
item's delivery.

