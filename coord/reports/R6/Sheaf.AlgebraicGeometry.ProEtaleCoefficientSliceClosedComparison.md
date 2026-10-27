## What changed

The normalized ordinary comparison is proved by lifting the composition/base-change adjunction to modules and using uniqueness of left adjoints. Its section formula follows from the unit equation, naturality and the triangle identity. The item is then assembled from monoidal descent and invertibility of the restriction closed mate. Scalar transport is an equivalence, so its closed mate is proved invertible by full faithfulness, the two tensor–Hom adjunctions, essential surjectivity and Yoneda. Naturality makes the component maps into natural isomorphisms. The closed-mate tower calculation and the normalized tensor square prove the pullback comparison formula; the closed adjunction proves evaluation and transpose. Koszul symmetry is retained in monoidal descent.

Existing data definitions move to ProEtaleCoefficientSliceComparisonData, publicly reexported by the item. TensorData retains the six ordinary/monoidal fields; Data.tensorData forgets the three Hom fields. TensorNormalized is the original normalization prefix with a proposition tail, so Normalized unfolds to the original conjunction. The data module privately imports ProEtaleScalarExtensionSliceComparison and reuses the proved public proEtaleSliceModules_exact for sectionwise restriction. The duplicate private exact_moduleRestriction proof is removed. The data node records the existing scalar-slice node as the dependency of this exactness proof. This uses only its exactness assertion, not its scalar-extension comparison or the perverse-sheaf unit route. No upstream source module is edited.

## Proved and sorry left

Repair of returned head ad094857678: no additional holes are closed or added by the duplicate-proof repair; the retained packet closes one existing hole and adds the two holes listed below.

The original hole in AlgebraicGeometry.Scheme.proEtaleCoefficientSliceClosedComparison is replaced by a complete assembly proof. This is a decomposition, not a net proof: one upper hole closed, two separate lower holes added.

The remaining new holes are AlgebraicGeometry.Scheme.proEtaleSlice_monoidal_descent (lem-zl-proetale-slice-monoidal-descent) and AlgebraicGeometry.Scheme.proEtaleSlice_closed_maps_isIso (lem-zl-proetale-slice-closed-mates). Each is strictly part of the original argument: the first asserts no Hom comparison; the second asserts only invertibility for restriction and no scalar/pullback Hom, evaluation, transpose or symmetry assertion. No definition contains a hole or chooses arbitrary data from an unproved existence theorem. The existing proEtaleSliceModuleRestriction_exact stays proved.

The new AlgebraicGeometry.Scheme.proEtaleSlice_ordinary_comparison is proved without holes. Its helpers identify the ring adjunction unit using the normalized Kan coprojections, verify both coefficient equations, and verify the distinguished-section normalization. The private closed-adjunction, naturality, tower and Yoneda arguments are also proved. Checks: the data interface and both geometric lemma statements compile (40.7, 6.1 and 7.2 seconds); the ordinary comparison and the main assembly compile (27.5 and 18.9 seconds). Formatting warnings in the ordinary comparison were removed before delivery. The repaired data module compiles cleanly in 43.5 seconds using proEtaleSliceModules_exact; its proof-only import is acyclic. The complete repaired packet compiles cleanly in import order: data 41.8 seconds, closed mates 4.4, monoidal descent 5.0, ordinary comparison 29.2, and main assembly 32.7. The delivery preflight performs the axiom audit.

## No longer needed

The duplicate private exact_moduleRestriction declaration is removed; its proof is replaced by application of the existing public proEtaleSliceModules_exact. No public helper is duplicated and no library module is withdrawn.

The original private imports RingedSliceEvaluationTranspose, ScalarExtensionRingIso, OrdinaryModuleDerivedInternalHom, HomComplex, InternalHom and CochainTensorUniverses are removed from the item. The literal-slice evaluation theorem is still a planned dependency of the restriction closed-mate lemma, so it is not claimed globally pruned. Scalar Hom preservation needs no K-injective or Hom-complex calculation: its equivalence proof is formal. The corresponding original proof steps using def-pur-kinjective-complex, def-pur-sheaf-hom, def-pur-hom-complex and def-pur-derived-internal-hom directly are unnecessary in the assembly; they remain statement/transitive dependencies of the fixed ordinary internal Hom. The source-library declarations are preserved. No module withdrawal is requested. RingIsomorphismTensorTransport and ScalarHomComparisonTower are not new imports: only their proved private generic arguments are reused in the item, so no additional dependencies are introduced for those arguments. The approved tool_uses list is retained because the geometric source results remain transitive dependencies of the monoidal and slice lemmas; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified that the generic exactness helper duplicated private helpers in ProEtaleScalarExtensionSliceComparison and ContinuousCoefficientSliceNormalization. Their statements have identical binders. They are private, so this repair imports and applies the public specialization proEtaleSliceModules_exact instead; its functor is definitionally equal to the one used here. It supplies exactness for arbitrary coefficients and all pro-etale U without new hypotheses.

The original plan describes restriction on the literal over-category, whereas the Lean statement uses the equivalent small site of the source scheme. The existing literal-slice theorem cannot be applied by definitional equality. Transport of the normalized tensor and Hom constructions is the separate geometric work retained below. Zero current Lean importers does not make the item unnecessary: its DAG parent still uses it. The mathematical statement and the unit route are retained.

## New nodes

- def-zl-proetale-slice-comparison-data records the moved comparison interface and its monoidal projection. See coord/changes/R6-proetale-slice-comparison-data.md.
- lem-zl-proetale-slice-ordinary-comparison records the proved normalized ordinary module comparison (Stacks 03CE and 03CZ).
- lem-zl-proetale-slice-monoidal-descent records the total-complex, K-flat, unit and symmetry portion given the normalized ordinary comparison (Stacks 03CE, 03EL, 07A4, 0FPT).
- lem-zl-proetale-slice-closed-mates records invertibility of the normalized restriction closed mate (Stacks 08JB and 08J9).

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
