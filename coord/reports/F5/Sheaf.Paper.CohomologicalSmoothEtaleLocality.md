## What changed

Filled both proofs in `Sheaf.Paper.CohomologicalSmoothEtaleLocality` without changing
any public signature, public import, definition, target, or source-library file.
The existing ordinary-etale canonical-map locality theorems already implement the
hard compact-support composition and conservativity argument. The proof transports
their three clauses through the exact comparison functor, rather than importing
all the separate planned pro-etale mate calculations.

The private proved helpers reflect comparison isomorphisms, lift unit-target
isomorphisms, recover etale invertibility from an etale-origin inverse, and
construct the inverse as `RHom(omega_f, unit)`. The last construction is explicit;
no arbitrary object is selected from a mere existence theorem. Exceptional
preservation and the internal-Hom finiteness theorem prove that this inverse is
Dctf. The base-change proof pastes only squares in the finite-type domain of the
original hypothesis. The etale dualizing isomorphism comes from the normalized
compactification adjunction and right-adjoint uniqueness.

Updated the item's DAG proof, proof dependencies, proof origin and obsolete tool
approvals. The unit statement and realized route are retained. The DAG now names the
existing source-library tools for smooth dualizing objects, arbitrary-scheme
etale exceptional locality, and normalized etale graph comparison, plus the
internal-Hom Dctf theorem. No maintainer approval is added to `tool_uses`. All additional
imports are private proof imports. No other module is adapted.

Repair of C-a9c00 / C1 point 6:

- (a) Replaced the use of `Etale.isCohomologicallySmooth_of_etale` in the
  etale base-change clause by `Etale.etaleBaseChange`, then converted its
  canonical unit component with `isIso_dualizingComplexBaseChangeMap_iff`.
  `etaleBaseChange` is proved from the canonical compactification etale
  adjunction, comparison isomorphism and unit base-change compatibility.
  It invokes no smooth-purity or affine-line base-change theorem.
- (b) Added `lem-route-exists-right-derived-lower-shriek-comp-iso` to steps
  3 and 4 and to `proof_deps`. Also recorded
  `lem-route-projection-map-associativity`, used by tensor-map composition.
- (c) Replaced direct etale dualizing preservation by the native node-owned
  pro-etale preservation interface of `lem-sf-native-finite-tor-preservation`.
  Its value on the comparison image of the unit is identified with the
  comparison image of the etale dualizing object. Exact faithful comparison
  and its full faithfulness reflect bounded constructibility and Tor amplitude.
  Replaced direct `Etale.constructibleFiniteTor_derivedHom` by the actual
  `WeilConjectures.finiteCoefficient_derivedHom_ctf_etale` declaration of
  `thm-sf-hom-ctf`. Private proved conversion lemmas relate the two etale
  constructibility and Tor predicates, including unordered input intervals
  (widened using min and max).

The compiled-data audit reads complete `.olean.private` data of project imports,
resolves declarations in their actual import closure, and traverses both types and
proof values from the two public theorem terms. It found exactly these eight
sorry leaves (all already owned):

- `AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso` — `lem-route-exists-right-derived-lower-shriek-comp-iso`.
- `AlgebraicGeometry.Etale.exists_smooth_compact_dual_model` — `lem-asd-smooth-compact-dual-model`.
- `AlgebraicGeometry.Etale.sfEtaleCompactProjectionInverse_composition` — `lem-sf-etale-compact-projection-coherence`.
- `AlgebraicGeometry.Etale.sfEtaleGraphExchangeTensor` — `lem-sf-etale-graph-exchange-tensor`.
- `AlgebraicGeometry.Etale.sfEtaleGraphTransferTensor` — `lem-sf-etale-graph-transfer-tensor`.
- `AlgebraicGeometry.Etale.sfAffineBaseP1TraceAdjunction` — `lem-sf-affine-base-p1-trace-adjunction`.
- `AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange` — `lem-asd-projective-line-exceptional-base-change`.
- `AlgebraicGeometry.Etale.nonempty_normalizedProjectiveLineAdjunction` — `lem-normalized-projective-line-adjunction`.

The proof retains Stability.Reduction for constructibleFiniteTor_tensorUnit;
the finite-type dimension-bound module is available through its public imports.

All eight owners are recorded in `proof_deps` and step 3. The composition owner
is additionally explicit in step 4. The raw source finiteness sorry leaves named in the return are absent from
this published closure; the preservation and Hom calls use the declared interfaces
listed above. The dimension-zero smooth tensor and
invertibility calls still pass through the node-owned smooth compact dual model;
this repair does not claim those lower purity obligations are proved. There is
no use of `affineLineBaseChange` in this closure.

Validation: final module compiled cleanly in 32.5 seconds, below the 60-second
limit. A temporary full-data audit printed the eight leaves above; its traversal
took 79.4 seconds and is not part of the delivered module. Static checks confirm
unchanged public signatures and imports, zero sorry tokens, and unchanged node
statement, statement dependencies and Lean attachment.

## Proved and sorry left

Closed 2 existing holes:

- `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_surjective_etale`
  (`lem-pur-co-smooth-etale-locality`).
- `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_etale_and_dualizing`
  (`lem-pur-co-smooth-etale-locality`).

Added 0 holes; split off 0 statements. There are 0 `sorry` occurrences in the
item and no new modules. Existing dependencies may retain their own holes;
this delivery does not claim to close them.

## No longer needed

Removed the following direct proof imports from this module. Some remain needed
transitively by existing source-library declarations; none is withdrawn or
asserted globally unreachable. The adopted source tree remains intact.

- `Sheaf.Paper.PurityFiniteSetting`
- `WeilConjectures.Compactification.NagataCompactification`
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Paper.PurityAffineChartBounds`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.Paper.SfDerivedComplete`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`
- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.FiniteConstructibleHom`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`
- `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.EtaleIsoDescent`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.FiniteTorStability`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`

The following planned direct proof dependencies are no longer invoked separately.
The existing ordinary-etale canonical-map results package their arguments;
the proof uses those results and explicit comparison transport. The native
finite-Tor preservation interface replaces the separated-scheme stability interface.

- `lem-weil-pbc-finite-type-over-noetherian`
- `def-weil-exceptional-inverse-image`
- `lem-sf-class-compact-support-comparison`
- `def-weil-derived-pullback-tensor-hom`
- `lem-weil-proetale-weakly-etale-localization`
- `cor-pur-general-admissibility-datum`
- `lem-sf-pullback-tor-amplitude`
- `lem-sf-tensor-ctf`
- `lem-weil-finite-compact-projection-formula`
- `thm-cbc-finite-level-proetale`
- `thm-sf-ambient-adjoint-class`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lemma-constructible-pullback-stratification`
- `lemma-constructible-pullback-constant`
- `lem-weil-pbc-etale-covering-base-change`
- `lem-sf-flat-model`
- `lem-sfb-quasifinite-compact-support-exact`
- `lem-pur-etale-support-map-compatibility`
- `lem-amb-etale-adjoint-locality`
- `def-weil-pbc-etale-shriek-base-change-map`
- `def-exchange-projection`
- `lem-amb-etale-compact-comparisons`
- `thm-sf-comp-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-pur-etale-iso-descent`
- `fix-prop-projection-formula`
- `thm-sf-ctf-stability`
- `lem-pur-rhom-global-sections`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `cor-weil-finite-constructible-hom`
- `lem-cbc-proetale-stalk-conservative`

Removed obsolete `tool_uses` entries, preserving the order of all retained entries:

- `lem-weil-finite-compact-projection-formula`
- `thm-cbc-finite-level-proetale`
- `lem-sf-pullback-tor-amplitude`
- `lem-sf-tensor-ctf`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-sf-class-compact-support-comparison`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-amb-etale-adjoint-locality`
- `lem-amb-etale-compact-comparisons`
- `thm-sf-comp-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-pur-rhom-global-sections`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `cor-weil-finite-constructible-hom`
- `lem-weil-pbc-etale-covering-base-change`
- `thm-sf-ambient-adjoint-class`
- `fix-prop-projection-formula`
- `thm-sf-ctf-stability`
- `lem-sfb-quasifinite-compact-support-exact`
- `cor-pur-general-admissibility-datum`
- `lemma-constructible-pullback-stratification`
- `lemma-constructible-pullback-constant`
- `lem-sf-flat-model`
- `lem-cbc-proetale-stalk-conservative`
- `lem-pur-etale-support-map-compatibility`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-weil-pbc-etale-site-localization-open`

No Lean file or DAG node is deleted. Global pruning is left to the maintainer's
reachability computation; removal of a direct import is not a withdrawal request.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch was found. The first delivery failed
to account for unowned source proof leaves. The returned C1 point 6 is repaired
as described above; the earlier compile alone did not validate DAG ownership. The plan expanded compact-support
normalization and mate calculations that the source library already proves. Its
unrestricted ordinary-etale smoothness predicate cannot simply be substituted for
the compared predicate: the latter requires a Dctf inverse and quantifies over
finite-type base-change schemes. Both differences are addressed explicitly.

The upstream `nonempty_dualizingComplex_iso_constantComplex_of_etale` retains an
irrelevant Tate-twist typeclass argument in its signature. The proof uses its
underlying normalized adjunction construction directly, with no upstream edit
or extra hypothesis. The method also works on the empty scheme, with the tensor
unit (possibly zero) and unitors; no nontriviality or nonemptiness is assumed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
