## Worker report

Module: `Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization`.
Main statement: `AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionDerivedOpenAdjunctionNormalization`.
There is one postponed theorem, with proof `sorry`, and five helpers with real data.
The node is unchanged except for `lean`. No new nodes or dependency repairs are needed.
No statement dispute was found.

Hypotheses and objects, checked against the node:

- The arbitrary commutative condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of `Profinite.CondensedRing`, not a topologically presented special case.
- `U X : Scheme.{u}`, `j : U ⟶ X`, `[IsOpenImmersion j]` are precisely the open immersion. The sites are the existing `Scheme.ProEt` and `Scheme.ProEt.topology`, with object universe u+1, morphism universe u, and coefficients u+1. No site universes are equated.
- `ring Λ T`, `internalModules Λ T`, `modules Λ T`, and `equivalence Λ T` are the dependency's transparent aliases for the pulled-back coefficient, its reconstructed ring, and the fixed section equivalence. Underlying sections and their additive groups remain identical.
- `[∀ X : Scheme.{u}, HasDerivedCategory.{u+1} (modules Λ X)]` retains the chosen localization universe of the existing derived realization. It is the chosen derived-category infrastructure, not a boundedness, injectivity, flatness or exactness assumption. The internal derived categories use the framework's existing instance.
- `openSectionObject j V` is the existing composition functor on the small pro-etale sites applied to V. Part (1) of weakly-etale localization identifies this with the forgetful functor from the slice; no assertion about constant coefficients is used.

Clauses, in the order they occur in the Lean statement:

1. The scalar actions on each summand are the first universally quantified conjunction. An object `V : U.ProEt` is exactly a summand index consisting of an ambient object with a factorization through U. Conversely every such factorization is weakly etale by weakly-etale cancellation, so this quantification covers every summand. `internalOpenGenerator` is the abelian ordinary adjunction unit followed by `upperStarIsoOpenImmersionRestriction`; this is the canonical sheafified summand injection. `openCoefficientSection` is the inverse of that restriction identification followed by `condensedPullbackHom Λ j`, hence exactly alpha_j(r restricted to U). The first equation computes the internal scalar action. The second computes the action after the fixed `ordinaryExtensionComparison`, the section-module comparison required by the node. Both use the actual section-module structures; m is explicitly typed in `(equivalence Λ U).functor.obj F` to expose its module instance.
2. The ordinary Hom identity uses `(openAdjunction Λ j).homEquiv`, the internal `CondensedRing.openImmersionLowerShriekUpperStarAdjunction`, `ordinaryExtensionComparison.inv`, and `pullComparison.hom`. Composition order is Lean's left-to-right `≫`, so it is h_sec(B(q) composed with c inverse) = t composed with A(h_int(q)).
3. The next universal clause is the ordinary unit equation eta'_AF = P'(c_F) composed with t_JF composed with A(eta_F).
4. The following universal clause is the ordinary counit equation epsilon'_BG composed with J'(t_G) = B(epsilon_G) composed with c_PG inverse. Both sides have source J' A P G and target B G.
5. The eight preservation conjuncts state finite-limit and finite-colimit preservation for the internal extension, internal restriction, section extension and section restriction. These additive functors are the existing ones; additivity is already supplied by their interfaces, so these are exactly their exactness claims.
6. `internalDerivedExtension` and `derivedExtension` are the existing termwise localized extensions. The helpers `localizedInternalOpenAdjunction` and `localizedSectionOpenAdjunction` independently apply `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` to their own ordinary adjunctions. The internal helper then applies `.ofNatIsoRight` using `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory.symm`. The section derived pullback is already the levelwise exact realization. These helpers implement exactly the node's specified localization construction, rather than conjugating an adjunction across E. The existing `internalOpenAdjunction` / `derivedOpenAdjunction` use the other total-derived construction (`mapDerivedCategoryAdjunction`); they are not silently substituted for the direct localization specified here.
7. The derived Hom identity universally quantifies over `K : DerivedCategory (internalModules Λ U)`, `M : DerivedCategory (internalModules Λ X)`, and every derived arrow q. It uses `derivedExtensionComparison.inv` for c inverse and the previously fixed `derivedPullComparison.hom` for b. Neither comparison is chosen as a hypothesis or replaced by a new isomorphism.
8. The final two clauses are the derived unit and counit identities for those independently localized adjunctions. Their types and order are identical to the ordinary clauses after localization. They explicitly include the units and counits, beyond the derived Hom identity.

Dependency declarations used (full namespace of comparison operations is `AlgebraicGeometry.ProEtale.ModuleRingedComparison`):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (the input's equivalent unbundled ring-object encoding).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedRingObj`, `coefficientRing`, `condensedPullbackHom`, `coefficientPullbackIso`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, `sectionRingSheaf` (through the recorded aliases).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`: `CondensedRing.openImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`, and its exactness instances. Lower shriek for arbitrary compactifiable maps is not used in place of open extension.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `internalModules`, `equivalence`, `extension`, `pullback`, `openAdjunction`, `ordinaryExtensionComparison`, `pullComparison`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `SheafOfModules.localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`, `localizedSystemAdjunction` (proof inputs on the slice).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `SheafOfModules.overFunctor` (slice restriction).
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`: `SheafOfModules.extensionByZeroPresheaf` (summand-action proof input).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`: `sectionDerivedPushpullNormalization`, specifically normalization of the existing `derivedPullComparison` against resolution transformations.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`: `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`, called in both helper definitions.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: `Scheme.ProEt.weaklyEtale_localization` Part (1) and `sliceEquiv` (proof inputs).
- The imported derived realization supplies `derivedEquivalence`, `internalDerivedExtension`, `derivedExtension`, `derivedExtensionComparison`, `internalDerivedPullback`, `derivedPullback`, `derivedPullComparison` without redefinition.
- Other stated proof dependencies are imported: the abelian presheaf adjunction, module-object projection formula and change of scalars, sheaf tensor, module sheafification, internal pullback exactness and section tensor comparison. Mathlib's `Functor.mapDerivedCategoryFactors`, `Adjunction.localization` (including unit and counit formulas), and `Localization.liftNatTrans`/`natTrans_ext` supply the three Mathlib proof leaves.

Sources read: `literature/stacks-project/sites-modules.tex`, extension-by-zero and extension-by-zero-exact (03DI/03DJ); the node's full ten-step proof; dependency statements and recorded Lean interfaces; `coord/pefw-upstream-framework.md`. The theorem docstring carries all ten proof steps. All helpers have the owning blueprint tag and source, and contain no proof placeholder or choice of unspecified data.

Edge cases checked: U empty (each existing summand is on an empty object, with the canonical zero sheaf); U = X / identity immersion (the same canonical units, comparisons and coefficient morphism apply, without requiring definitional identities); zero coefficient ring (all module maps and scalar equations remain valid); an ambient V with no map to U (no summand, hence the extension presheaf is zero there); arbitrarily unbounded complexes and arbitrary derived morphisms (no cochain-map representative for q is assumed). No nonempty, finite, bounded-below, injective or flat hypothesis was added.

Searches made before adding the statement:

- msearch LeanFinder: `equivalence of module sheaves identifies extension by zero restriction adjunction after deriving exact functors`: 8 hits, on sheafification adjunctions, generic module pullback and condensed discrete modules; none states this comparison.
- msearch Loogle: `CategoryTheory.Adjunction.mapDerivedCategory, CategoryTheory.Adjunction.ofNatIsoRight`: 0 hits, first identifier unknown.
- msearch grep: `mapDerivedCategory.*Adjunction|exactDerivedAdjunction` in Mathlib CategoryTheory: 0 hits. The exact localization helper exists in the recorded project module and is reused.
- msearch LeanSearch: `An equivalence of module sheaves identifies the derived extension by zero adjunction including its unit and counit`: 8 hits, generic equivalences and sheaf/module adjunctions; no exact theorem.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, pinned Mathlib and `dag/lean_names_upstream.json` for the six new declaration names: no collisions. Search for the item id in WeilConjectures: no existing declaration.
- Concept searches for open comparisons and normalization found `InternalModuleOperationsTransport` (ordinary comparison, mates and unit/counit equations) and `SectionDerivedRealization` (data for derived comparisons and total-derived adjunctions). These are reused; neither states the complete scalar and direct-localization derived normalization asserted by this node.

Validation: prescribed scompile.py compiled this module in sandbox and library-name modes, both clean (19.0 s and 12.7 s), under the default 60-second limit. The only initial error was absent scalar-action inference on a bare abelian-group carrier; explicitly using the identical section-module carrier fixed it. No warnings, extra axioms, or additional sorry declarations were introduced. The maintainer performs the independent delivery review.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
