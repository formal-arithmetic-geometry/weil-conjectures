## Worker report

The delivery states `AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionGeometricAdjunctionBridge` in `Sheaf.Paper.SectionGeometricAdjunctionBridge`. Its only new theorem has `sorry` as its entire proof. No assertion is proved. The four helper declarations in the same item module contain transparent constructions only.

Hypotheses and clauses, in node order:

- A commutative condensed ring is the section variable `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the underlying-object presentation of the recorded `Profinite.CondensedRing`; it permits arbitrary condensed rings and imposes no topological-ring presentation.
- Schemes and their arbitrary morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`. There is no properness, finite-type, boundedness or constructibility assumption.
- The actual small sites are `Scheme.ProEt.topology X` and `Scheme.ProEt.topology Y`, retained by `modules Λ T`. Site objects have universe `u+1`, morphisms `u`, sections `u+1`. The explicit family `[∀ T, proEtaleRingDerivedLocalization.{u, u+1} T (ring Λ T)]` transparently means `[∀ T, HasDerivedCategory.{u+1} (modules Λ T)]`, exactly the fixed normalization interface and size convention.
- `ring Λ T` is the recorded reconstructed section ring of `condensedRingObj Λ T = p_T^*Λ`. `equivalence Λ T` is the fixed section equivalence, not a new module category.
- The canonical coefficient identification is expressed by `∃! c` together with the equality of its adjunct on every section to `coefficientMap Λ f`. This uniquely specifies the given coefficient map; it is not an arbitrary input identification or an additional hypothesis.
- Ordinary pullback and direct-image comparisons are `b` and `d`. The direct-image comparison is required to act identically on all sections. The ordinary Hom-equivalence identity fixes `b` as its adjunction mate, so its tensor-formula comparison and scalar action are those of the same ordinary adjunction. Both pullbacks are the imported scalar-extension/inverse-image constructions. The four `PreservesFiniteLimits`/`PreservesFiniteColimits` conjuncts say both pullbacks are exact.
- `l` compares the two exact localized pullbacks; its square at every complex is the equality involving the two `mapDerivedCategoryFactors` and the degreewise image of `b`. The separate `IsIso leftDerivedFunctorCounit` clause retains the comparison from the canonical K-flat left derived functor on every complex. The fixed section `derivedPullback` already uses its exact descent, as in the normalization dependency.
- `r` compares the two K-injective right derived functors. Its square at every complex identifies both universal `rightDerivedFunctorUnit` transformations via the degreewise image of `d`. Their invertibility on K-injective `I` expresses the common canonical value `Q(f_*I)`. For a quasi-isomorphism `s : K ⟶ I`, naturality gives precisely beta_I followed by the inverse of `G(Qs)` used in the representative equations.
- The derived Hom identity compares the two specified adjunctions on every derived object and morphism. The following two conjuncts explicitly identify their units and counits with the correctly directed `l` and `r` maps.
- The next two conjuncts state the node's fraction formula separately for section and operation adjunctions. They quantify over all complexes, all quasi-isomorphisms `t : P ⟶ M`, `s : K ⟶ I`, K-injective `I`, and all cochain maps `h`. `Adjunction.mapHomologicalComplex` supplies the ordinary transpose `h^flat`. Lean's `homEquiv` is oriented from left-adjoint Hom to right-adjoint Hom, so the equality says that the displayed transpose is sent to the displayed fraction. The factor comparison at `M` identifies `L(QM)` with `Q(f^*M)`. No K-flat assumption is imposed on `P`, and no preservation of arbitrary quasi-isomorphisms by direct image is assumed.
- The final conjunct composes the fixed `derivedPullComparison`, `derivedPushComparison` and `D(E)` with `l,r`, and identifies the internal Hom transpose with the independently specified operation transpose. The preceding unit/counit identities and the imported section normalization identify the transported units/counits as well.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `coefficientRing_X`, `condensedRingObj` and commutativity preservation.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: `InternalAbelianSheafModule.sectionModuleEquivalence` and `sectionRingSheaf`.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `equivalence`, `coefficientMap`, `pullback`, `pushforward`, `adjunction` and their recorded comparison aliases.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `Q`, `Qh`; convention nodes have no declaration of their own.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`: `sectionDerivedPushpullNormalization`, `normalizationInternalAdjunction`; its imported `SectionDerivedRealization` supplies `derivedAdjunction`, `derivedPullComparison`, `derivedPushComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly reexports `ProEtaleOperations` and `ProEtaleOperationsCanonicalAdjunction`: `proEtaleRingModules`, `proEtaleRingDirectImageMap`, ordinary pullback/direct image, tensor-unit-normalized ordinary adjunction and original derived operations. The item module defines four localization-parametric helpers without changing this dependency record, as explained below.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`; `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: `IsKInjective.Qh_map_bijective` and `quasiIso_iff`.
- Proof imports retain the stated DAG plan: `InternalModuleOperationsTransport.internal_module_operations_transport`, `SheafOfModules.module_pullback_pushforward_adjunction`, `CondensedRing.module_pullback_additive_exact`, `Functor.exactFunctor_derivedFunctor`, the ringed-site K-injective existence theorem, `exists_rightDerived_of_enough_isKInjective`, `preDerivedAdjunctionGeneral`, `ringedTopoiDerivedPullbackIndependent`, `Adjunction.mapHomotopyCategory`, `Adjunction.preservesKInjectiveComplexes`, and Mathlib `Adjunction.derived` with its counit compatibility.

Edge cases checked before drafting: identity morphisms reduce the comparisons to canonical identity adjunction comparisons; the zero coefficient ring and empty scheme give zero module categories and do not require nonzero sections; complexes in a single degree recover the ordinary tensor/restriction transpose. The quasi-isomorphisms `t,s` may both be identities. A general `t` need not have K-flat source, since exact pullback preserves all quasi-isomorphisms. All complexes are unbounded. Opposite tensor-factor order is handled by the ordinary adjunction-normalized comparison, not by assuming equality of those constructions.

Searches actually run:

- `msearch.py leanfinder`: “The canonical section derived geometric adjunction agrees with exact proetale coefficient pullback and K injective direct image including resolution comparisons units and counits”. Eight results, chiefly ΓSpec adjunction normalization and ordinary sheaf-module adjunctions; none compares these two fixed realizations.
- `msearch.py loogle`: `"Adjunction.derived", "IsIso"`. Zero results.
- `msearch.py grep`: `section.*[Aa]djunction|[Dd]erived.*[Aa]djunction`, restricted to `CategoryTheory`. Nine hits, including Mathlib's general derived-adjunction file; no bridge.
- `msearch.py leansearch`: “The derived adjunction for module sheaves agrees with an independently specified exact pullback and K injective direct image under canonical resolution comparisons”. Eight ordinary adjunction results; no bridge.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item ID, `sectionGeometric`, `geometricAdjunction` and section/derived-adjunction phrases. The fixed section normalization and operation definitions were found and read; no declaration states their comparison. Further searches for `proEtaleRingDerivedPullback` and `proEtaleRingDerivedAdjunction` found the localization-fixed operations and their existing consumers. Their signatures were inspected with a server-only `scompile.py` diagnostic probe; diagnostics were removed from the final file.

The source read was Stacks `derived.tex`, `lemma-pre-derived-adjoint-functors-general` and `lemma-derived-adjoint-functors`, together with `sites-cohomology.tex` `lemma-adjoint`. The current blueprint ancestor is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-open-coefficients/lem-sfb-dc-lower-star-preserves.proof.md`, its final coefficient-extension paragraph. The bridge is the reviewed agent comparison extracted from that paragraph, not the unit statement itself.

No mathematical node statement is corrected, and no new DAG node is introduced. No STATEMENT-DISPUTED finding.

## Repair of returned delivery (H13)

The immutable returned head was `23cbbe7d918d`. Its mathematical theorem was accepted in the return; H13 rejected rebinding the heavily shared `def-weil-pbc-proetale-operations` ownership record from its 13 existing declarations to four helpers. This repair follows the first requested alternative: all four helpers now live in `Sheaf.Paper.SectionGeometricAdjunctionBridge`, carry this item's blueprint ID and source docstrings, and are listed alongside the theorem in this item's `lean.declarations`. The separate `ProEtaleRingDerivedOperationsOfUniverses` module is removed. The dependency node is copied byte-for-byte from current `sheaf-dag`; its module, primary declaration, all 13 names and every other field remain unchanged. No dependency module or new node is delivered. Comparing the item with current `sheaf-dag` shows that only its `lean` record changes.

The helpers are `AlgebraicGeometry.Scheme.proEtaleRingDerivedLocalization`, `proEtaleRingDerivedPullbackOfUniverses`, `proEtaleRingDerivedDirectImageOfUniverses`, and `proEtaleRingDerivedAdjunctionOfUniverses`. The old operations fix `HasDerivedCategory.standard` with derived Hom universe `u+2`; the section realization uses a supplied localization with Hom universe `u+1`. The helpers retain the actual module categories and expose exactly the existing `mapDerivedCategory`, `rightDerivedFunctor`, and `proEtaleRingModuleAdjunction.mapDerivedCategoryRightDerivedAdjunction` with explicit localization universe `w`. The localization helper is transparent `HasDerivedCategory`. The imported completed-coefficient ring-sheafification instance has an unresolved `max` universe during helper elaboration; it is disabled for those declarations and restored locally before the theorem. This only controls inference for the same canonical sheafification. No site-universe equality, alternate operation, arbitrary adjunction, additional hypothesis, or theorem-statement correction is introduced.

## Second reading by Q86

Written by the maintainer's independent reader (cc review service) at head 936ccdba. The worker's section said that no second reading took place. This section replaces it.

Node clauses and the Lean that renders them:

1. Λ is a commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the presentation of def-pd-section-module-operations-data. OK.
2. f is any scheme morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`. The small pro-étale sites and module universe come from `[∀ T, proEtaleRingDerivedLocalization.{u,u+1} T (ring Λ T)]`, which is `HasDerivedCategory.{u+1}`, the same family the section realization uses. No properness, finiteness or boundedness is assumed. OK.
3. The canonical c : f⁻¹R_Y ≅ R_X: `∃! c` whose adjunct `proEtaleRingDirectImageMap` equals `coefficientMap Λ f` on every section. This pins c. OK.
4. Both ordinary pullbacks are R_X ⊗ f⁻¹(−) with the same adjunction, and both are exact. `d` is the identity on sections. `b` is pinned as the adjunction mate by the homEquiv equation. Four `PreservesFinite{Limits,Colimits}` conjuncts give exactness. OK.
5. L_sec(QM) → Q(f^*M) is invertible and identifies with L_op(QM):
   - `IsIso` of the K-flat `leftDerivedFunctorCounit` at every complex.
   - The `l` square through both `mapDerivedCategoryFactors` and Q(b) pins `l`, since Q is a localization.
   OK.
6. The common value Q(f_*I) on K-injective I: the `r` square through both `rightDerivedFunctorUnit`s and Q(d), plus invertibility of both units at K-injective I. OK.
7. The two adjunctions agree, including units and counits:
   - Hom identity: `e_sec h ≫ r = e_op (l⁻¹ ≫ h)`.
   - Units: η_op = η_sec ≫ r ≫ G_op(l).
   - Counits: ε_op = L_op(r⁻¹) ≫ l⁻¹ ≫ ε_sec.
   I checked every direction by hand. OK.
8. Representative formula, stated for each realization. `homEquiv` maps factors(M) ≫ Q(f^*t)⁻¹ ≫ Q(h♭) ≫ Q(s)⁻¹ to Q(t)⁻¹ ≫ Q(h) ≫ β_I ≫ G(Qs)⁻¹, where h♭ comes from `Adjunction.mapHomologicalComplex`. t and s are arbitrary quasi-isomorphisms, I is K-injective, and no K-flat source is required. This matches Stacks 0FND and the node. OK.
9. Internal-to-operation identification: D(E_Y), D(E_X), `derivedPullComparison`, `derivedPushComparison`, l and r identify `normalizationInternalAdjunction` with the operation adjunction. OK.

Helpers. The four `abbrev`s in this module are the existing `mapDerivedCategory`, `rightDerivedFunctor` and `mapDerivedCategoryRightDerivedAdjunction` of `proEtaleRingModuleAdjunction`, taken at localization universe w. They carry real data and docstrings with the source and the blueprint ID. No name clashes with side-live. The def-weil-pbc-proetale-operations record is byte-identical to sheaf-dag. The `[-instance]` / `[local instance]` switch for `integralCoefficientRingSheafify` has landed precedents (LocalizedOrdinaryPullbackNormalization, FiniteProjectiveModelPullback).

Edge cases: f = id, Λ = 0, X = ∅ (zero categories), t = s = 1, single-degree complexes. None needs an extra hypothesis.

Records:
- All 11 statement-dependency nodes are byte-identical to side-live.
- The item node differs only in `lean`.
- `lean.statement` matches the file's signature.
- The proof is `sorry` only.
