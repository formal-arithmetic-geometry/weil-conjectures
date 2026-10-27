## Worker report

The module `Sheaf.AlgebraicGeometry.UnboundedOpenCounitSiteTransport` states
`AlgebraicGeometry.ProEtale.unboundedOpenCounitSiteTransport` with one `sorry`.
Six auxiliary declarations expose two restriction left-adjoint instances, the actual
etale/pro-etale derived adjunctions, and the two specified localized comparisons.
They have real construction bodies. No arbitrary adjunction, comparison, map or
existence choice is introduced. No statement correction or dependency repair is needed.

Hypothesis and clause correspondence:

- The finite commutative coefficient ring is `R : Type (u + 1)`, `[CommRing R]`,
  `[Finite R]`. This is the common coefficient universe of the recorded fixed comparison.
- Arbitrary schemes and open immersion are `{U X : Scheme.{u}}`, `j : U ⟶ X`,
  `[IsOpenImmersion j]`. There are no Noetherian, separated, qc or qs assumptions.
- Ordinary constant-R modules use `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} R)`
  and `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} R)`. These are the recorded
  fixed-scalar presentation, canonically equivalent to modules over the constant ring
  sheaves via `finiteCoefficientRealization` / `finiteCoefficientEtaleRealization`.
  The pro-etale dependency's intrinsic category is not used as a different coefficient
  theory: its realization is exactly the ordinary category used by the canonical open
  comparison. The imported intrinsic extension declaration transports the same Kan
  extension under its specified realization equivalences.
- C_T is `(comparisonUpperStar (ModuleCat R) T).mapDerivedCategory`.
  J^e and J^p are `openImmersionLowerShriek ... j` and its Etale counterpart, each
  with `.mapDerivedCategory`; U^e and U^p are the corresponding
  `openImmersionRestriction ... j` with `.mapDerivedCategory`.
- The actual sheaf adjunctions are the recorded `openImmersionLowerShriekAdjunction`
  on both sites. Their definitions are Kan extension / sheafification adjunctions,
  whose transpose evaluates each factorization summand (and is zero on the empty sum).
  The imported `Adjunction.mapHomologicalComplex` constructs unit, counit and both
  triangle identities degreewise. `Adjunction.mapHomotopyCategory` gives their
  homotopy-category adjunctions. Our `unboundedOpenEtaleAdjunction` and
  `unboundedOpenProEtaleAdjunction` apply the existing
  `Adjunction.mapDerivedCategoryAdjunction` to these very adjunctions; hence they
  contain both actual units, counits and triangle fields, rather than assert only
  abstract existence of some adjunction. The imported `AdjunctionUnit` formulas
  identify their units and counits on Qh objects with the localized degreewise ones.
  This encodes the initial construction clause through the actual library constructions.
- e is `unboundedOpenExtensionComparison`, the canonical
  `Functor.mapDerivedCategorySquareIso` of the recorded
  `openImmersionLowerShriekComparisonUpperStarIso`.
  r is `unboundedOpenRestrictionComparison`, the same construction on the recorded
  `openComparisonRestrictionIso`, whose body uses the canonical pullback comparison.
- Conjunct one is exactly C_U(eta^e_F), then r at J^e F, then U^p(e_F), equal to
  eta^p at C_U F. Lean's `≫` orders these maps left to right.
- Conjunct two is exactly e at U^e H, then J^p(r_H), then v^p at C_X H, equal to
  C_X(v^e_H). Its adjunctions are the actual ones defined above.
- Conjunct three writes the node's full-subcategory transport as the explicit natural
  Hom compatibility for every F,H and f: the actual pro-etale transpose of
  e_F inverse followed by C_X(f) equals C_U of the actual etale transpose followed
  by r_H. Restricting this equation to any full subcategories on which C_U,C_X are
  equivalences gives precisely the five-step transported Hom chain in proof step 7.
  Full faithfulness gives the middle Hom identifications and essential surjectivity
  covers every target pair. Identity transposes give the actual counit. Thus the
  statement records the transport uniformly, without choosing extra subcategories.
- Conjunct four quantifies `K : DerivedCategory.Plus (...)`, and specializes the
  recorded `fixedCompactSupportComparisonIso` to
  `Compactification.ofIsOpenImmersion j` (j followed by id_X). The pro-etale identity
  direct-image inverse is precomposed and C_X of the etale identity direct-image
  map is postcomposed; the result equals e inverse at K.obj. These are exactly the
  canonical identity identifications in the node, with the opposite orientation
  explicitly permitted there. Reversing yields e on D+; e itself is unbounded.
- The first three conjuncts quantify over the entire unbounded derived categories:
  no constructibility, Tor-amplitude, boundedness or resolution condition is added.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`; its recorded additional declarations are used as described above.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`; its recorded additional declarations are used as described above.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`; its recorded additional declarations are used as described above.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`; its recorded additional declarations are used as described above.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`; its recorded additional declarations are used as described above.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`; its recorded additional declarations are used as described above.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`; its recorded additional declarations are used as described above.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`, `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`; its recorded additional declarations are used as described above.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.upperStar`; its recorded additional declarations are used as described above.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`; its recorded additional declarations are used as described above.
- `lem-cbc-proetale-extension-zero-comparison`: `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`, `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-comparison-pullback`: `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, `AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent`; its recorded additional declarations are used as described above.
- `def-sp-fixed-compact-support-comparison`: `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`, `AlgebraicGeometry.ProEtale.fixedCompactSupportComparisonIso`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-extension-by-zero-adjunction`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-extension-by-zero-exact`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`; its recorded additional declarations are used as described above.
- `lem-weil-proetale-weakly-etale-localization`: `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`; its recorded additional declarations are used as described above.
- `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`; its recorded additional declarations are used as described above.
- `def-weil-presheaf-modules-sheafification`: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `PresheafOfModules.sheafification`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-termwise-adjunction-homotopy`: `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, `CategoryTheory.Adjunction.mapHomotopyCategory`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-exact-functor-derived-factorization`: Mathlib `{'declaration': 'CategoryTheory.Functor.mapDerivedCategoryFactors', 'file': 'Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean', 'how': 'specializes in one line per clause, for F with [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]: F_D = F.mapDerivedCategory (line 36); φ = F.mapDerivedCategoryFactors : DerivedCategory.Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (line 41); σ = the instance F.mapDerivedCategory.CommShift ℤ (line 80) and (1) = instance F.mapDerivedCategory.IsTriangulated (line 104); (2) = instance NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ (line 94), where the shift structure of F.mapHomologicalComplex is commShiftMapCochainComplex with commShiftIso = mapCochainComplexShiftIso, the identity in each degree (Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean:247-282, mapHomologicalComplex_commShiftIso_hom_app_f); preservation of quasi-isomorphisms = HomologicalComplex.quasiIso_map_of_preservesHomology (Mathlib/Algebra/Homology/QuasiIso.lean:280) with Functor.preservesHomologyOfExact'}`.
- `lem-sfb-adjunction-localization`: Mathlib `{'declaration': 'CategoryTheory.Adjunction.localization', 'file': 'Mathlib/CategoryTheory/Localization/Adjunction.lean', 'line': 89, 'how': "exact, one declaration per clause: Adjunction.localization (line 89) gives the adjunction and its triangle identities; Adjunction.localization_unit_app (line 118) and Adjunction.localization_counit_app (line 125) give the two formulas. In the file G=L, F=R, G'=bar L, F'=bar R, L₁=Q₁, L₂=Q₂; CatCommSq.iso G L₁ L₂ G' is p.symm and CatCommSq.iso F L₂ L₁ F' is q.symm. Lines 33-131 read in full."}`.
- `lem-sf-open-comparison-unit-normalization`: `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`, `AlgebraicGeometry.ProEtale.openComparison_unit_normalization`; its recorded additional declarations are used as described above.
- `lem-weil-pbc-localization-universal-property`: Mathlib `{'declaration': 'CategoryTheory.Localization.lift', 'file': 'Mathlib/CategoryTheory/Localization/Predicate.lean', 'how': "specializes in one line, one declaration per clause, for `L : C ⥤ D` with `[L.IsLocalization W]` (Mathlib's notion of localization; `DerivedCategory.Q` is one for `HomologicalComplex.quasiIso C (ComplexShape.up ℤ)`, DerivedCategory/Basic.lean:98): (1) `Localization.lift F hF L` (line 304) with `Localization.fac F hF L : L ⋙ lift F hF L ≅ F` (line 313); (2) `Localization.liftNatTrans L W F₁ F₂ F₁' F₂' τ` (line 326, for `[Lifting L W Fᵢ Fᵢ']`, the class holding the isomorphisms φᵢ, line 295) with `liftNatTrans_app` (line 332), `liftNatTrans_id` and `comp_liftNatTrans` (lines 339-351), `liftNatIso` (line 357); uniqueness in (2) and clause (3) is `Localization.natTrans_ext` (line 286); the equivalence of functor categories is `Localization.fullyFaithfulWhiskeringLeft` (line 278) with `Localization.essSurj`"}`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`: `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`, `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`; its recorded additional declarations are used as described above.

Source reading: the full Locality paragraph in the current main-20261015 blueprint;
Stacks sites-modules.tex, lemma-extension-by-zero (03DI), its inverse Hom maps and
lemma-extension-by-zero-exact (03DJ); proetale.tex, lemma-jshriek-comparison (09AF).
Read the full signatures and docstrings for the ordinary adjunctions, restriction
comparison, extension comparison, exact/termwise/localization interfaces, fixed comparison
and its specified direct-image mate. The fixed comparison really has D+ as its input.

Edge cases checked before writing: empty U and empty X (empty extension index gives zero),
j=id (the identity proper factor and both identity comparison maps survive), zero ring,
zero sheaves/complexes, and complexes unbounded in both directions. All remain permitted;
there is no nonempty, nontrivial, finite-Tor or constructibility hypothesis. Exact degreewise
functors preserve quasi-isomorphisms without truncating a complex. No disputed statement.

Searches for existing declarations:

- msearch LeanFinder: canonical etale/proetale open extension comparison preserves actual
  adjunction units and counits on unbounded derived categories. Eight hits, mainly generic
  derived-adjunction counits and sheaf adjunctions; no full theorem.
- msearch Loogle: `CategoryTheory.Adjunction.localization, CategoryTheory.Adjunction.counit`.
  One exact generic tool, `Adjunction.localization_counit_app`; reused, not a duplicate.
- msearch grep: `mapDerivedCategory.*[Aa]djunction|[Aa]djunction.*mapDerivedCategory`:
  zero Mathlib hits. Project rg found `Adjunction.mapDerivedCategoryAdjunction`,
  `AdjunctionUnit` and `mapDerivedCategorySquareIso`; these are reused in full.
- msearch LeanSearch: canonical etale/proetale extension by zero preserves actual counit
  on unbounded derived categories. Eight generic derived-adjunction/counit results;
  none states this combined theorem or the fixed compact-support clause.
- rg in WeilConjectures and Sheaf for the item id, new names, open counit/comparison
  phrases: no match for the complete item. `VectorIntegrationSite.openCounitComparison`
  is a related counit identity using inverse-image/left-derived presentations, with no
  unit equation, full Hom transport or fixed compact-support restriction clause.
  `CompactSupportSiteComparisonOpen` uses D+ and different compactified exchange maps.
  Neither records the complete statement; existing generic constructions are reused.

Validation: scompile.py compiled both sandbox and actual module names cleanly, including
all public and proof imports, under the default per-file 60-second limit. The only
postponed proof is the named main theorem, whose docstring contains all eight proof steps.

## Second reading by N5

Self-check only; no independent worker was started, as required by the dispatcher brief.
The maintainer's independent delivery review is still required. Re-read the node and module
with all four conjuncts open: checked map domains and composition order in the unit and
counit equations, the e inverse orientation in the Hom formula, and both identity
pushforward identifications in the final D+ equality. The finite-ring and open-immersion
hypotheses are explicit; arbitrary schemes and unbounded F,H remain allowed. Checked the
full-subcategory assertion by the explicit Hom transport formula and essential
surjectivity, and checked that the selected adjunction constructions retain localized
actual evaluation rather than an existential adjunction. No mismatch found in this check.
