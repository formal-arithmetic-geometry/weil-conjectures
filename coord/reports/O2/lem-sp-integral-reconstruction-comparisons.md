## Worker report

Item: `lem-sp-integral-reconstruction-comparisons`, group O2, stage 2.
Module: `Sheaf.Paper.IntegralReconstructionComparisons`.
Namespace: `AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons`.
Main statement: `integral_reconstruction_comparisons`.

The module states the node, with one postponed theorem. Its other declarations are real
constructions or structures packaging the conclusions of this same node. No new DAG nodes,
dependency-record repairs, or mathematical statement changes are needed. The repair adds
`def-sp-complete-compactification-limit-comparison` to `stmt_deps` and updates `lean`.
The seven-step natural-language proof in the theorem docstring follows the accepted split.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| A finite field k0, its fixed algebraic closure k, characteristic p | `D₀ : WeilConjectures.FiniteFieldDatum.{u}`, with base `D₀.k₀`, closure `D₀.k`, and prime `D₀.p` |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime]`, `_hl : l ≠ D₀.p` |
| Finite extension E / Q_ell, with its valuation ring | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; inherited coefficients use `Padic.coefficientExtensionIntegers l E` |
| Separated finite-type k-schemes X,Y | `X Y : Over (Spec (.of D₀.k))`, with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on their structure maps |
| A smooth separated k-morphism f, pure dimension d >= 0 | `f : X ⟶ Y`, `(d₀ : ℕ) [SmoothOfRelativeDimension d₀ f.left]`; the selected `c : Compactification f.left` includes an open immersion followed by a proper map, hence also entails separatedness of f |
| Small pro-etale sites | All inherited objects use `Scheme.ProEt.topology T`, whose objects are in `Type (u+1)` and morphisms in universe u |
| R_T = lim (O_E / ell^n)_T, B_(n,T) its actual quotients | `SpReductionTower`, `spCompletedReduction`, `spCompletedStrictTower`, and `spCompletedTotalLimit` reuse the completed sheaf and actual ell-power projections; the recorded cofinality identifies the uniformizer-power completion. No discrete constant O_E is substituted |
| Strict varying-coefficient towers | `spCoefficientTowers` and `spDerivedCoefficientTowers`, with original strict semilinear transitions and the localization supplied by `q.abelian T` |
| C_T = derived-complete bounded constructible integral category | Exactly `sfIntegralConstructibleCategory l E T`, not the internal condensed-module presentation of a different category |
| N_T = full normalized constructible category with common cohomology and Tor bounds | Exactly `spNormalizedConstructibleTorTowerCategory l E T (q.abelian T)` |
| r_T = strict derived reduction | Ambient `reduction` is the dependency alias for `spCompletedReduction`; the new `red` only restricts this existing functor to the prescribed full subcategories |
| L_T = total derived limit after restriction of scalars | Ambient `totalLimit` uses the dependency `LimitPresentation`; the new `lim` only restricts this existing functor |
| Choose f = bar-f composed with j | `c : Compactification f.left`, with `c.i`, `c.g`, `c.Z` |
| F = R bar-f_* j_! on completed coefficients | Exactly `CompleteCompactificationLimit.image l E c`; `integralLeft` is its full-subcategory restriction |
| Specified F_bullet, G_bullet and their adjunction | `SpTowerGluing.support l E b o q c hF`, `G`, and `adj`. `_charts` and `_levels` retain the recorded gluing theorem's normalized chart/finite adjunction identifications. These are the data of the specified choice, not an assumption that the desired normalized restrictions or integral comparisons already exist |

The parameters `b,o,q,r` are the existing normalized presentations supplied by the dependency
nodes. They do not replace a canonical construction by an arbitrary functor. In particular,
`SpTowerShriek.Base` fixes the ordinary equivalence on sections and maps;
`SpTowerCalculus.Coordinates` fixes its finite evaluations and scalar adjunctions;
`SpReductionTower` fixes the ordinary tensor generators, quotient transitions and universal
left-derived functor. The theorem works for such supplied presentations. The chosen tower
adjunction is retained, including its actual unit and counit.

### Every conclusion

| Node clause | Lean rendering |
| --- | --- |
| X,Y are Noetherian | First two conjuncts `IsNoetherian X.left ∧ IsNoetherian Y.left` |
| Reduction and total limit preserve the indicated full subcategories | `Reconstruction.reduction_mem` and `limit_mem`, as conclusions via existential `aX,aY` |
| Actual reconstruction unit and counit are invertible there | `Reconstruction.unit_iso` and `counit_iso`, on `presentation.adjunction` |
| r is fully faithful, with inverse L | `Comparisons.equivalenceX/Y`, with `equivalenceX/Y_functor` equal to `red` and `equivalenceX/Y_inverse` equal to `lim`; being the functor of this equivalence gives full faithfulness |
| Both F_bullet and G_bullet preserve normalization | The existential witnesses `hFn,hGn`; constructibility/common bounds are already encoded in the specified gluing functors' types |
| Restricted tower adjunction N_X <-> N_Y | `towerLeft` and `towerRight` are literal ObjectProperty lifts; `Comparisons.adjunction` is an adjunction between those restrictions |
| Restricted unit/counit are the same actual tower maps | `Comparisons.unit_same` and `counit_same` compare the underlying derived-tower arrows directly with those of the supplied `adj` |
| H(K) = L_X G_bullet r_Y K is a functor C_Y -> C_X | `exceptional` is precisely `red_Y ⋙ towerRight ⋙ lim_X`; identities and composition are those of a composite functor, with no extra existential choice of H |
| F maps C_X into C_Y | `Comparisons.image_mem`; `integralLeft` uses that proof to restrict the actual proper/open functor |
| Canonical natural isomorphism b : r_Y F -> F_bullet r_X | `Comparisons.direct`, a natural isomorphism of the normalized full categories |
| b is an entire-tower compactification comparison | `Comparisons.direct_hom` identifies its underlying arrow with `reduction(realization)` followed by the actual reconstruction counit. `realization` is the recorded `comparison` followed by the explicitly constructed `supportCoordinates` under the total limit. It is an actual natural transformation before restriction; it is not assembled from finite level isomorphisms |
| Canonical natural isomorphism c : r_X H -> G_bullet r_Y | `Comparisons.exceptionalComparison`, with `exceptional_hom` identifying its underlying arrow with precisely `aX.presentation.adjunction.counit.app (G(r_Y K))` |
| Naturality in a : M -> M' | `direct_naturality`: in Lean's left-to-right composition, `b_M ≫ F_bullet(r_X a) = r_Y(F a) ≫ b_M'`, the displayed equation in the node |
| Naturality in h : K -> K' | `exceptional_naturality`: `c_K ≫ G_bullet(r_Y h) = r_X(H h) ≫ c_K'` |
| u_A is the actual reconstruction unit | The definition `unit` applies `asIso` to `presentation.adjunction.unit.app M.obj`, using `unit_iso`, then only lifts the resulting isomorphism into the full category |
| Every a equals u_B inverse L(r a) u_A | `Comparisons.reconstructX/Y`: `a = (unit A).hom ≫ lim.map (red.map a) ≫ (unit B).inv` |
| Applies also to transported unit/counit | The reconstruction identities quantify over every actual morphism between any objects of C_X or C_Y; in particular all restricted/transported adjunction components are included. No separate restriction on a is imposed |

The existential maps `e`, `pO`, and `d` are the ordinary open, ordinary direct-image, and
derived direct-image scalar comparisons. The first two concluding conjuncts write out the
`open_normalized` and `push_normalized` finite scalar equations for every strict tower and
index. The third conjunct is `IsPushScalarNormalized ... pO d`, fixing the derived map by
the two composition units on complexes. These are exactly the fields previously packaged
as `ScalarComparison`, with no reference to that theorem-owned structure in the signature. `LimitPresentation.unit_projection` pins
the reduction/limit adjunction to the actual quotient augmentations. Thus the comparisons
and reconstruction identity do not use arbitrary choices of identifications or adjunctions.

### Coordinate construction

The recorded gluing functor is expressed through the sequence-site presentation, whereas the
compactification-limit word uses the original strict category. The three helpers bridge exactly
these published interfaces. `openCoordinates` localizes the given ordinary exact equivalence
word. `pushCoordinates` uses the canonical right-derived composition comparisons; the source
equivalence preserves K-injectives and the target equivalence is exact. `supportCoordinates`
composes these and contracts the middle equivalence by its actual counit. There is no new
postponed comparison theorem, and no bare `Nonempty` is used to select a comparison map.
These are helpers belonging to the comparison in this node, all listed in `lean.declarations`.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (including its field and algebraic-closure instances).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; it reexports `Padic.coefficientExtensionIntegers`, the fixed uniformizer and finite quotients.
- `def-weil-scheme-morphism-properties` is a convention node, not a declaration. Its named Mathlib properties are used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.SmoothOfRelativeDimension`; the recorded `Smooth` notion follows from it.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `WeilConjectures.integralConstantToCompletionOfUniverses` and the reexported actual completed sheaf, used through the recorded completed scalar interfaces.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spCoefficientRings`, `spEllIdeal`, with n : Nat denoting exponent n+1.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spNormalizedConstructibleTorTowers`, `spNormalizedConstructibleTorTowerCategory`, `IsSpNormalizedTower`, `spConstructibleTorTowerCategory`.
- `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `spCompletedReduction`, `spCompletedStrictTower`, `spCompletedTotalLimit`, `SpNormalizedEquivalence`, `sp_normalized_equivalence`.
- `det-sp-integral-direct-image-tower` remains a recorded dependency, but its declaration `IntegralDirectImageTower.shriek` lives on the condensed `Integral` category, not C_T's completed scalar-module category. Its unused public import is removed; the actual typed compactification functor comes from the definition node below. This interface distinction is recorded in `lean.note`.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.support`, `Charts`, `Levels`, `tower_gluing`; its reexported `SpTowerCalculus.C`, `Coordinates`, `F`, `compactSupport`, `realization`.
- `Sheaf.Paper.CompleteCompactificationLimitSupport` (explicit statement dependency `def-sp-complete-compactification-limit-comparison`): `LimitPresentation`, `image`, `comparison`, `reduction`, `forgetting`, `totalLimit`, `towerOpen`, `towerPush`, `fixedOpenOrd`, `fixedPushOrd`, `forgetDerived`, `ScalarSquares`, `Evaluation`, `ordinaryTowerOpen`, `ordinaryTowerPush`, `ordinaryOpenEvaluation`, `ordinaryPushEvaluation`, `ordinaryOpenScalar`, `ordinaryPushScalar`, `IsPushScalarNormalized`. This is now a direct public import.
- `Sheaf.Paper.CompleteCompactificationLimitRealization` is a proof-only import: `complete_compactification_limit_realization` supplies the scalar data and the comparison theorem used in the proof plan. Its `ScalarComparison` structure is not used in any delivered declaration.
- Proof imports: `Sheaf.Paper.SmoothPurityTowerGamma` (`SpTowerGamma.tower_gamma` and normalization preservation); `Mathlib.AlgebraicGeometry.Noetherian` (`LocallyOfFiniteType.isLocallyNoetherian`, `IsNoetherian`, `IsLocallyNoetherian.quasiSeparatedSpace`); `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (`QuasiCompact.of_comp`). Properness and the tower-shriek/abelian interfaces are reexported by statement imports.
- `Mathlib.CategoryTheory.Adjunction.Restrict`: `Adjunction.restrictFullyFaithful` and its exact unit/counit equations are available for the restriction proof. `Adjunction.FullyFaithful` provides the full-faithfulness consequences of an invertible unit.
- The coordinate definitions use the published `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryCompRightDerivedFunctorIso`, `Functor.rightDerivedFunctorCompMapDerivedCategoryIso` and the exact section equivalences' counits.

### Searches

All searches were performed read-only, before writing the statement.

- `msearch.py ... leanfinder "Natural reconstruction comparisons between derived complete integral constructible sheaves and normalized coefficient towers, including compact support direct image"`: eight hits, chiefly ordinary scheme normalization and condensed/sheaf section constructions, none this statement.
- `msearch.py ... leansearch "An adjunction restricts to full subcategories with the same unit and counit, and an invertible unit reconstructs every morphism"`: found `Adjunction.restrictFullyFaithful`, its exact unit/counit formulas, and `Adjunction.toEquivalence`. Read their sources; reuse their categorical notions instead of restating them.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.FullyFaithful"`: no hits, unknown identifier (FullyFaithful is under Functor).
- Corrected Loogle query `"CategoryTheory.Adjunction, CategoryTheory.Functor.Full"`: twelve hits including `unit_isIso_of_L_fully_faithful` and `counit_isIso_of_R_fully_faithful`; categorical results only.
- `msearch.py ... grep "reconstruction.*comparison|normalized.*equivalence"`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the exact node id and proposed names: no exact match. The related `WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction` was opened and read: it has the finite-Tor exceptional-system construction with other prescribed operations, not this smooth-purity strict-tower comparison with the specified G and actual b,c. It does not replace this node.
- Concept searches over the pro-etale source and `lean/Sheaf/Paper` located the recorded normalization, gluing, compactification comparison and full-subcategory APIs used above. The proposed namespace/names were also checked against `dag/lean_names_upstream.json`, Mathlib, and both source roots: no collision.

### Edge cases and checks

- Empty X and/or Y: no nonempty hypotheses; all categories and natural transformations remain defined. A morphism to empty Y entails empty X, as usual. The compactification may also be empty.
- d = 0: `d₀ : ℕ` includes zero. Neither the statement nor the comparison adds a positive-dimension condition.
- Zero objects and zero morphisms, identity arrows, and arbitrary noninvertible arrows: every morphism is included in `reconstructX/Y`, and no map is assumed invertible there except the actual unit.
- Ell = 2, ramified E, and the first positive quotient: all use the recorded actual ell-power rings, not an unramified or uniformizer-equals-ell shortcut. Index n=0 means exponent one throughout inherited tower definitions.
- Non-normalized constructible towers are excluded only by the node's own N_T; the original supplied adjunction remains on the full ambient uniformly bounded constructible category. No extra compatible-origin witness changes N_T.
- Natural transformations are in the ordinary derived category of strict towers. No faithfulness of finite evaluation on morphisms is used.
- The full categories use the inherited ambient morphisms, and `unit_same/counit_same` compare those exact arrows.
- A common universe u contains the finite-field datum, E and schemes. The small site remains object universe u+1 and hom universe u; no equality of those site universes is imposed. All binders are explicit, with `set_option autoImplicit false`.
- Canonical normalization test: an independent sign twist of b fails `direct_hom`; a sign twist of c fails `exceptional_hom`; replacing u by an arbitrary object isomorphism fails its definition. Simultaneous changes of the supplied adjunction must still meet the recorded chart/level constraints, and its actual restricted maps are retained by `unit_same/counit_same`.

No counterexample or statement correction was found. No disputed claim is recorded.

Original-delivery validation: `scompile.py O2 lem-sp-integral-reconstruction-comparisons <module>` passed both
sandbox and library compilation (21.8 s and 14.7 s respectively), with no errors or warnings.
The first version had an omitted explicit ObjectProperty parameter in `isoMk`; fixed before
the passing compile. Only `integral_reconstruction_comparisons` has a `sorry` proof.

## Second reading by O2

This is an additional worker self-check, not a claim of an independent reader. The dispatch
brief forbids starting other agents and assigns independent review to the maintainer.

I reopened the node and final module together and checked each row above. The direct and
exceptional naturality fields have the paper's directions after translating composition
notation. The b formula uses the compactification comparison before reduction and then the
actual counit, while c uses that counit directly. The reconstruction unit is the actual
adjunction component, not the potentially different unit of an unspecified equivalence.
The equality of equivalence functor/inverse with the literal restrictions supplies full
faithfulness and inverse L. The normalized subcategory definition and actual unit/counit
carrier equalities are unchanged. The original module-mode compile checked the full package,
not a legacy import probe. No changes to the node statement or dependency interfaces were
made during the original check. The maintainer subsequently checked the mathematics clause
by clause at immutable head `25f208747d02`, and returned the dependency/import issues repaired below.


## Returned delivery repaired

Return L at immutable head `25f208747d02` identified H2 and H9. All requested repairs:

1. Added the existing definition node `def-sp-complete-compactification-limit-comparison`
   to this item's `stmt_deps`; publicly imported its owning module
   `Sheaf.Paper.CompleteCompactificationLimitSupport`.
2. Replaced the existential `ScalarComparison` with existential `e`, `pO`, `d` of
   exactly its three map types. Wrote its `open_normalized` and `push_normalized`
   equations out verbatim with the present scheme/presentation parameters, and retained
   `IsPushScalarNormalized ... pO d` as a conjunct. `Comparisons` receives the same `e,d`.
   The realization theorem module is imported only for the proof. No map normalization
   or canonical comparison condition was dropped or strengthened.
3. Removed the unused public import of `IntegralDirectImageTower` and added the required
   `lean.note`: its `shriek` has the condensed `Integral` category as domain, not C_T's.

Before editing, the sandbox node's non-Lean fields were compared with current shared main:
there were no differences. All 14 supporting declarations and the accepted comparison
formulas are retained unchanged. Only imports, the expanded theorem signature, metadata,
and this report change. The mathematical node statement and proof text are unchanged.
The node's `lean.statement` is regenerated verbatim from the repaired theorem signature.
The expansion preserves every previous edge case: the three maps are existential output,
not additional hypotheses, with all original normalization conditions retained.

Repair validation: the prescribed `scompile.py` compiled the repaired file in sandbox mode
(27.4 s) and library mode (17.1 s), with no errors or warnings. The signature has no
`ScalarComparison` references; there remains exactly one `sorry`, in the named main theorem.
All Lean lines have at most 100 characters. The only non-Lean node delta against current
main is the addition of the requested existing definition to `stmt_deps`.
