## Worker report

The module `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization` states
`AlgebraicGeometry.Etale.rawRestrictedClassNormalization`. Every theorem proof is
`sorry`. The auxiliary definitions have actual data. The node records `lean` and adds the landed definition nodes
`def-weil-pbc-abelian-higher-image-class` and
`def-sbc-raw-affine-restricted-cohomology` to `stmt_deps`. The removed theorem node
`sbc-lem-higher-direct-image-presheaf` is not a dependency. There is no statement
correction, disputed statement, new node, or dependency module.

The main statement follows the corrected canonical-class formulation in the node,
not an arbitrary witness of the natural-comparison existence theorem.

Hypotheses and objects:

- Any schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`. There is no proper,
  affine, quasi-compact, separated, or torsion assumption.
- Abelian coefficients: `(F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  This is the recorded abelian-sheaf encoding, with one common coefficient universe.
- Every nonnegative degree: `(q : ℕ)`, including zero.
- Every etale object: `V : S.Etale`, with no affinity restriction.
- The chosen chart is `pullback V.hom f`, with projection `pullback.snd V.hom f`.
  This is the existing upstream convention V ×_S X, canonically symmetric to the
  node's X ×_S V; it retains both scheme projections and imposes no condition.
- `abelianHigherDirectImageRawPresheaf f q F` is exactly A: free abelian
  representable, sheafification, inverse image, degree-zero single, shifted Hom.
- `rawAffineRestrictedCohomology f q F V` is exactly P(V), computed by the existing
  derived global sections functor on the degree-zero complex of j_V^{-1}F.

Each assertion:

1. The first conjunct is an isomorphism `c : A ≅ normalizationRestrictedPresheaf f q F`
   with `c.hom.app (op V) = rawRestrictedCohomologyComparison f q F V` for every V.
   This fixes the isomorphism component by component to the required evaluation;
   existence of some isomorphism would not suffice. A's restriction is the existing
   free-represented precomposition. P's object is definitionally the required
   restricted cohomology group.
2. The second conjunct identifies every P restriction with
   `normalizationCohomologyRestriction f q F t`. The latter uses the existing
   `rawAffineComplexPullback`, and then the exact-pullback single comparison and
   inverse-image composition. It contains no raw Hom or evaluation inverse.
   The map of charts is the actual map of the etale base-change functor.
3. `normalizationIota` is the canonical cocycle map. Its data are specified
   independently of raw evaluation and raw classes: restrict an injective
   resolution, use its canonical derived-sections computation, identify sections
   with evaluation at the chart, and use the map from sectionwise homology to
   sheaf homology induced by sheafification. In detail,
   `normalizationResolutionClass` uses `toSheafify`, the inverse
   `ShortComplex.mapHomologyIso` for exact sheafification, homology of its counit,
   and the two resolution/classical-derived/total-derived comparisons. Thus it
   sends a section cocycle to its cohomology-sheaf class, as in Tag 072W. The
   degree is indexed by integers using the standard extension of the injective
   cocomplex; `isoRightDerivedObjCochainComplex` includes that canonical transport.
   No inverse raw evaluation is used in this definition.
4. `normalizationKappa` bundles exactly the existing function
   `abelianHigherDirectImageClass f q F V` at each etale V.
   `normalizationKappaComponent` uses `AddMonoidHom.mk'` and the separately named
   theorem `normalizationClass_add` to supply only its additivity proof.
   `normalizationKappaComponent_naturality` separately states the presheaf
   naturality equation and supplies that proof field of `normalizationKappa`.
   No data are chosen and no upstream higherDirectImagePresheafToHomologyAbelian
   is used. The components reduce to the prescribed class function, so the
   derived adjunct, homology, identity generator and canonical shift are fixed
   by the landed definition node, rather than by an unowned helper.
5. `normalizationLift` is the inverse of the sheafification adjunction's Hom
   equivalence applied to this kappa. Therefore it is the specified unique lift
   E and has the defining equation eta_A ≫ E = kappa. Its data are not obtained
   from an existential comparison or an unproved existence claim.
6. The additional component equation explicitly identifies normalizationKappa
   with abelianHigherDirectImageClass. `IsIso (normalizationLift f q F)` is the assertion that this E is invertible.
7. The normalization conjunct, for every V and z, is precisely
   `normalizationIota ... (rawRestrictedCohomologyComparison ... z) =
   abelianHigherDirectImageClass ... z`, the displayed iota(c(z)) = kappa(z).
8. The last conjunct quantifies over all coefficient sheaves G and maps φ : F ⟶ G.
   Its four equations give naturality of c, iota, kappa, and E respectively.
   Raw coefficients are shifted postcomposition; restricted coefficients are
   derived global sections of the restricted sheaf map; higher coefficients are
   H^q of Rf_* applied to the single sheaf map. The equation for E uses the
   sheafification of that actual raw coefficient natural transformation.

Auxiliary proof obligations are named separately, with source and proof docstrings:
`normalizationRestrictionAugmentation_quasiIso` and
`normalizationRestrictionComplex_isKInjective`. They are the exactness and
bounded-below-injective assertions of step 1 of this node's proof, needed as proof
fields of the real restricted-resolution construction. Its underlying complex and
augmentation are explicit; neither is chosen from a sorry existence theorem.
The other two postponed helper theorems are `normalizationClass_add` and
`normalizationKappaComponent_naturality`. Both belong to this node's canonical
class-map construction (proof steps 4 and 6), are listed in `lean.declarations`,
and have complete source/proof docstrings. Their proofs alone are postponed;
the functions they certify are the existing explicit class function. The final
theorem docstring records all eight proof steps and their dependencies.

Dependency declarations read and used:

- Mathlib's `AlgebraicGeometry.Scheme`, `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, `CategoryTheory.Sheaf`, `Limits.pullback`,
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`, and the homology and
  evaluation functors. Scheme base change is the pullback underlying the recorded
  base-change convention, not its unrelated module-pullback helper.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `upperStarComp`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedGlobalSections`, `cohomology`.
- `WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`:
  `rawRestrictedCohomologyComparison`, `RawRestrictedComparison.sectionsIso`;
  the new natural sections comparison is assembled from the same existing
  restriction/localization and terminal-section natural isomorphisms.
- `WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology`:
  `rawAffineRestrictedCohomology`, `rawAffineComplexPullback`.
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`:
  `abelianHigherDirectImageRawPresheaf`; its existential comparison is read but
  is not chosen to define E.
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility`:
  `abelianHigherDirectImageClass`, `abelianComparisonShift`, and the explicit
  class-pullback compatibility theorem.
- The direct import of `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
  was removed. The raw presheaf is imported from its recorded owning interface,
  `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`.
- `def-weil-pbc-abelian-higher-image-class` owns the existing
  `AlgebraicGeometry.Etale.abelianHigherDirectImageClass` in
  `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility`.
  Its full signature, body and docstring were checked: it is the exact canonical
  derived-adjunction/evaluation function required by this node.
- `def-sbc-raw-affine-restricted-cohomology` owns the reused
  `rawAffineRestrictedCohomology` and `rawAffineComplexPullback` in
  `WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology`; the formulas
  and signatures were read and agree with P and its canonical restriction.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus` and its unit/counit comparison signatures, used in the
  existing class construction and in proof step 6.
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`:
  `CategoryTheory.siteHigherDirectImageSheafifiedPresheaf`, whose displayed
  canonical sheafification/homology/counit composite is used in step 7.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution`:
  `CochainComplex.KInjectiveResolution.homologyRightDerivedFunctorObjIso`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`:
  `InjectiveResolution.isoRightDerivedObjCochainComplex` and
  `Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`.
- Proof imports include the recorded resolution evaluation, restriction of
  injectives, evaluation-isomorphism, inverse-image exactness, and cohomology
  pullback functoriality modules. The recorded pullback uses `Sheaf.H`; the actual
  complex-level pullback in `RawAffineRestrictedCohomology` supplies its already
  existing derived-sections version, so no Ext/derived identification is assumed
  as a new hypothesis. D^+ and its homology are the recorded generic constructions;
  the torsion predicate in the mixed derived-categories node is not needed.

Edge cases checked before stating:

- q = 0 uses the degree-zero single and identity shift comparisons; it retains the
  ordinary adjunction normalization, rather than allowing its negative.
- Empty X or an empty chart has the zero sections complex. All the constructions
  still type, with the unique zero class map; no nonemptiness assumption appears.
- F = 0 and zero coefficient maps are covered by the additive constructions.
- Identity coefficient maps and chart identities are included. P's functor laws
  follow by cancellation of the canonical resolution comparison and functoriality
  of sectionwise homology. There is no restriction to affine objects or a bound
  on q and no independent smaller coefficient universe.

Searches (2026-10-21):

- msearch leanfinder, query “Derived adjunction raw evaluation to restricted etale
  cohomology equals the canonical cocycle class into the higher direct image
  sheaf”: eight hits on `Sheaf.H`, `cohomologyPresheaf`, and general adjunctions;
  none normalizes these two specified maps.
- msearch loogle, query `CategoryTheory.presheafToSheaf, CategoryTheory.toSheafify`:
  seven hits on sheafification units and compatibility, no normalization theorem.
- msearch grep, query `homology.*[Tt]o.*[Ss]ection|homologyPresheaf|homologyTo`
  in CategoryTheory: general sheaf cohomology-presheaf declarations, no match.
- msearch leansearch, query “Canonical map from cohomology of sections of an
  injective resolution to higher direct image cohomology sheaf agrees with free
  represented derived adjunction evaluation”: eight hits on resolution and
  right-derived naturality/computation, no such normalization theorem.
- rg in both project roots for rawRestricted, abelianHigherDirectImageClass,
  higherDirectImagePresheafToHomology and restricted presheaves found the reused
  constructions and the naturality/isomorphism statements. The natural raw
  comparison theorem is existential and lacks the cocycle normalization.
  `exchangeChartTheta` uses inverse evaluation followed by the raw class map,
  so it cannot replace the independently specified cocycle map in this item.
- Exact item-id search in WeilConjectures found no existing normalization statement.
  Exact new full-name searches in WeilConjectures and Sheaf found no collisions
  (an unrelated private normalizationLift has a different namespace).

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
No shared source file or launcher tool was edited; no git command, local build,
project build, or forbidden preflight command was run.

## Repair of returned delivery

The return on immutable head `bc0785c3579e` identified H2: the saved item added
`sbc-lem-higher-direct-image-presheaf`, a theorem node removed by stage-1 review,
solely to own a plain definition used by kappa. The initial saved-packet dry run
passed mechanically (`0929159a7e2`), but the semantic dependency defect was still
present. This repair removes that addition, imports the raw-presheaf owning
interface, and builds kappa directly from the landed definition node
`def-weil-pbc-abelian-higher-image-class`, with named additive and naturality
proof obligations. The advisory definition dependency
`def-sbc-raw-affine-restricted-cohomology` was also added.

The main statement, all geometric/coefficient hypotheses, iota, the restrictions
of P, the sheafification lift E, and the coefficient naturality clauses are
retained. The new wrappers only bundle the specified class function as an
additive natural transformation. No correction of the natural-language statement
is needed, and no other node is edited.

Self-check completed: the sandbox node differs from the current shared node
only in `lean` and addition of these two landed definition ids in `stmt_deps`.
The main Lean signature matches `lean.statement` verbatim; all 22 public
declarations are listed, and every Lean line is at most 100 characters. Searches
of the current project roots for the three new helper names found no collisions. The existing three-kind searches above still apply; no new
mathematical notion has been introduced. Read the source of Stacks 03Q8/072W and
the two newly cited definition interfaces. Degree zero, empty charts, zero
coefficients, and all coefficient morphisms remain included with universes u/u+1.

Repair validation: the prescribed server `scompile.py` finished both sandbox
and library checks cleanly (50.7 s and 52.3 s), with no diagnostics. The repaired
packet then passed `deliver2.py --no-push`: preflight and per-file compilation
OK at dry-run commit `51da7338cd3`. The report-only validation update is checked
again by the final dry run and delivery wrapper.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
