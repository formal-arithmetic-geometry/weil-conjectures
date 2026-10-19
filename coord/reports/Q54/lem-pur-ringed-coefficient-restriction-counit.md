## Worker report

Current return repair (immutable returned head `99f1ec254060`): the saved packet's
required initial dry run reproduced the timeout in
`RingedCoefficientChangePresentations` on both the private overlay and server
confirmation. A scratch profile of the restriction component identified costly
kernel checking of generated `recOn`, `casesOn`, `noConfusion` and flat-constructor
code. The repair factors that component into
`CoefficientRestrictionChangeData` (the eight comparison data fields),
`CoefficientRestrictionChangeNormalized` (a proposition containing the same nine
explicit compatibility and normalization equations), and
`CoefficientRestrictionChange` (the data together with that proof). The two
naturality equalities, the other representative equations and the item theorem's
signature are unchanged. The component has been refactored within its existing
module; no module was split off to evade the time limit.


This repairs the returned Q54 packet rather than re-pushing it. The retained packet's first dry run failed at `tensorPullback.map_id` and `map_comp`, whose proofs used `Subsingleton.elim` for non-subsingleton module Hom sets. The replacement uses the existing tensor object and morphism constructions through explicit functor equations, as the published ringed tensor-pullback interface does; it introduces no separate tensor functor and proves no functor laws in stage 2.

The theorem is `CategoryTheory.RingedCoefficientCounit.ringedCoefficientRestrictionCounit`. It asserts existence of normalized derived presentations, the counit identity for every such presentation and every derived object, and existence plus both naturality equations for every compatible coefficient triple. The only postponed proof is this theorem, with the node's five proof steps in its docstring. There is no statement correction: comparison with the current shared node found only the authorized added definition dependencies and Lean record.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| Small sites and a geometric morphism | `C,D`, `Category.{v}`, `JX,JY`, `UnivLE`, `EssentiallySmall`, `inverse`, `direct`, `geom`, and `leftExact`; no equality of site-object and morphism universes |
| A commutative coefficient ring and its constant sheaves | `A : CommRingCat.{r}` and `constantRing JX A`, `constantRing JY A`, abbreviating the recorded `constantSheaf` |
| Identification of inverse image of constant coefficients | `IA : AlgebraicInverseImage inverse (constantRing JY A) (constantRing JX A)` |
| Algebra sheaves, their inverse image, and structural map | `RX,RY,RI`, `IR`, `c`, `aX,aY,aI`; `haI` is compatibility with inverse image, and `hc` is `aI ≫ c = aX` |
| Ordinary module categories and unbounded derived categories | `modules` is the recorded `ringedSiteModules`; all four `DerivedCategory` types and their explicit `HasDerivedCategory.{w}` instances are Mathlib's localization |
| Exact coefficient restriction | `restriction` is Mathlib's `SheafOfModules.restrictScalars`; `DerivedPresentation.exactness : CoefficientExactness aX aY` supplies finite-limit and finite-colimit preservation as part of the theorem's existence conclusion. There are no such exactness hypotheses on the theorem |
| Ordinary tensor pullback | `OrdinaryPresentation.pull_obj` and `pull_map` identify it with `changeOfRings c (IR.modules.obj M)` and the existing sheafified `id ⊗ h` map. Pullback is not assumed exact |
| Direct image and canonical ordinary adjunctions | `pushRUnderlying` and `pushAUnderlying` are natural identifications with `direct`. `tensorUnitFormula` fixes the sheafified `1 ⊗ x` map. `adjRFormula` and `adjAFormula` fix both Hom bijections using `geom.homEquiv`; the geometric adjunction is used in the equations |
| Compatibility of inverse image with coefficient restriction | `inverseRestriction` and `inverseRestrictionFormula` fix the underlying comparison through `IA.moduleUnderlying` and `IR.moduleUnderlying` |
| Ordinary scalar unit and composition comparison | `scalarUnitFormula` uses the tensor unit after inverse restriction; `ordinaryKappaFormula` fixes the underlying direct-image identity |
| Q_R = Lf_R^*, with flat-term K-flat representatives | `p.r.left` has `isLeft`, a universal localization comparison `epsilon`, and `p.flatComparison` makes that comparison invertible on the existing `IsKFlatIndependentCoefficients` and `IsFlatOnSite` predicates |
| Q_A = inverse image on constant-A complexes | `p.a.left` is the same normalized derived construction for `IA.modules`; `p.exactA` says its localization comparison is invertible on all complexes. The structural additive instance for `IA.modules` is available from `o.inverseAdditive` and is bound explicitly for elaboration |
| F_R and F_A computed with K-injectives | `p.r.right`, `p.a.right`, the two `isRight` fields, localization units `eta`, and `onInjective` fix their universal derived-functor structures and K-injective computations |
| Canonical derived adjunctions and counits | `DerivedAdjunction.adj` is constrained by `homFormula`: on a chain map `P → push I` with I K-injective, the derived transpose is `epsilon_P` followed by the localized ordinary transpose. This fixes the adjunction, not only its functors |
| Tau's specified representative | `p.tau` is a natural transformation. `p.tauFormula` is the localization equation for `o.scalarUnit` on every flat-term K-flat complex, with `xFactors`, `yFactors`, and both left-derived comparisons explicitly present |
| Kappa's Tag 0D6E normalization | `p.kappa` is a natural isomorphism. `p.kappaFormula` quantifies over K-injective I and every K-injective resolution j of its restricted complex; the right side contains exactly `Q(f_*j)`, followed by the canonical resolution identifications |
| Displayed counit equality for every K | `CounitCompatibility p` is the conclusion `p.tau.app (p.r.right.obj K) ≫ p.x.map (p.r.adj.counit.app K) = p.a.left.map (p.kappa.hom.app K) ≫ p.a.adj.counit.app (p.x.obj K)` |
| Naturality in K | Tau, kappa, and the adjunction counits are actual natural transformations/isomorphisms |
| Naturality in compatible algebra homomorphisms | The theorem quantifies over separate primed sheaves and maps `bX,bY,bI`, their three algebra equations, the structural square, and the inverse-image square. It concludes `Nonempty (CoefficientChange p p' bX bY bI)` and `∀ m, m.IsNatural`. `IsNatural` uses `restrictions`, `direct` and `constants` component fields and is two actual derived equalities: tau with the canonical pullback mate, and kappa with the normalized direct-image comparisons |
| No extra boundedness, coefficient-flatness, completeness or constructibility | None of these is a binder. Flatness and K-flatness appear only in representative normalizations, with existence of such representatives supplied by the recorded resolution theorem |

The presentation definitions contain no arbitrary proposition-valued normalization field. The new `normalized` field has the fixed type `CoefficientRestrictionChangeNormalized`; its nine fields are exactly the displayed compatibility and localization equations, with no proposition supplied by a caller. In particular, `CounitCompatibility` is a separate proposition, not a field of `DerivedPresentation`, and `CoefficientChange.IsNatural` is not a field of `CoefficientChange`. Changing tau to zero in the identity example violates its representative equation. Assigning False to a normalization field is impossible: each normalization is a proof of a displayed equality or of a specified universal/representative property.

Dependencies used and read:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.AlgebraicInverseImage`: `SheafOfModules.AlgebraicInverseImage`, including the full underlying-sheaf and operation identifications.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: `changeOfRings`, `changeOfRingsHom`, `changeOfRingsPresheaf`, and the sheafification unit.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`; its object/map and K-flat normalization conventions are retained, without identifying site universes.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows` reexports the general `Sheaf.Paper.ProjectionFormulaArrows` interface. Its `ringedProjectionFormulaArrows` documentation and canonical-adjunction normalization were read. The present item only uses its canonical derived adjunction and counit convention; no perfect coefficient object or projection formula is introduced here.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: `CategoryTheory.ringedToposDerivedPushforwardComposition`; the `Q(f_*j)` formula is written explicitly in `kappaFormula` and `betaFormula`.
- Proof imports also retain `module_pullback_pushforward_adjunction`, `preDerivedAdjunctionGeneral`, `sheafRingDerivedCoefficientAdjunction`, and `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`. The K-flat predicate and resolutions use the existing independent-coefficient interface, not a duplicate definition.

Edge cases read against the formulas: f=id; R_X=R_Y=A; identity coefficient maps; zero complex; the zero ring; non-flat quotients A→A/I; unbounded complexes; independent site-object and site-morphism universes. Identity comparisons are forced by the unit and representative equations. The zero-complex case has the ordinary zero equality. Non-flat maps require left derivation rather than the retained packet's erroneous exact module pullback. No positive-rank, nonzero-ring or bounded-support premise excludes these cases.

Searches: the retained `searches.jsonl` records the earlier searches. This repair reran msearch LeanFinder for the canonical coefficient counit and separately for coefficient-change mates; both returned ordinary sheaf pullback/unit/counit and abstract derived-adjunction results, not this normalized coefficient diagram. Loogle `CategoryTheory.Adjunction.comp_counit_app` returned the formal composite counit, without the ringed representative normalization. msearch grep `CoefficientChange|ringedCoefficientRestrictionCounit` and `coefficient.*counit|counit.*coefficient|CoefficientChange` in Mathlib CategoryTheory returned zero hits. LeanSearch for a canonical K-flat/K-injective coefficient-square presentation returned total-left-derived counits and unrelated adjunctions, not the presentation. `rg` in the upstream WeilConjectures sources and the shared Sheaf sources found no declaration of this item or either presentation. `tools/blueprint_refs.py search 'coefficient counit'` found one unrelated finite-field coefficient node. DAG searches found the theorem and specialized applications, not an existing normalized presentation.

The source passages were opened locally: `sites-modules.tex`, lemma-adjoint-pullback-pushforward-modules (03D7), and `sites-cohomology.tex`, lemma-adjoint (07A6) and lemma-derived-pushforward-composition (0D6E). Their ordinary tensor Hom bijection, derived adjunction and composition constructions give the equations used here. No source-level mathematical dispute remains.

## Second reading by Q54

I performed a separate pass with the current node and all delivery modules open; this dispatcher brief forbids starting another agent. The retained report was discarded because it named absent declarations. This report names only declarations and fields actually present in the repaired files.

The pass checked all return points: the bare normalization propositions were removed; both ordinary adjunctions now use `geom`, tensor pullback has explicit object/map equations and the sheafified unit, both derived adjunctions have the representative Hom formula, tau has its flat-term K-flat equation, and kappa has the `f_*j` equation. Exactness of restriction is supplied by existence of a presentation. The counit equality and both coefficient-naturality squares are conclusions. The coefficient maps range between distinct primed and unprimed rings, with all three maps used in their compatibility equations. The new nodes and declaration inventories describe exactly these structures, and their primary Lean signatures are copied verbatim. The theorem docstring contains all five proof steps. The naturality squares were checked for source/target orientation against the displayed counit formula and the mate defining sigma.

## New nodes

`def-pur-ringed-coefficient-counit-presentations`, module `Sheaf.CategoryTheory.RingedCoefficientCounitPresentations`, defines the ordinary and derived presentations, their exactness and representative normalization equations, and the separate counit proposition. It is a package of the canonical constructions of Tags 03D7, 07A6 and 0D6E, using existing module, tensor and derived-category definitions. The searches above and in its JSON record found no existing package. This repairs the retained new node's inaccurate description and non-verbatim signature.

`def-pur-ringed-coefficient-change-presentations`, module `Sheaf.CategoryTheory.RingedCoefficientChangePresentations`, defines changes between two such systems and the separate two-square naturality proposition. Its component records `CoefficientRestrictionChange`, `CoefficientDirectChange` and `ConstantDerivedChange` organize the dependent fields. The restriction component now stores its eight data fields in `CoefficientRestrictionChangeData` and its nine equations in the proof-valued `CoefficientRestrictionChangeNormalized`, to avoid large generated recursors for the combined record. It specifies ordinary underlying identity maps, derived localization and K-injective equations, and the pullback comparison as an adjoint mate. It depends on the first new node. It is separated to keep file-only compilation within the required limit. The same source passages and the separate coefficient-change searches justify the package; no existing declaration supplies it.

## Current return self-check

Compared the retained item with the current shared node: only `lean` and the two
added definition dependencies differ. In the current source, the restriction
component still contains all eight data fields (`vx`, `vy`, their localization
factorizations, `ordinaryX`, `ordinaryY`, `rhoX`, `rhoY`) and all nine proof fields
(`commX`, `commY`, `commI`, `commStructural`, `commInverse`, the two ordinary
identity equations and the two localization equations). Only their storage
changes. `CoefficientDirectChange`, `ConstantDerivedChange`, `CoefficientChange`,
`CoefficientChange.IsNatural`, and the main theorem retain every original field,
equation and binder. The new helper structures have the same source/blueprint
identification and appear in the definition node's declaration inventory.
