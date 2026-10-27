## Worker report

Repair of L's immutable-head return a51c40daa5f0. This delivery replaces the prior
existing:true attachment with the new module
`Sheaf.Paper.RationalScalarMixedUnitCancellation` (existing:false). All declarations
listed in the item's lean.declarations are new declarations in that module. The
natural-language statement and proof are unchanged. The current read-only base has
no lean attachment for this item; the retained sandbox had the returned parent
attachment. The repaired node is regenerated from the current base, preserving its
other fields. The delivery wrapper supplies the current live base/rebase.

The only additional statement dependency is the already landed
`lem-per-rational-pullback-composition-coherence`, previously a proof dependency.
It is needed in signatures/bodies to extract the canonical, fully normalized
geometric compositors and unitors. No dependency interface is repaired, no new DAG
notion is introduced, and no statement correction is needed.

### Return repaired, point by point

- H4: public imports use `RationalScalarBalancedLocalization` and
  `RationalScalarCompletionUnitSquare`. Every scalar coefficient map in the new
  signatures is `rationalBalancedCoefficient`, every theta is
  `rationalBalancedTheta`, and `rationalMixedBetaComponent` is the restriction and
  rationalization of `rationalScalarStrictBeta`. There are no bX/bY records.
- H3: D is exactly `pbcDerivedExtend (rationalBalancedCoefficient ...)`.
  `RationalScalarMixedUnitCancellation.compatibility` spells out the displayed
  equation in the node's orientation. Its `beta_normalization` fixes every
  component to `rationalMixedBetaComponent`. Its `ordinary_units` and
  `ambient_normalization` fix zeta by tensor generators and derived computation
  counits. Alpha is precisely aE.alpha/aF.alpha from the dependency's recorded
  `RationalRealizationPullbackComparison`, including that record's normalization.
- Ownership: the downstream `RationalRealizationScalarCoherence` module is never
  imported. No declaration of that module is recorded, copied under its name, or
  claimed. The primary declaration is the new theorem
  `AlgebraicGeometry.Scheme.rationalScalarMixedUnitCancellation`.

### Hypotheses and objects

The Lean schemes X and Y mean respectively X' and X in the node.

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite Q_l extensions E subset L | `(E F : Type u) [Field E] [Field F]`, their Padic algebra and FiniteDimensional instances, `(i : E →ₐ[ℚ_[l]] F)`; an algebra hom between fields is injective |
| Valuation rings and chosen uniformizers | The dependency's `PbcIntegralRing`, `pbcIntegralDatum`, and `pbcUniformizer`, unchanged |
| Both schemes noetherian, finite dimensional, ell invertible | `[IsNoetherian X] [IsNoetherian Y]`, one `Fact (∃ n : ℕ, topologicalKrullDim ... ≤ n)` and one `Fact (∀ x, IsUnit (l : ...presheaf.stalk x))` for each scheme |
| Arbitrary geometric map | `(g : X ⟶ Y)`; no smoothness, flatness, properness or nonemptiness assumption |
| Small pro-etale sites | The recorded `Scheme.ProEt`, object universe u+1 and morphism universe u; no equality imposed |
| Completed integral coefficients B and continuous rational coefficients | `pbcAdicCompletion ... (pbcIntegralDatum ...)`, `rationalCoefficientSheaf`, and the supplied normalized `RationalModuleRealization` records |
| Completed constructible category and raw rationalization | `PbcBoundedConstructibleComplete` with all three published conditions; `PbcRationalDerivedCategory`/`pbcRationalization`, with unchanged integral objects and localized Hom modules |
| Sheaf modules and unbounded derived tensor | `pbcModules`, `pbcExtend`, `pbcDerivedExtend`, `DerivedCategory`; these are the dependency's constructions |
| J's object/fraction normalization | Four supplied `RationalModuleRealization` records sXE,sYE,sXF,sYF; their `objects` and `fractions` fields are retained, not replaced by arbitrary functors |
| C and T | `pbcEmbeddingAmbientTensor`, `pbcEmbeddingIntegralTensor`, `pbcRationalScalarExtension` |
| P, completed P and gamma | `pbcActualDerivedPull`, `pbcActualStrictCompletedPull`, and `pbcActualStrictCompletedPullUnit`, the actual quotient-tower augmentation |
| H and alpha | `rationalPullDerived ... aE.rationalCoefficient`, respectively F, and the supplied record's `alpha` |
| Canonical inverse-image localization identification | The public imported dependency and aE/aF's `rational_normalization`, `coefficient_square`, `module_unit`, `derived_normalization`, `alpha_normalization`; no inverse-image coefficient-map isomorphism is assumed |
| Theta=t inverse s, and D | Exactly `rationalBalancedTheta` and extension along exactly `rationalBalancedCoefficient` |
| Actual beta-hat | `rationalMixedBetaComponent` applies the recorded `rationalScalarStrictBeta`, then ObjectProperty.isoMk, Q.mapIso, and only the recorded raw_objects transports |
| Additional maps/fields for compositions | Third scheme Z has the same three hypotheses; G,H are finite Padic extensions with algebra embeddings j,k; repeated fields and identity embeddings are allowed |

### Every conclusion clause

1. The displayed equation is the `compatibility` field in
   `RationalScalarMixedUnitCancellation`. Written in Lean composition order it is
   theta_X at aE.rawPull K, then D_X(alpha_E), then zeta; on the right it is
   J_F(beta), then alpha_F at T_Y K, then H_F(theta_Y). The structure's existence
   is the primary theorem. Its coefficient_square uses the actual finite-field
   scalar maps and the supplied geometric coefficient maps.
2. The endpoints are fixed by these functor types: source J_F T_X P-hat_E and
   target H_F D_Y J_E. `rationalMixedBetaComponent` gives the actual beta on every
   raw object with all object transports visible. This is not the parent's
   comparison built from `pbcActualCompletedPullback_tower.exists.choose`.
3. `rationalMixedUnitPrecomposition` is exactly J_F Q_F(C_X gamma_E), transported
   to the supplied raw pullback object's equality. The theorem
   `rationalMixedUnitPrecomposition_eq` states IsIso of that arrow and BOTH
   precomposition equations, with common value `rationalMixedOrdinaryPath`.
4. `rationalMixedTargetFlatten` composes the target's object equality, inverse
   zeta, inverse ordinary alpha, and rationalBalancedT. `rationalMixedCommonTensor`
   states that EACH precomposed route, followed by this specified flattening, is
   exactly the object transport followed by rationalBalancedS on ordinary pullback.
   The target is F_X tensor over B_E,X of P_E K, canonically the node's
   F_X tensor over g-inverse B_E,Y of g-inverse K.
5. The structure's `ordinary_units` fixes the tensor-unit generators of ordinary
   zeta inverse; `ambient_normalization` fixes its derived descent by the ordinary
   cochain map and actual computation counits. `rationalMixedOrdinarySections`
   states the all-scalar formula c tensor b tensor p maps to c*i(b) tensor p on
   pulled-back charts. Specializing b through integral inclusion gives the node's
   b' in B_E,X. The two rationalBalancedS/T tensor models are exactly the recorded
   balanced-localization tensor models, including restriction naturality. These
   are sheaf morphisms/natural transformations, so restriction compatibility is
   present in their types, not an unquantified pointwise-only assertion.
6. `rationalMixedRawNaturality` states naturality of BOTH routes for arbitrary
   raw arrows f. This includes all fraction arrows and Hom torsion. beta is a
   natural isomorphism and beta_normalization fixes all components, so no merely
   integral naturality or Karoubi completion is substituted.
7. `rationalMixedGeometricComposition` is the ambient zeta pasting equation;
   `rationalMixedRawGeometricComposition` is its specified raw beta equation.
   The geometric comparison helpers extract witnesses from the FULL
   `HasRationalPullbackCompositionCoherence`, with the ordinary generator formula,
   canonical inverse-image compositor, derived normalization, completed-unit
   equation, raw normalization and alpha equation all retained in its theorem.
   They do not choose from an unnormalized Nonempty endpoint-isomorphism theorem.
   That dependency's generator formula is precisely c''*c_h(c') after the canonical
   site compositor. Combining its alpha equations with compatibility for each cell
   gives geometric pasting of the displayed mixed realization equation.
8. `rationalMixedGeometricIdentity` states both ambient and raw identity equations,
   using the corresponding fully normalized identity dependency. Its ordinary
   formula is multiplication after the canonical first projection of the identity
   fiber product. Identity geometric maps are expressly included.
9. `rationalMixedCoefficientTower` states zeta's pasting under the actual balanced
   derived scalar associators. `rationalMixedRawCoefficientTower` states beta's
   pasting under exactly `pbcRationalScalarComp`. Combined with compatibility in
   each cell and the already recorded `rationalBalancedTower`, these are the mixed
   coefficient/realization pasting equations, with no fresh theta.
10. `rationalMixedPentagon` equates the two canonical three-factor derived
    flattenings followed by the SAME zeta for E to H. Its coefficient maps and
    comparison proofs are the actual rationalBalancedCoefficient_comp. The owning
    dependency's `rationalBalancedPentagon` supplies theta's raw pentagon for those
    same comparisons, so the mixed faces use the product nml independently of
    parentheses. The geometric and coefficient pasting equations state either
    order of mixed pasting; no unrelated endpoint isomorphisms enter.
11. `rationalMixedCoefficientIdentity` states zeta and beta's identity-field equations
    using the owning node's multiplication-normalized derived unitor and the actual
    `pbcRationalScalarUnit`. `rationalBalancedNormalizedIdentity` and
    `rationalBalancedNormalizedTower` of the owning dependency give their published
    conjugation to the literally identity stage functor, including equal fields.
12. The precomposition/common-tensor statements, actual strict beta component,
    alpha_normalization in the supplied pullback records, and all the pasting
    equations express cancellation of these very completion units. Each theorem
    docstring includes the natural-language proof, including reflected-unit
    substitution, adjacent pair cancellation, scalar insertion, associative
    multiplication and descent to fractions. Every theorem proof is exactly sorry;
    all helper definitions contain actual data or extraction from a characterization
    that determines its canonical map. No extra geometric/coefficient flatness or
    invertibility hypothesis is introduced.

### Dependency declarations read and used

Full signatures and docstrings were read in the current source. All Scheme names
below are in AlgebraicGeometry.Scheme.

| Dependency module | Declarations used |
| --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses | SheafOfModules.cochainModulesMonoidal and the inherited sheaf tensor |
| Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory, HasDerivedCategory, DerivedCategory.Q |
| Sheaf.NumberTheory.Padics.CoefficientExtensionFinite | Padic.finite_coefficientExtensionRing and its publicly imported valuation-ring/uniformizer constructions |
| Sheaf.Paper.AdicCoefficientDatum | completedReductionTower, pbcAdicCompletion and quotient-normalized coefficient data |
| Sheaf.Paper.IntegralUniformCoefficient | pbcBoundedConstructibleComplete and the underlying PbcBoundedConstructibleComplete three-condition full subcategory |
| Sheaf.Paper.PbcQbarCompletedPullback | pbcQbarCompletedPull and its public strict-tower pullback/unit construction; the actual finite-field functors remain pbcActualStrictCompletedPull and its unit |
| Mathlib.AlgebraicGeometry.Sites.Proetale | Scheme.ProEt, ProEt.topology |
| Sheaf.Paper.PbcRationalCategory | PbcRationalDerivedCategory, PbcRationalCategory, pbcRationalization |
| Sheaf.CategoryTheory.RingedSiteModules | CategoryTheory.ringedSiteModules / the same Mathlib SheafOfModules category |
| Sheaf.Paper.RationalModuleRealizationFunctor | RationalModuleRealization, rationalModuleRealizationFunctor |
| Sheaf.Paper.RationalRealizationPullbackComparison | RationalRealizationPullbackComparison, rationalRealizationPullbackComparison, rationalPullDerived, rationalPullComplexCounit |
| Sheaf.Paper.RationalScalarBalancedLocalization | rationalBalancedCoefficient, rationalBalancedTheta, rationalBalancedS/T, tensor/derived naturality, tower, identity and pentagon normalizations |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | rationalScalarStrictBeta, rationalScalarOrdinaryBeta, rationalScalarCompletionUnitSquare and actual-unit/pasting laws |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | CategoryTheory.existsUnique_localizationInverseImage and its unit-preserving inverse-image localization normalization |
| Sheaf.Paper.PbcScalarExtension | pbcCoherentScalarExtension, pbcEmbeddingIntegralTensor, pbcEmbeddingAmbientTensor, pbcRationalScalarExtension, pbcRationalScalarComp, pbcRationalScalarUnit |
| Sheaf.Paper.RationalPullbackCompositionCoherence | rationalPullbackCompositionCoherence, rationalPullbackIdentityCoherence and the FULL Has predicates; rationalCoherenceUnit |

Statement interfaces are public imports, directly or reexported by the owning
public imports. Plain proof imports also include LocalizedOrdinaryPullbackNormalization,
QuotientCompletedCompositorUnit, RingedDerivedMonoidalComparisons,
RingedTopoiCanonicalTensorPullbackOfUniverses and ReflectedAdjunctionCoefficientSquares,
matching all remaining recorded proof dependencies. No parent proof import cycle.

### Edge cases and source

Read Bhatt--Scholze Remark 6.8.15 in the actual PDF (printed p.62): the pullback is
naive inverse image followed by tensor over the pulled coefficient ring. The further
completion-unit calculation is the DAG's explicit expansion of the parent argument.
Also read the latest blueprint smooth-pullback-t-exact proof, whose first paragraph
is the root purpose of this realization input. No source correction is needed.

Checked zero objects, empty schemes and empty charts: no point, section or nonempty
hypothesis is inserted. All categorical/sheaf equations still have their meaning
there. Checked n=0 fraction denominators, torsion integral Hom groups, arbitrary
ramification and repeated coefficient fields: no cancellation of an integral scalar
and no unramified assumption. Identity maps, equal fields, binary geometric
composition, two coefficient extensions and the four-field pentagon are explicitly
stated, with the same normalized comparisons. No boundedness is imposed on ambient
complexes or resolving models beyond the source's constructible input. The small
site and coefficient universes stay u+1/u/u+1.

### Searches

Repeated the prescribed msearch searches on this repair:

- leanfinder: "Rational realization mixed scalar geometric pullback square commutes
  after cancelling actual completion units"; eight ordinary Proj/pullback hits, no
  matching completion-unit rational-realization theorem.
- loogle: "SheafOfModules.pullback_assoc, pbcActualScalarOrdinaryPullIso"; zero hits,
  and the service does not recognize the project-only second name.
- Mathlib grep: "mixed.*(scalar|unit)|rationalScalarMixed|completion.*unit.*cancell";
  three unrelated hits in number-field mixed embeddings and tensor spans.
- rg in lean/WeilConjectures and lean/Sheaf with the same expression: ordinary
  mixed-tensor results and the returned parent module. Read its full signatures:
  they use the alternate scalar records and strict comparison, which the return
  correctly identifies as insufficient for this item's specified comparisons.
- Item-id search in lean/WeilConjectures: no occurrence. No matching new declaration
  name is present in upstream or Mathlib. The helper declarations belong solely to
  this item's normalization and equations, rather than a new independent notion.

No STATEMENT-DISPUTED issue remains or is introduced.

## Second reading by NI

This is the dispatcher's single worker's second reading, not a claim of a second
agent. The prompt prohibits starting agents; the maintainer supplies independent review.

Reopened the node and complete new module. Traced every scalar map to
rationalBalancedCoefficient and every theta to rationalBalancedTheta. Traced
rationalMixedBetaComponent through ObjectProperty.isoMk and Q.mapIso directly to
rationalScalarStrictBeta, with raw_objects supplying exactly the endpoint transports.
Checked the written equation's composition order against the TeX: theta, D alpha,
zeta equals J beta-hat, alpha, H theta. Checked the source of unit precomposition
and the single-tensor target. Added rationalMixedCommonTensor in this pass so the
precomposition clause identifies an actual common flattened map, not just another
equality of endpoints. Added explicit arbitrary-raw naturality and equal-coefficient
identity in this pass; both compiled cleanly.

Checked both geometric and scalar identity clauses, both raw composition/tower
clauses, and the mixed pentagon; none uses bX/bY or an unrelated zeta. The helpers
for geometric composition and identity extract from FULL normalized existential
statements, not from bare existence of endpoint isomorphisms. Their source
characterizations determine their tensor maps and thus their derived/raw maps.
The ownership list contains only the new module's top-level declarations. The old
parent module is absent from the imports. No existing:true parent attachment remains.

Validation: scompile.py compiled the final module separately in sandbox and module
path mode with no errors or warnings (16.6 s / 15.9 s). Default 60-second limits;
no lake/global build, live-source edit or direct Git command. The prescribed dry-run
and final delivery are the remaining validation steps and will be reported below.

Dry run result: deliver2.py --no-push printed
`OK (dry run): commit 971dd179d6b passes the preflight and compiles; nothing pushed`.
The exact staged paths were the new module, the item's node record, and this report.
The final delivery repeats these required checks before pushing.
