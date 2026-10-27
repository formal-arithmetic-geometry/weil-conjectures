## Worker report

The module `Sheaf.Paper.FdShiftTriangleReflection` states the requested result as
`WeilConjectures.fdShiftTriangleReflection` and the explicit cone clause as
`WeilConjectures.fdCommonStageConeIdentification`. Both proofs are `sorry`.
The canonical scalar-shift helper and the two unit isomorphism helpers have actual data: the existing tensor unit,
transported along the recorded stage-system equality, and the equality isomorphism
of the PBC identity transition. `fdPbcScalarShift` is the existing scalar shift
comparison applied to its explicitly named stage object. No new category, arbitrary comparison, Karoubi
completion, or object selected from a mere existence statement is introduced.

Hypotheses and clauses, in the order of the node:

- `_D : FiniteFieldDatum.{d}` and `_hl : l ≠ _D.p` retain the global datum and
  characteristic convention. `l`, `Fact l.Prime`, `Ω`, its field and Padic algebra,
  and `IsAlgClosure` bind precisely the coefficient data.
- `W : Scheme.{u}`, `IsNoetherian W`, `dW` and `iW` give an arbitrary allowed
  scheme, finite dimension and invertibility on every stalk. Since the assertion
  is pointwise in W, universal W is equivalent to its application at every member
  of the given scheme family; no cross-scheme data are used in this lemma.
  Universes d, u and w are independent, and all pair-category objects live in the
  common resulting larger universe.
- The source is exactly `GeneralAlgebraicallyClosedCoefficients.stageSystem`,
  with `sfRationalConstructibleCategory` stages. The target is exactly
  `pbcScalarSystem`, with `pbcStageCategory` raw PBC rational stages. These are
  existing published constructions; their owning modules are identified below.
- `J : StageSystem.Morphism` contains the finite functors and beta = inverse j,
  together with exactly the scalar cocycle involving the two actual associators.
  Its `functor` has the literal pair object formula and conjugation map formula
  by the existing `Morphism.functor`/`mapAt` definitions. The instances on `J.Φ E`
  specify integer shifts, additivity, equivalence, E-linearity and exactness.
- `hunit` is the identity normalization, expressed with the canonical unit
  isomorphisms since the framework identity transition is not definitionally the
  identity functor. `hshift` is compatibility of the actual beta with shifts.
  `J.functor.Additive` and `hhom` retain exactly the assumed additive functor and
  bijective induced Hom maps. No scalar-transition faithfulness is assumed.
- The existential `s : J.functor.CommShift ℤ` gives a natural isomorphism for
  every integer shift, with zero/addition coherence. Its hom and inverse at each
  literal pair are specified by `HEq` with inclusion of the prescribed finite
  comparison and its inverse, for every E, n and K; n = 1 gives the stated
  one-shift assertion. HEq accounts only for the existing shifted-pair object
  equality; no finite-stage restriction is weakened to an unrelated isomorphism.
- The equality of inclusion/functor composites gives the specified finite-stage
  restriction, on objects and arrows. `J.functor.IsTriangulated` is forward
  preservation; the following `↔` is preservation and reflection of distinguished
  triangles with that same descended shift structure.
- The finite-model clause quantifies over every D with distinguished image. It
  supplies M, a distinguished `A : Triangle (pbcStageCategory ... M)`, R and an
  adjunction with invertible unit and counit (an exact quasi-inverse), plus its
  compatible integer shifts. `R.IsTriangulated` is the asserted finite exactness.
  Alpha and beta are actual triangle isomorphisms with the exact endpoints in the
  node. The third isomorphism e has all three components explicitly equal to the
  included finite counit. The triangle-category equality
  `J.functor.mapTriangle.map β.hom ≫ e.hom = α.hom` is precisely the required
  compatibility of the reflected isomorphism with the first isomorphism.
- The final universal R/adj/r clause covers every quasi-inverse with the induced
  shifts, encoded equivalently by shift compatibility of its equivalence
  adjunction and invertible unit/counit, and asserts its exactness.
- `fdCommonStageConeIdentification` quantifies over every actual target common
  stage cone and distinguished finite cone. Its isomorphism has first two
  components `isoToStage`, third component identity, and explicitly records the
  representative identity classes at the endpoints. Since repeated-field
  transitions are propositionally, rather than definitionally, the identity,
  `fdPbcStageUnit.inv.app` is the necessary identity transport in those classes.
  Its last HEq is the required third arrow: the identity transition transport,
  followed by p_u (`h`), followed by the inverse actual scalar-shift comparison.
  All three triangle squares are part of the triangle isomorphism type.

Dependencies read and used (module / declaration):

- `Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi` /
  `WeilConjectures.sfRationalConstructibleCategory` and its canonical structures.
- `Sheaf.Paper.PbcRationalCategory` /
  `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`, `PbcRationalCategory`.
- `Sheaf.Paper.SfScalarExtensionComposition` /
  `WeilConjectures.sfRationalScalarComp`, `sfRationalScalarUnit`.
- `Sheaf.Paper.PbcScalarExtension` /
  `AlgebraicGeometry.Scheme.pbcCoherentScalarExtension`; the actual normalized
  `pbcScalarSystem` interface is reexported by the recorded PBC pair modules.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` /
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`, its `Stage`,
  `stageSystem`, `inclusion`, `unitor`, and canonical shifts/triangles.
- `Sheaf.Paper.PbcQbarCategory` / `AlgebraicGeometry.Scheme.pbcQbarCategory`,
  `pbcQbarLinear`, `pbcQbarTriangulated`. The landed dependency record remains
  attached to `IntrinsicQbarCategory` with all eight recorded declarations.
- `Sheaf.Paper.IntrinsicQbarCategory` /
  `WeilConjectures.intrinsicQbarStageLinear` for the source's existing E-action.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` /
  `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization` supplies
  the allowed-scheme convention; the integral characterization itself is not
  an additional assumption on objects.
- `Sheaf.Paper.PbcCommonStageCones` /
  `AlgebraicGeometry.Scheme.pbcCommonStageDistinguished` and
  `CategoryTheory.StageSystem.commonStageCone`.
- `Sheaf.Paper.CommonStageCalculus` /
  `AlgebraicGeometry.Scheme.commonStageCalculus`, the actual pair/inclusion
  shifts and scalar-shift comparisons.
- `Sheaf.Paper.FiniteStagePairCategory` /
  `AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory`, `pbcScalarSystem`,
  `pbcScalarSystem_units` and `pbcStageCategory`.
- Mathlib `CategoryTheory.Triangulated.Pretriangulated` / `Pretriangulated`;
  `CategoryTheory.Triangulated.Basic` / `Triangle`, `TriangleMorphism`;
  `CategoryTheory.Triangulated.Adjunction` / `Equivalence.IsTriangulated.mk'`.
  Upstream `WeilConjectures.CategoryTheory.StageSystem.Functor` supplies
  `StageSystem.Morphism`, `mapAt`, `functor` and `ιCompFunctorIso`.

Edge cases checked: repeated coefficient fields E = F = M; different endpoint
fields; zero representative and zero cone arrows; the empty scheme; n = 0,
n = 1 and negative integer shifts; unrelated scheme and closure universes.
The repeated-stage unit transports are written explicitly instead of assuming
that the library's identity transition reduces definitionally. Bijectivity is
an assumption of the pair Hom maps, independent of transition faithfulness.
No statement correction or STATEMENT-DISPUTED issue was needed.

Searches: prescribed msearch leanfinder query about coherent finite exact
comparisons, descended shifts and finite reflected models returned eight generic
triangulated-functor/equivalence lemmas, including `map_distinguished_iff` and
`Equivalence.IsTriangulated.mk'`. Loogle query
`CategoryTheory.Functor.distTriang_iff, CategoryTheory.Equivalence.IsTriangulated`
returned no combined match. Mathlib grep query
`commonStageCone|mapTriangle.*essImage|distTriang_iff` in
`CategoryTheory/Triangulated` returned three generic matches. LeanSearch query
about coherent exact finite stage equivalences and finite triangle models
returned eight generic exactness/equivalence results. None gives the prescribed
shift components, counit-compatible finite model and endpoint representatives.
Direct rg searches in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
`fdShiftTriangleReflection`, and `shiftTriangleReflection` found no existing
statement. Concept searches found `FdCommonStageComparisonDescent`, which does
not state the finite reflected model, counit equation or explicit cone identities;
its proof sketch uses this node's argument, so it is not a substitute dependency.

## Dependency records retained

H13 repair: restored the sandbox copy of
`def-weil-pbc-qbar-category.json` byte-for-byte from the current shared
`sheaf-dag` checkout. Its `lean` remains the maintainer-reviewed NM record for
`Sheaf.Paper.IntrinsicQbarCategory` / `WeilConjectures.intrinsicPbcQbarCategory`,
including all eight declarations and the landed linear instances. The record's
stage-3 proof and review fields are retained too. The proposed `existing: true`
replacement is withdrawn. This delivery supplies no dependency module or
replacement dependency record. The item already imports both
`IntrinsicQbarCategory` and `PbcQbarCategory`, and uses the published
`AlgebraicGeometry.Scheme.pbcQbarCategory` directly as the comparison target;
its accepted Lean source needs no change.

The advisory ownership point is also recorded: `pbcScalarSystem` and
`pbcStageCategory` belong to `def-weil-pbc-finite-stage-pair-category`, in
`Sheaf.Paper.FiniteStagePairCategory`. That node is an existing proof dependency
of this item, and its module is imported explicitly. Neither declaration is
attributed to `def-weil-pbc-qbar-category`; no ownership record is rewritten.

## Second reading by Q102

Reopened the current node's full `statement` and seven proof steps, the delivered
`FdShiftTriangleReflection.lean`, the stage-morphism implementation, the actual
PBC stage/category definitions, and the landed intrinsic-category record. This
reading follows the node in order. It is performed by the dispatched worker;
independent delivery review remains with the maintainer, as the brief requires
and its prohibition on starting other agents specifies.

| Node hypothesis or clause | Lean counterpart and reading finding |
| --- | --- |
| Global finite-field datum, prime ell distinct from p, and algebraic closure Omega/Q_ell | `_D : FiniteFieldDatum.{d}`, `_hl : l ≠ _D.p`, `l : ℕ`, `[Fact l.Prime]`, and `Ω : Type w` with `Field`, `Algebra ℚ_[l] Ω`, `IsAlgClosure ℚ_[l] Ω` retain each piece of context. No coefficient characteristic or closure choice is silently fixed. |
| Allowed T and each allowed W | The section's arbitrary `W : Scheme.{u}`, `[IsNoetherian W]`, `dW : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)`, and `iW : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))` are exactly the allowed-scheme conditions. T has no separate role in this pointwise assertion; instantiating W gives T as well. There is no compatibility across schemes to encode here. |
| Actual framework and PBC finite raw rational stages | The source of `J` is `GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W`; its `Stage` is the existing framework rationalization. The target is the published `pbcScalarSystem l Ω W dW.out iW.out`, whose stages are `pbcStageCategory l Ω W E`. The latter abbreviates the existing PBC raw scalar localization. Neither side uses a Karoubi envelope. |
| Exact E-linear equivalences J_(W,E), with the specified finite shifts | `J.Φ E` is a functor with the five explicit families of instances `CommShift ℤ`, `Additive`, `IsEquivalence`, `Linear E.val`, and `IsTriangulated`. These encode the specified finite exact functor, its integer-shift comparisons, equivalence and E-linearity, without requiring a strict inverse functor. |
| Natural scalar comparisons j on the actual transitions | `J : StageSystem.Morphism ... ...` contains natural isomorphisms `J.β h : J.Φ E ⋙ P h ≅ S h ⋙ J.Φ L`. Thus beta is the inverse of the node's j, with the same source and target after inversion. Reading `Morphism.coh` verifies the scalar cocycle uses the actual source and target associators, rather than strict transition composition. |
| Identity normalization | `hunit` equates `(J.β (le_refl E)).hom.app K ≫ (J.Φ E).map ((fdFrameworkStageUnit ... E).hom.app K)` with `(fdPbcStageUnit ... E).hom.app ((J.Φ E).obj K)`. These are the canonical tensor-unit/equality transports. They express j_(E/E) = identity in the normalized identifications even when those transitions do not reduce definitionally. |
| Exactness/shift compatibility of the natural scalar comparisons | `hshift` requires `NatTrans.CommShift (J.β h).hom ℤ` for every field inclusion. Since beta is an isomorphism, this is equivalently compatibility of j and its inverse with the specified shift comparisons. |
| Additive pair functor with prescribed object and representative formulas | The statement uses the existing `J.functor` and `[J.functor.Additive]`. Reading `Morphism.functor` gives `(E,K) ↦ (E,J.Φ E K)` literally; reading `mapAt` gives `beta_X ≫ J_M.map u ≫ beta_Y⁻¹`, hence `j_Y J_M(u) j_X⁻¹` in the node's composition convention. An arbitrary descended functor is not substituted. |
| Bijective induced Hom maps | `hhom : ∀ X Y, Function.Bijective (J.functor.map : (X ⟶ Y) → _)` quantifies over every pair of source objects. It retains both fullness and faithfulness and adds no scalar-transition faithfulness assumption. |
| Natural descended [1] comparison and inverse | `∃ s : J.functor.CommShift ℤ` supplies a natural isomorphism, and the first conjunct pins both its hom and inverse at every literal pair `⟨E,K⟩` to the inclusion of the corresponding finite comparison. The two `HEq` clauses account for the existing object transports; they specify actual arrows and do not merely require some isomorphism. Taking `n = 1` gives exactly the two displayed classes in the node. |
| Integer comparisons and coherence | The same first conjunct ranges over `n : ℤ`; zero, addition and inverse-shift coherence are in the `CommShift ℤ` structure. It therefore includes zero and negative shifts as well as the one-shift assertion. |
| Restriction along the finite-stage inclusions | The next conjunct states `(source.ι E) ⋙ J.functor = J.Φ E ⋙ (target.ι E)` for every E. Together with the preceding component equalities it is the prescribed finite restriction on objects, arrows and shift comparison. |
| Forward preservation of distinguished triangles | `J.functor.IsTriangulated` uses the very descended shift instance s installed by the surrounding explicitly bound instance lambda. It says every distinguished source triangle has distinguished image with that comparison on the last arrow. |
| Distinguished image has a finite distinguished target model | The next existential clause starts with arbitrary `D` and distinguished `J.functor.mapTriangle.obj D`, and supplies `M`, `A : Triangle (pbcStageCategory ... M)`, and `A ∈ distTriang ...`. Alpha has exactly the endpoint `J D ≅ ι_M^p A`. No common field is fixed in advance. |
| An exact finite quasi-inverse | The same clause supplies `R`, `adj : J.Φ M ⊣ R`, `r : R.CommShift ℤ`, `adj.CommShift ℤ`, invertibility of unit and counit, and `R.IsTriangulated`. The invertible adjunction is an equivalence quasi-inverse, and its compatibility makes r the induced inverse shift comparison. |
| Reflected finite model in the source | Beta has exactly type `D ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion ... M).mapTriangle.obj (R.mapTriangle.obj A)`. Thus the model is the included R_M A for the same M and A, rather than an unrelated distinguished triangle. |
| Counit triangle isomorphism and compatibility with alpha | The existential e goes from the image of that source model to `ι_M^p A`; all three `HEq e.hom.homᵢ` clauses pin its components to the included finite counit. The final equation `J.functor.mapTriangle.map β.hom ≫ e.hom = α.hom` is precisely `e ∘ J(beta) = alpha`. Inverting e recovers the equivalent composite description of the image of beta. |
| Every common-stage cone is the inclusion of its finite cone | `fdCommonStageConeIdentification` takes arbitrary X, Y, M, hX, hY, Z, f, g, h and distinguished `Triangle.mk f g h`, and supplies an isomorphism from the actual `StageSystem.commonStageCone` to its finite inclusion. Triangle-isomorphism typing includes all three squares, including the last shift square. |
| Endpoint identity classes and cone-object identity | That companion pins the first two components to `isoToStage X hX` and `isoToStage Y hY`, and the third to `𝟙 _`. Its next two `HEq` clauses expand the endpoint classes as `mkHom` with `fdPbcStageUnit.inv.app`, the identity class after the necessary repeated-stage transport. They are not arbitrary endpoint isomorphisms. |
| Connecting arrow with the inverse actual scalar-shift | The companion's final `HEq` expands `commonStageCone.mor₃` as `mkHom` of `fdPbcStageUnit.hom.app Z ≫ h ≫ (fdPbcScalarShift ... X.obj).inv`. The order is p_u followed by inverse sigma in Lean's left-to-right composition; the first factor is only the identity-transition transport. The sigma is the existing `pbcScalarExtension.commShiftIso 1` at X.obj. |
| Preservation and reflection | The explicit `∀ D, J.functor.mapTriangle.obj D ∈ distTriang ... ↔ D ∈ distTriang ...` gives both directions for all source triangles with s. It accompanies, rather than replaces, the more detailed finite-model and counit clauses. |
| Every quasi-inverse with induced shifts is exact | The final universal clause ranges over every `R : pbcQbarCategory ... ⥤ generalAlgebraicallyClosedConstructibleCategory ...`, adjunction and integer shift structure, assumes `adj.CommShift ℤ` and invertible unit/counit, and concludes `R.IsTriangulated`. This is exactly the node's restriction to the inverse shift comparison induced by the equivalence. |
| Literal pair categories in one sufficiently large universe | Source and target remain their published pair carriers throughout. Explicit universes `d u w` keep finite-field datum, scheme and coefficient closure independent; no equality between them is imposed. |

The three helper definitions also have actual data on rereading:
`fdFrameworkStageUnit` composes `eqToIso` of the existing uniquely specified
stage-system transition equality with the existing tensor unitor;
`fdPbcStageUnit` is `eqToIso` of the published identity-transition equality;
`fdPbcScalarShift` is the existing finite scalar functor's comparison component.
No data is supplied by a new uncharacterized existence assertion. Both postponed
theorems have the matching node tag and a full natural-language proof docstring.

Checked the degenerate cases against those binders and formulas: E = F = M uses
the explicitly written unit transports; zero arrows and a zero cone have no
nonzero restriction; empty W remains allowed; the shift clauses include n = 0
and n < 0; no relation between d, u and w is assumed. The common-stage clause
allows different endpoint stages, and hhom still ranges over all source pairs.

Findings and changes: the mathematical clauses match and the accepted Lean
module is retained unchanged. H13 was the stale replacement of the landed
intrinsic-category record, not a defect in this item's target type; restored
that whole JSON file byte-for-byte. H11 was the old short reading paragraph,
which did not map the hypotheses and clauses; replaced it with this complete
reading. Removed the report's claim that a dependency rebind is needed and
corrected the ownership description of the PBC scalar/stage constructions.
No new node or statement correction is introduced.

Validation: the initial saved-packet dry run passed preflight and all per-file
compiles (`52e4c0bfbcb`, not pushed). The repaired packet is compiled and dry-run
again before delivery. `autoImplicit` and `relaxedAutoImplicit` are false; no
Lean declaration or signature was changed for this repair.
