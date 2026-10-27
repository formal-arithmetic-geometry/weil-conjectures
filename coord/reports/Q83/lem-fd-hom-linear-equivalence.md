## Worker report

The delivery states `WeilConjectures.fdHomLinearEquivalence` in
`Sheaf.Paper.FdHomLinearEquivalence`. The auxiliary proposition
`FdHomLinearEquivalence` packages the complete conclusion; it introduces no new
carrier, scalar action, stage system, quotient, or completion. Its definition is
written in full. The sole postponed theorem is `fdHomLinearEquivalence`, with the
node's eleven-step proof in its docstring. No statement correction is needed.

Hypotheses and their Lean counterparts:

- The global finite-field datum is `_D : FiniteFieldDatum.{d}`. The prime is
  `l : ℕ` with `[Fact l.Prime]`, and `_hl : l ≠ _D.p` excludes the characteristic.
- The fixed algebraic closure is `Ω : Type w`, `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`.
- The arbitrary allowed scheme is `T : Scheme.{u}`, `[IsNoetherian T]`,
  `dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)` and
  `iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))`.
  This is pointwise in arbitrary T: the input family for every allowed W can
  be specialized to T, and the conclusion applies to every such specialization.
  No scheme map to the global finite field or finite-type condition is imposed.
- The actual framework and PBC raw stages and transitions are
  `GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T` and
  `pbcScalarSystem l Ω T dT.out iT.out`.
- `J : StageSystem.Morphism` supplies the finite functors `J.Φ E` and comparisons
  `J.β h`; beta is inverse j. `J.coh` is precisely the displayed cocycle in this
  inverse orientation, including both actual associators.
- `[∀ E, (J.Φ E).IsEquivalence]`, `_hadd`, `_hlinear`, the finite `CommShift`
  instances and `_hexact` give the exact E-linear finite equivalences. `_hshift`
  supplies scalar-comparison compatibility with shifts. Inverting the natural
  isomorphism exchanges beta and j without changing that condition.
- `_hunit` identifies beta at E/E with J applied to the inverse framework unitor;
  the PBC repeated-field transition is literally identity. It expresses exactly
  identity normalization, with HEq handling the published framework unitor's
  transition presentation.
- Universes d, u and w are explicitly declared and independent. All other
  variables are explicitly bound, with both automatic implicit options disabled.

Conclusion clauses, in the order of the definition:

- `stage` is the additive stage-Hom bijection. Its first equation is
  `stage ... f = J.mapAt f`. Unfolding `mapAt` gives beta_source, J_M(f),
  inverse beta_target, i.e. j_target J_M(f) inverse j_source in the source's
  right-to-left composition convention.
- The inverse equation is exactly `J_M.preimage` after conjugation by inverse
  beta_source and beta_target. This is the displayed psi, using the fully
  faithful Hom inverse supplied by the assumed finite equivalence.
- The following two equations state phi and psi commute with actual `S.tr` and
  `P.tr`, at every M ≤ N, retaining both associators. No transition is assumed
  faithful or injective.
- `hom` is an Omega-linear equivalence of the existing quotient Homs, hence
  both forward and inverse maps are additive bijections and Omega-linear.
  Its forward map equals `J.functor.map`; both representative equations are
  stated with `StageSystem.PairCategory.mkHom`, not a replacement colimit.
- The additive and linear clauses give the asserted functor properties; the object
  equation is the literal pair `(E, J_E K)`.
- Stage essential surjectivity supplies K and an isomorphism at the original
  target field E. For every choice K(A), epsilon(A), the next clause supplies
  an equivalence with this forward functor and an inverse retaining A.stage.
  The inverse arrow formula is the inverse Hom equivalence applied to
  epsilon_A followed by f followed by inverse epsilon_B. The counit is the
  finite-stage inclusion of epsilon_A. Consequently these chosen stage
  isomorphisms give the required isomorphisms of pair objects. An equivalence
  includes the unit, counit and triangle law, so this is a quasi-inverse rather
  than just an abstract essential-surjectivity assertion. Both functors are
  additive and Omega-linear.
- The final object and arrow equations give the identity-normalized finite-stage
  inclusion equality literally at both levels.
- Omega scalars are the existing `intrinsicQbarLinear` on the framework side and
  `pbcQbarLinear` on the PBC side. Their definitions multiply a representative
  at a finite compositum containing the scalar. Thus the linear-equivalence
  clause uses precisely the scalar action prescribed in the node, including
  scalars outside the representative's original field.
- No idempotents are adjoined: both carriers are the recorded literal pairs.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, including all its fields.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalScalarExtension`, and the canonical localization coefficient
  identification; framework Stage specializes these declarations.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory` and its raw
  localization `PbcRationalCategory`; `pbcStageCategory` is their small-model
  specialization.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp` and
  `sfRationalScalarUnit`, including the localized integral-component specification.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and the recorded
  scalar comparison machinery. The pair system's transitions and associators
  are the ones already specialized in `FiniteStagePairCategory`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`,
  `unitor`, `generalAlgebraicallyClosedConstructibleCategory`; their docstrings
  and system uniqueness specification identify the actual framework transitions.
- `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicQbarStageLinear`,
  `intrinsicQbarLinear`, and the reexported `pbcQbarCategory` / `pbcQbarLinear`.
  Careful reading matters: its primary `intrinsicPbcQbarCategory` aliases the
  framework carrier, while the PBC carrier is the reexported existing
  `AlgebraicGeometry.Scheme.pbcQbarCategory`. The statement uses the latter,
  preserving the two actual systems rather than silently identifying them.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, whose source hypotheses explain
  the allowed-scheme convention. Here no criterion is asserted again.
- Proof imports: `Sheaf.Paper.FiniteStagePairCategory` (`PbcFiniteStagePairCategory`,
  `pbcScalarSystem`) and `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
  (`FiniteCoefficientFields`, finite composita and their properties).
- Upstream `WeilConjectures.CategoryTheory.StageSystem.Functor`: `Morphism`,
  `mapAt`, `functor`, `functor_map_mkHom`, `functor_map_ι`, `ιCompFunctorIso`;
  Mathlib `Functor.preimage` and linear functor / linear equivalence notions.

Edge cases checked before writing: equal or repeated coefficient fields use the
actual unit and associators; zero arrows and zero objects are covered by additive
bijections; the empty scheme is not excluded by any binder; no descent to a smaller
field is required for a target object; nonfaithful transition functors are allowed;
scalars need not belong to M; closure and scheme universes are independent; arbitrary
choices of stage object preimages are quantified, not a special choice.

Searches actually run through msearch.py:

- LeanFinder: "Coherent linear equivalences of finite coefficient categories induce
  equivalences on literal pair categories with common-stage Hom colimits". Eight
  hits, including `Linear.homCongr`, `Functor.linear_of_iso` and fixed-ring module
  equivalences. None states this two-system quotient result.
- Loogle: `CategoryTheory.Equivalence, CategoryTheory.Functor.Linear`. Two hits:
  `CategoryTheory.Equivalence.inverseLinear` and `MoritaEquivalence.mk`.
  They cover inverse linearity infrastructure, not the specified transport maps.
- LeanSearch: "Coherent equivalences of linear categories induce inverse linear maps
  on common stage Hom colimits and an equivalence of pair categories". Eight hits,
  including `Equivalence.inverseLinear`, `Linear.homCongr` and colimit equivalences.
  None covers the explicit varying-field pair-category statement.
- Mathlib grep through msearch: `StageSystem|PairCategory|common.stage` in
  CategoryTheory, zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for Hom linearity, stage comparisons,
  cocycles and pair equivalences found the existing stage-system functor and
  `FdCommonStageComparisonDescent`. Reading that module shows forward bijectivity
  and transport, but not all inverse representative formulas and arbitrary chosen
  quasi-inverse equations required here, so no exact existing match was recorded.
- rg of upstream sources for `lem-fd-hom-linear-equivalence` found no attachment.
  rg in Mathlib, upstream and Sheaf for the chosen new declaration names found none.

No STATEMENT-DISPUTED issue was found. Every node field except lean is preserved, also in the dependency repair.

## Second reading by Q83

The dispatcher prohibits starting another agent, so this is the assigned worker's
separate second reading; the maintainer supplies the independent delivery review.
I reread the node and the final module together. The checks above distinguish the
framework carrier from the PBC carrier, reverse j to the published beta consistently,
retain the actual quotient transport in both directions, and include the inverse
representative and arbitrary-object-preimage formulas absent from the older descent
lemma. Endpoint types of mkHom are written explicitly so that the forward and inverse
classes lie in the right pair categories. No finite-field label, scalar restriction,
extra scheme structure or faithful-transition hypothesis was introduced. The complete
conclusion is an existential proposition to avoid expensive generated dependent
structure eliminators; its clauses are unchanged. Compiler and delivery validation
are recorded below after they complete.

Validation: scompile.py passed both sandbox and library compilation with no
errors or warnings (67.2 seconds total sandbox orchestration, 40.9 seconds
library orchestration; each compiler invocation passed its 60-second limit).
The initial inference errors were corrected by explicit mkHom endpoints; the
large result structure was replaced by the equivalent explicit proposition.

## Dependency modules

No dependency module or dependency record is changed in the repaired delivery.
`def-weil-pbc-qbar-category` is retained byte-identically to the current live node,
including NM's `Sheaf.Paper.IntrinsicQbarCategory` record and all eight intrinsic
declarations. The saved sandbox copy now matches that live file exactly and is
therefore omitted from the delivery diff by the normal delivery wrapper.

## Maintainer note: the two coefficient carriers

The primary `WeilConjectures.intrinsicPbcQbarCategory` in the landed record aliases
`generalAlgebraicallyClosedConstructibleCategory`, the framework carrier. The PBC
raw-rational finite-stage pair category is the distinct existing declaration
`AlgebraicGeometry.Scheme.pbcQbarCategory`, defined in
`Sheaf.Paper.PbcQbarCategory` as
`PbcFiniteStagePairCategory l Ω T hDim.out hInv.out`. Its
`pbcQbarScalarAction`, `pbcQbarLinear` and `pbcQbarTriangulated` supply the prescribed
scalar action and common-stage triangulation. `Sheaf.Paper.IntrinsicQbarCategory`
already publicly imports that module. This item's module explicitly imports both
and uses the actual framework and PBC systems separately. It does not identify
the two carriers.

The dependency record continues to own **all eight** landed intrinsic declarations:
`intrinsicPbcQbarCategory`, `intrinsicQbarStageFieldEquiv`,
`intrinsicQbarStageLocalizedLinear`, `intrinsicQbarStageLinear`,
`intrinsicQbarScalarCompatible`, `intrinsicQbarScalarAction`,
`intrinsicQbarLinear_existsUnique`, and `intrinsicQbarLinear`, all in namespace
`WeilConjectures`. Their definitions and proofs, including the stage-3-proved
scalar compatibility and linear structure used by live consumers and this item,
are preserved.

## Repair of return 0574c0e64d9d

H13/H4: the returned packet discarded NM's eight intrinsic declarations when it
selected the PBC carrier. This repair uses the reviewer's expressly authorized
alternative: **keep the live record byte-identical and add a maintainer note**.
The note above explains the carrier distinction without rebinding any landed
record or withdrawing any live declaration. The item's explanatory `lean.note`
now describes this repair. The item module is unchanged, as the return explicitly
confirms its mathematical statement is correct.

Repair second reading by Q83: read both existing source modules; verified the
public reexport and actual carrier definitions; compared the restored dependency
file byte-for-byte with live; checked all eight intrinsic names remain owned.
The item changes only `lean`. Its theorem signature is verbatim, it contains one
expected postponed theorem, and no diagnostic commands or lines over 100 characters.
No carrier, scalar instance, proof, statement dependency or non-lean field changes.

Validation: the saved packet's initial dry run passed at 5d8417dbcc7. For this
repair, scompile.py passed sandbox mode (33.3 s) and library mode (47.5 s), with
no errors or unexpected warnings. An attempted superset record on
IntrinsicQbarCategory passed the declaration compile probe but was rejected by
preflight's textual check because pbcQbarCategory is publicly reexported rather
than directly declared in that source file. The final packet instead uses the
reviewer's byte-identical-record alternative above and is checked again by
normal deliver2.py before push.
