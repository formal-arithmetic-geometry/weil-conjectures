## Worker report

The module `Sheaf.Paper.ExceptionalCommonStageDescent` states
`WeilConjectures.ExceptionalCommonStage.exceptionalCommonStageDescent` with a single
`sorry`. Every other authored declaration is a data record, a proposition record,
or an explicit construction from existing data. No definition contains `sorry`.
The records only package this node's hypotheses and conclusion; they introduce no
replacement coefficient category, scalar extension, or independent notion.

Source read: main-20261015, `sec-smooth-purity/sk-prop-sf-localization/`
`prop-sf-localization-all-stages.proof.md`, the full proof, particularly the
algebraically closed-stage paragraph. I also read all nine accepted proof steps of
the assigned node, every statement dependency's statement and record, and the
recorded declarations and their source docstrings. The CompactObject example is
now a withdrawn empty module; its node records the upstream existing definition.
I followed the current module-mode convention in the standing brief instead.

Hypothesis-by-hypothesis correspondence:

- Prime ell: `{l : ℕ} [Fact l.Prime]`.
- Algebraic closure of Q_l: `{Ω : Type v} [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. The closure universe `v` is independent of `u`.
- Field k and ell invertible: `(k : Type u) [Field k] (hl : IsUnit (l : k))`.
- X separated of finite type over k: the structure morphism `s` to `Spec k`,
  `[IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]`. The last two
  are the standard finite-type decomposition, with no properness assumption.
- Complementary closed/open pair: `i`, `[IsClosedImmersion i]`, `j`,
  `[IsOpenImmersion j]`, and `hij : Set.range j.base = (Set.range i.base)ᶜ`.
  Z and U inherit their k-morphisms by composing with s; no descent of k to a
  finite field, dimension bound, or extra quasi-compactness hypothesis is imposed.
- Actual raw rational categories and specified scalar functors:
  `GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E` and
  `stageSystem l Ω T`. Stage unfolds to `sfRationalConstructibleCategory` on the
  existing canonically shrunken finite coefficient field. The system's T and
  associators are uniquely specified to be the actual completed-integral scalar
  extension followed by rationalization and its balanced tensor associator.
  `scalarUnit` composes the existing `operationStageTransitionIso` with the
  existing tensor unitor; it does not replace repeated-field extension by identity.
- Exact functors and the three specified adjunctions: `FiniteData` records
  `closedPull`, `closedPush`, `openPull`, `openPush`, `exceptional`, and `closedAdj`,
  `openAdj`, `exceptionalAdj`. The first four are existing `StageSystem.Morphism`
  records, so their invertible comparisons and actual scalar-associator equations
  are input data. `Hypotheses` has all five `IsTriangulated` conditions.
- Canonical geometric operations and coefficient normalization:
  `GeometricNormalization.closedPull/openPull` identify the left adjoints with
  the recorded `rationalDerivedPullback` along i and j. Its two comparison fields
  identify their coefficients with `commonStagePullbackComparison`, the existing
  rationalized integral tensor/pullback normalization. Invertibility in residue
  fields is quantified inside these normalization clauses, not assumed of the
  theorem: witnesses exist by mapping hl through the canonical k-to-residue maps.
  `Hypotheses.closedMate/openMate` require the two direct-image comparisons to
  be the actual right mates of the inverse pullback comparisons. Specifying the
  left adjoint and the given adjunction fixes its right adjoint by the unique
  adjunction-preserving identification with the derived direct image; this is
  not an arbitrary map or a Nonempty choice of an unnormalized isomorphism.
- Invertible closed/open counits: `Hypotheses.closedCounit/openCounit`.
- Closed-to-open orthogonality in all shifts: `Hypotheses.orthogonal`, for
  independent P and N and every integer n; vanishing is `Subsingleton` of Hom.
- Distinguished supported triangles with actual maps: `FiniteData.boundary` supplies
  an arrow for every object, and `Hypotheses.distinguished` uses exactly
  `exceptionalAdj.counit`, `openAdj.unit`, and that boundary in `Triangle.mk`.
- Canonical adjunction-induced shifts: finite `CommShift` data together with
  `Hypotheses.closedShift/openShift/exceptionalShift`. Mathlib's
  `Adjunction.CommShift` states precisely unit/counit compatibility; the recorded
  uniqueness lemma identifies it with `rightAdjointCommShift`. Thus no arbitrary
  exact structure on a right adjoint is substituted for the canonical one.
- Identity, tower and shift coherence of input comparisons:
  `Morphism.coh`, `Hypotheses.inputUnit`, and `Hypotheses.inputShift` respectively.
  The unit equation retains the actual scalar unitors on both schemes.

Conclusion clause-by-clause:

- The open comparison preserves the extended open unit:
  `FiniteConclusion.openUnit`, using the explicit `lastMap`, which is the
  openPush comparison followed by the openPull comparison mapped by openPush.
- Unique counit-normalized natural isomorphism b:
  `comparison` is defined, with real data, by `mateEquiv` applied to the inverse
  closedPush comparison. `FiniteConclusion.invertible` makes it an isomorphism.
  `FiniteConclusion.unique` quantifies over all natural transformations with
  the displayed counit transpose and says they equal this very transformation.
  `firstMap` is the closedPush comparison followed by closedPush of b, and
  `FiniteConclusion.counit` is exactly its prescribed exceptional-counit square.
- Both exceptional adjunction maps: `FiniteConclusion.unit` is the mate unit
  equation; the counit equation is the preceding `counit` field.
- Identity, successive inclusions and actual scalar associators:
  `FiniteConclusion.identity` and `tower`. Tower uses `(stageSystem ...).assoc`,
  not a strictified equality or a replacement associator.
- Exact shifts: `FiniteConclusion.shift` is `NatTrans.CommShift` for b, with
  the finite canonical right-adjoint structures fixed in the hypotheses.
- All three supported-triangle arrows: `counit`, `openUnit`, and `third` give
  the three literal coefficient squares. The last includes the scalar shift
  comparison before the shifted `firstMap`. `boundaryShift` uses the displayed predicate `boundaryShiftCompatible`
  to give the boundary shift square, including the integer sign `n.negOnePow` and `shiftFunctorComm`.
  The first two shift squares follow from the input adjunction shift clauses.
  Naturality is the conclusion `FiniteConclusion.boundaryNatural`, not an extra input. Tower and
  identity compatibility on vertices comes from the input Morphisms and b's
  tower/identity equations, so these arrow squares have those same compatibilities.
- Descent to the existing finite-field pair category: `exceptionalSystem` uses
  the finite J functors and `asIso comparison`, with coherence supplied by tower.
  Its existing `.functor` sends a literal pair `(E,K)` to `(E,J_E K)`.
  `Descent.representative` states its map on every common-stage representative:
  b at the source, J_M of the representative, then inverse b at the target.
  In mathematical composition order this is exactly
  `[M,b_{M/F}^{-1} J_M(u) b_{M/E}]`. Morphisms are the existing abelian Hom
  colimits, not a new carrier or a Karoubi envelope.
- Descended J is additive and exact: `Descent.exceptionalAdditive`,
  `exceptionalShift`, `exceptionalExact`, and `shiftNormalization`. The last
  pins its comparisons on every included finite object to the specified finite
  J shifts. Four analogous input functors have their exact structures and
  inclusion comparison shift equations in `inputShiftNormalization`.
- Descended adjunctions: `Descent.closedAdj/openAdj/exceptionalAdj`. These are
  actual Mathlib adjunctions on the literal pair categories, so they include
  natural inverse bijections on those filtered-colimit Hom groups, and both
  triangle identities. The six unit/counit normalization fields identify every
  component with its specified finite-stage class. The adjunction shift fields
  retain compatibility of those maps with the canonical shifts.
- Descended distinguished triangles with specified counit/open unit:
  `Descent.boundary`, its `boundaryNormalization` and signed `boundaryShift`,
  and `distinguished` for every
  literal pair. The boundary normalization contains the inclusion's shift map.
  Thus all three descended arrows are the prescribed finite-stage classes.
- Retained closed-to-open orthogonality: `Descent.orthogonal` for every pair P,
  pair N (possibly at different fields), and every integer n.

Dependency declarations used/read:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient field data.
- `def-weil-scheme-morphism-properties` is a convention node: the declared Mathlib
  `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` are used, rather than another collection of properties.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory` and its inherited category/triangulated data.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStagePullbackComparison`, `operationStageTransitionIso`. The recorded
  main declaration `commonStageDerivedInternalHom_existsUnique` was read; the
  pullback clauses in its same owning module are the relevant declarations here.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`,
  `SfIntegralDirectImage`, and the normalized coefficient ring and reduction
  comparisons. They fix the derived-direct-image meaning in the input; the
  right-adjoint interface uses the stipulated adjunction and its specified mate.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`,
  `stageSystem_existsUnique`, `unitor`, `inclusion`, `Pair`, `inclusionCommShift`,
  `inclusion_exact`, `distinguished_iff`; these are the actual category objects.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `.Triangulated`:
  `Pretriangulated`, `IsTriangulated`, `distTriang`; `.Functor`: `IsTriangulated`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `unit_mateEquiv`,
  `mateEquiv_counit`, and the pasting lemmas (the latter three are proof inputs).
- `Mathlib.CategoryTheory.Shift.Adjunction`: `Adjunction.CommShift`,
  `rightAdjointCommShift`, `commShift_of_leftAdjoint`,
  `CommShift.compatibilityUnit_unique_right`.
- `Sheaf.Paper.PbcScalarExtension`: `AlgebraicGeometry.Scheme.pbcCoherentScalarExtension`
  supplies the recorded scalar-coherence reference; the actual framework stage
  functors and tensor associators here are those of the general owning definition,
  not PBC categories substituted for the raw categories of this node.
- Proof-only modules: `Sheaf.CategoryTheory.StageSystemFunctorDescent`
  (`coefficientPairFunctor_exists` on the actual upstream quotient),
  `Sheaf.Paper.PbcVerdierAxioms`, and the triangulated adjunction import. Other
  proof dependencies are exact Mathlib lemmas already available through imports:
  `Triangle.coyoneda_exact₂`, `Triangle.yoneda_exact₂/₃`,
  `isIso₁_of_isIso₂₃`, `mateEquiv_vcomp/hcomp`, and `Adjunction.mkOfHomEquiv`.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: the existing
  `StageSystem.Morphism` and `.functor`, which provide the real colimit action.

Edge cases checked before and during writing:

- Z empty, U=X, and Z=X, U empty remain included; no nonempty-scheme binders.
- Zero objects and zero morphisms remain included. Orthogonality is subsingleton
  of an inhabited abelian Hom group, not `IsZero` of a bare type.
- E=L and repeated fields in a tower retain scalar unitors; no literal identity
  equality is imposed on tensor extension. All tower maps use actual associators.
- All positive, zero and negative shifts are quantified. The boundary equation
  retains the sign of the distinguished shifted triangle, unlike the degree-zero
  unit/counit equations. The earlier stage-1 warning about arbitrary rescaled
  right-adjoint shifts is addressed by the adjunction CommShift hypotheses.
- P and Q may start over different fields, and an arrow may first exist over a
  strictly larger field. `representative` quantifies over every common M and map.
- Scheme universe u and closure universe v stay independent, using the existing
  coefficient size transport. There is no finite-field model assumption on k.

Searches actually run with `msearch.py Q111 lem-sf-exceptional-common-stage-descent`:

- LeanFinder: `Counit normalized exceptional right adjoint scalar comparison supported
  localization triangles coherent common field pair category descent` returned eight
  generic localization/derived-adjunction results, including
  `Adjunction.localization_counit_app`; none states this node.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.rightAdjointCommShift`
  returned zero hits. The exact source declarations were opened directly.
- Mathlib grep: `exceptional.*descent|coefficientPairFunctor|mateEquiv` in
  `CategoryTheory` returned the existing generic mate API and bicategorical mates,
  not the supported comparison/descent statement.
- LeanSearch: `Scalar extension comparison for exceptional right adjoint with supported
  localization triangle and descent to common field pair category` returned eight
  ring/module scalar-localization results, no match for this node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` searched exceptional descent,
  common-stage and counit-normalization names and supported triangles. I read
  `SfQbarLocalizationCommonStage` (the opposite, open-extension-by-zero localization
  triangle), `SfLocalizationAllStages` (the parent existence theorem), and
  `SupportedTriangleMateIdentification` (finite etale coefficient support triangles).
  None states this conditional raw rational exceptional comparison/descent theorem.
  The assigned id was also searched by grep in WeilConjectures and in the upstream
  name index, with no matching declaration.

No node statement correction, new node, dependency repair, or STATEMENT-DISPUTED
flag is needed. The node statement and all dependency fields are preserved.
Compilation is through the prescribed server wrapper only; no local or global
Lean build was run. The finite and descent draft compiled cleanly; a final compile,
dry run and delivery validate the final packet. The first dry run passed after
moving an older unrecorded sandbox draft out of the delivery module directory.
A final clause audit then removed assumed finite-boundary naturality (it is proved
as a conclusion instead) and made descended-boundary shift compatibility explicit;
the revised file is recompiled and the dry run repeated before delivery.

The signed boundary equation is factored into `boundaryShiftCompatible`, a fully
explicit proposition on the already supplied functors and arrows. This preserves
the equation while avoiding repeated elaboration through concrete coefficient
category instances. It adds no assumption or new category structure.

The descended boundary shift proposition is packaged as `Descent.boundaryShift`
outside the dependent data record. The theorem existentially supplies both the
descent data and this proposition; its mathematical conclusion is unchanged.
The generic equation retains independent category object and morphism universes.

Final `scompile.py` result: both sandbox and library modes compile without errors
or warnings (27.8 s and 32.7 s). The delivered module contains exactly one named
theorem with `sorry`, no diagnostic commands, and no lines above 100 characters.
The node copy differs from the shared node only in `lean`; the stored signature
is extracted verbatim from the final theorem.

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
