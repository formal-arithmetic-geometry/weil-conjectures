## Worker report

Item: `lem-sf-qbar-localization-common-stage`. The module is
`Sheaf.Paper.SfQbarLocalizationCommonStage`; its theorem is
`WeilConjectures.sfQbarLocalizationCommonStage`. This is stage 2: the theorem's
only proof is `sorry`, with the complete eight-step natural-language proof in its
docstring. All helper definitions have actual data. The three records package
parts of this one assertion; they do not define another coefficient category.

Source read: the current main-20261015 blueprint,
`sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md`,
especially the integral, rational, and algebraically closed paragraphs. I read the
item, its eight proof steps, and the declarations and docstrings attached to all
statement dependencies. The stage-1 PASS record remains unchanged. This packet repairs the returned
immutable head `a16022f00064` (R1 and R2), as described below. The current live
node has no `lean` record. The retained packet was inspected and the prescribed
saved-packet `deliver2.py --no-push` was run before editing.

### Hypotheses

- The global field is `D : FiniteFieldDatum.{u}`. Its actual `D.k` is used as the
  geometric base, with its recorded characteristic `D.p`. The prime is
  `l : ℕ` with `[Fact l.Prime]`; the different-characteristic hypothesis is
  `hl : l ≠ D.p`.
- The coefficient closure is `Ω : Type v` with `[Field Ω]`,
  `[Algebra (Padic l) Ω]`, and `[IsAlgClosure (Padic l) Ω]`. The scheme and closure
  universes are independently quantified. The existing `Index l Ω` consists of
  finite coefficient subextensions of Ω and `Coefficient.{u} l Ω E` is the
  recorded coefficient-field lift used by the raw categories.
- `X : Scheme.{u}` has `[X.Over (Spec (.of D.k))]`. Separated finite type is
  `[IsSeparated (X ↘ Spec (.of D.k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
  `[QuasiCompact (X ↘ Spec (.of D.k))]`.
- `i : Z ⟶ X` has `[IsClosedImmersion i]`; `j : U ⟶ X` has
  `[IsOpenImmersion j]`. Complementarity is
  `hij : Set.range i.base = (Set.range j.base)ᶜ`.
- The structures over the base on U and Z are induced by composition with j and i.
  Their finite-type instances and quasi-compactness are constructed in the
  conclusion from those of X. Noetherianity of X follows from finite type over
  the field; the open embedding and closed embedding give the required
  topological Noetherian instances. In particular quasi-compactness of j is
  derived, rather than an added hypothesis. Residue-field invertibility is actual
  data from `sfQbarLocalizationResidueInvertible`: it maps
  `PurCompactSupport.coefficientPrimeUnit l D hl` along the geometric structure
  map to the residue field. No separate characteristic or invertibility
  assumption is imposed on U or Z. No descent of X to the finite field is assumed.

### Conclusions, clause by clause

The conclusion is `Nonempty (SfQbarLocalizationDescent l Ω D hl i j)`.

1. The categories are exactly `GeneralAlgebraicallyClosedCoefficients.Stage` and
   `Pair`, using the recorded `stageSystem`. A Stage is the raw
   `sfRationalConstructibleCategory`, and a Pair is the existing literal
   coefficient/object pair. The theorem never invokes a Karoubi envelope.
2. `openAction` is the existing `SfCompactSupportCoefficientAction` for
   `Compactification.ofIsOpenImmersion j`, hence the normalized extension by
   zero at `(j,id_X)`. Its `finite_eq`, `integralBeta_spec`, and `rationalBeta`
   fix all finite morphism maps and scalar comparisons to that construction.
   `closedAction` is a `StageSystem.Morphism` from Z to X.
   `closedAction_finite` identifies its entire finite functor with
   `(finiteLocalization E).closedRationalImage`, whose `closedPush.objects`
   and `tensors` pin ordinary closed direct image on objects and all arrows.
   `closedAction_beta` fixes the closed scalar comparison to
   `mateEquiv (finiteClosedAdjunction E) (finiteClosedAdjunction L)` applied
   to the square `(closedPull.β h).inv`. Its source is
   `closedAction.Φ E ⋙ T_X`, and its target is `T_Z ⋙ closedAction.Φ L`.
   This is the ordinary direct-image scalar comparison, fixed by the canonical
   pullback beta and the prescribed adjunctions. No equality with the chosen
   compact-support derived-limit object at `(id_Z,i)` is asserted.
3. `openPull` and `closedPull` are morphisms of these same stage systems.
   `openPull_finite` and `closedPull_finite` fix their finite functors to
   `rationalDerivedPullback`. The `*_beta` fields fix each comparison to
   `commonStagePullbackComparison` on the indicated literal pair, using `HEq`
   solely to account for the displayed equal finite functors. Their `*_desc`
   fields identify the descended functors with `commonStageDerivedPullback`.
4. `openExact`, `closedExact`, `openPullExact`, `closedPullExact` each have type
   `SfQbarLocalizationExactAction`. These assert finite and descended additive
   structures, shift structures for every integer, and `Functor.IsTriangulated`.
   The actual scalar associator/tower equation is already the `coh` field of each
   `StageSystem.Morphism`. The extra `unit` field spells out the normalized
   scalar multiplication unit through `operationStageTransitionIso` and
   `unitor`. `beta_shift` and `inclusion_shift` assert compatibility of the
   scalar and inclusion comparisons with those shifts. The four
   `openShift_finite`, `closedShift_finite`, `openPullShift_finite`, and
   `closedPullShift_finite` equations identify these finite shifts by `HEq`
   with the corresponding `rationalShift` fields of the rational sibling.
   Quotient descent uses the existing functor, whose map is defined on every common-field
   representative, so representative/enlargement independence is retained.
5. `finiteOpenAdjunction E` is `j_!,E ⊣ j^*,E`; `finiteClosedAdjunction E` is
   `i^*,E ⊣ i_*,E`, for the fixed functors above. All their units/counits occur in
   the compatible `StageSystem.Morphism.Hom` fields `openUnit`, `openCounit`,
   `closedUnit`, and `closedCounit`. The four `*_finite` equations equate the
   components of these compatible transformations with the finite adjunction
   components. The `finite*Adjunction_shift` fields assert shift compatibility.
   `openAdjunction` and `closedAdjunction` are the claimed common-stage
   adjunctions; their `*_shift` fields assert shift compatibility, while the four
   `*_desc` equations identify their units and counits on every pair with the
   actual image of the finite-stage components. Thus neither adjunction is a
   bare existence assertion detached from its finite-stage maps.
   In addition, `finiteOpenAdjunction_normalization` and
   `finiteClosedAdjunction_normalization` require `HEq` to the sibling
   `openRationalAdjunction` and `closedRationalAdjunction` at every E.
   These retain its `openCounitNormalization` and `closedUnitNormalization`;
   simultaneously negating the finite unit and counit cannot supply another
   normalized witness.
6. `triangle_image E K δ hδ` is precisely conditional on the given finite-stage
   completion being distinguished. Its first arrow is the finite open counit,
   its second the finite closed unit. The conclusion's first two arrows are the
   descended open counit and closed unit at `(E,K)`. Its third arrow is
   `(inclusion E).map δ` followed by the recorded inclusion shift comparison.
   Distinguishedness uses the existing `distTriang` on the raw Pair category.
   The field does not assert existence of a finite completion (that is the
   rational sibling's role). `objects` says every Pair is literally an inclusion
   of some `KE : Stage ... E`, a stronger representability convention already
   built into the dependency's pair definition.
7. `homComparison N M m` quantifies independently over `N : Pair ... U`,
   `M : Pair ... Z` and `m : ℤ`. `SfQbarLocalizationCommon` is the existing
   common-upper-field index of the literal shifted open output and closed
   output; their stages are N.stage and M.stage. At a common L,
   `SfQbarLocalizationStageHom` is exactly
   `Hom(((J.Φ L).obj (N.toStage hN))[m], (I.Φ L).obj (M.toStage hM))`.
   `sfQbarLocalizationSourceIso` is the prescribed scalar-shift comparison
   followed by shifted beta (the proof's a_L), and
   `sfQbarLocalizationTargetIso` is beta for the closed operation (b_L).
   The additive maps `sfQbarLocalizationToOperation` and `...ToRaw` conjugate
   by these actual isomorphisms using Mathlib's additive composition maps.
   `sfQbarLocalizationHomTransition` conjugates the existing `transportHom`
   with those maps. Thus it includes the scalar associators and the operation
   comparisons, including arrows first represented beyond E and F.
8. `SfQbarLocalizationHomColimit` is literally `AddCommGroup.DirectLimit` of
   those displayed Hom groups with those transitions, rather than an abstract
   carrier asserted to be a colimit. `SfQbarLocalizationHomComparison.system`
   asserts the directed-system equations. Its `coordinates` is the displayed
   additive equivalence, from the shifted common-stage Hom to this direct
   limit. Its `representative` equation fixes the equivalence on every raw
   morphism represented at every common field L, using the canonical shifted
   pair isomorphism and the actual `DirectLimit.of` map. `finite_zero` states
   every displayed group is a subsingleton; `colimit_zero` and `hom_zero` state
   the two final vanishings. Because all Hom types are additive groups,
   `Subsingleton` means the zero group. This covers all common-stage arrows,
   and does not assert any single integral lattice for rational arrow data.

### Dependencies and imports

All names below lie in `WeilConjectures` unless otherwise specified.

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and its actual base field.
  The characteristic-to-unit map is the existing
  `PurCompactSupport.coefficientPrimeUnit`.
- Mathlib `FieldTheory/IsAlgClosed/Basic`: `IsAlgClosure`; Mathlib scheme
  properties use `Scheme.Over`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsClosedImmersion`, and `IsOpenImmersion` as specified by
  the convention dependency.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  the raw scalar localization, its additive and triangulated structures.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `Pair`,
  `stageSystem`, `stageTransition`, `Common`, `StageHom`, `transportHom`,
  `ofHom`, `inclusion`, and the inherited shifts and triangulation. This is
  publicly imported by `DerivedPullbackTensorHom`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, `commonStagePullbackComparison`,
  `operationStageTransitionIso`. Its recorded representative normalization
  supplies the pullback interface used here.
- `Sheaf.Paper.SfDerivedDirectImage`: the recorded completed/proper direct-image
  construction used by the normalized ordinary closed direct image.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the recorded compact-support
  construction, including `sfCompactSupportFiniteFunctor` and the
  `Compactification.ofIsOpenImmersion` specialization.
- `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportCoefficientAction` (the added landed statement dependency).
- Mathlib `CategoryTheory.Adjunction.Mates` supplies `mateEquiv` and `TwoSquare`;
  `CategoryTheory.Shift.Adjunction` supplies `Adjunction.CommShift`;
  `Triangulated.Functor` supplies `Functor.IsTriangulated`.
  Mathlib `AddCommGroup.DirectLimit` is the recorded directed-colimit leaf.
  `CategoryTheory.Preadditive.leftComp` and `rightComp` give actual additive
  conjugation maps.
- Proof-dependency imports, without `public`: `Sheaf.Paper.BasicOperationsCoefficientReduction`
  (`basicOperationsCoefficientReduction`), `Sheaf.Paper.ScalarExtensionExactIntrinsic`
  (`sfScalarExtension_exact_triangulated`), `Sheaf.Paper.SfScalarExtensionComposition`
  (`sfRationalScalarComp` and coherence), and
  `Sheaf.CategoryTheory.StageSystemFunctorDescent`
  (`CategoryTheory.StageSystem.coefficientPairFunctor_exists` and the
  reexported compatible-transformation descent).
- `Sheaf.Paper.SfRationalLocalizationOrthogonality`:
  the unchanged definition-node interface `def-sf-rational-localization-data`:
  `SfRationalLocalizationOrthogonality`, with `openRationalAdjunction`,
  `closedRationalAdjunction`, `closedRationalImage`, and the four
  `SfRationalizedExactFunctor.rationalShift` projections. This now-live
  data package is a public statement dependency. Its normalization fields fix the
  integral maps; its four localization equations fix the rational maps.

The new definition node registers the existing six data definitions in the
rational-localization module. The theorem remains only in `proof_deps`: the
signature uses no theorem constant or choice from its existence assertion. The
item changes only `lean` and `stmt_deps`; its mathematical statement and proof
are unchanged. No dependency module is replaced.

### Edge cases

The types allow empty X, U, or Z; complementarity retains the expected empty/full
cases, and residue-field instance construction then has no points to evaluate.
Zero N or M is included because both quantify over the full raw categories.
The shift m is any integer, including negative and zero. E and F may differ;
`Common` ranges over fields containing both, and the transition/representative
formulas quantify over every larger common field. When E=F=L the scalar-unit
normalization is still required, rather than treating scalar identity as a
literal identity functor. No condition says that an arrow is represented at E
or F. Independent u and v do not force a new coefficient/geometric universe
identity. The algebraic closure and finite-coefficient index are inhabited
through the existing dependency, so the displayed colimit is not an empty
index trick. No false-statement counterexample was found and no
STATEMENT-DISPUTED flag is raised.

### Searches for reuse

- `msearch.py ... leanfinder` with “Descent of open and closed localization
  adjunctions through common finite coefficient fields, exact triangles, and
  cross-stage Hom colimit orthogonality”: eight generic hits, including
  `CategoryTheory.Adjunction.localization`, its counit formula, triangulated
  localization triangles, and `ObjectProperty.isColocal_trW`; none is this
  constructible coefficient-stage assertion.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CategoryTheory.Functor"`:
  twelve generic constructors/accessors (`Adjunction.mkOfHomEquiv`,
  `mkOfUnitCounit`, etc.); no such descent statement.
- `msearch.py ... grep` with
  `(common.stage|cross.stage|[Qq]bar).*(localization|orthogon)|(orthogon).*filteredColimit`:
  zero Mathlib hits.
- `msearch.py ... leansearch` with “Exact open closed adjunctions descend to
  common finite coefficient stages with Hom groups a filtered colimit”:
  eight general filtered-colimit constructions for groups and modules,
  including `AddCommGrpCat.FilteredColimits.colimitAddCommGroup`; no exact match.
- Project/upstream `rg` with
  `SfQbarLocalization|sfQbarLocalization|qbar.*localization|localization.*[Cc]ommon[Ss]tage`
  found no exact statement (only unrelated qbar scalar-basis pushforward).
  `grep -rn "lem-sf-qbar-localization-common-stage" lean/WeilConjectures` found
  no attached declaration. The related `SfLocalizationAllStages` handles the
  supported localization route and imports the parent, so it is deliberately
  not imported here: that would create a downstream import cycle.
  `SfCommonStageDirectImage` has a finite-field descent hypothesis on geometry
  and is too restricted for this node. Neither replaces this assertion.

### Validation

Every delivered file is compiled separately through the prescribed
`scompile.py NE lem-sf-qbar-localization-common-stage` wrapper against the live
published build. The statement compiled in both the sandbox and library module
modes without errors or unexpected warnings. The expected stage-2 `sorry`
remains only on the named theorem. The wrapper's delivery preflight and per-file
compilation are run before pushing; no local global build or direct repository
mutation is used.

## Repair of returned immutable head a16022f00064

R1 (H3/H5): removed the closed compact-support action at `ofIsProper i`.
Its finite object was chosen as a derived-limit vertex, whereas the normalized
ordinary direct image has a different literal object. An isomorphism of these
objects does not justify the old equality. The replacement `closedAction` is a
stage morphism with its finite functors equal to `closedRationalImage` and its
beta exactly the mate of inverse `closedPull.β`. All closed exactness, shifts,
adjunction units/counits, triangle vertices and Hom coordinates now use this
ordinary direct-image stage morphism. The existing closed adjunction and shift
HEqs are therefore on the matching finite functors. No noncanonical equality
of chosen limit vertices remains.

R2: removed the rational-localization theorem from `stmt_deps`, retaining it in
`proof_deps`. Added `def-sf-rational-localization-data` as a statement dependency.
The existing module is unchanged. The new node's six declarations are exactly
the plain definitions used by the signature; it contains no existence theorem.
Thus the statement depends on the meaning of normalized rational localization
data, while the proof will use the theorem that supplies it at every E.

Comparison with the current read clone shows the item has no landed module or
Lean record. The wrapper rebases the packet onto current main for delivery;
no direct Git command or shared-repository write is used. The theorem signature,
open side, pullback pins, Hom DirectLimit, triangles/objects, geometry, universes
and the sole sorry proof are retained from the returned head.

## New nodes

`def-sf-rational-localization-data` names the six already published definitions
in `Sheaf.Paper.SfRationalLocalizationOrthogonality`, with `existing:true`.
The source is the rational-stage paragraph of the same localization proof.
It defines the *type* of normalized integral/rational operations, exact shift
structures, adjunction maps, triangle images and cross-Hom coordinates, and
its three canonical normalization helpers. It makes no assertion of existence.
Its `stmt_deps` are the definition prerequisites of the published package;
all ten are cited in its self-contained statement. Its `lean.statement` is
verbatim the existing structure signature. The existing theorem-module source
and its docstrings are unchanged, as R2 explicitly permits.

Searches for this node: `blueprint_refs.py search 'rational localization'`
returned zero blueprint nodes, and ancestor returned
`prop-sf-open-closed-triangle-all-stages`. `rg` across `dag/nodes` found these
names attached only to the rational-localization *theorem*, with no definition
node. `rg` in `lean/WeilConjectures` found none, and in `lean/Sheaf` found the
six exact definitions in the unchanged module. `msearch.py leansearch` with
“Normalized rational open closed localization data with exact functors
adjunctions and cross Hom coordinates” returned eight generic derived/localized
adjunction results. `leanfinder` with “Data package for rationalized open and
closed immersion functors with fixed adjunction maps and orthogonality” returned
eight scheme restriction/gluing results. `grep` with the six declaration names
returned zero Mathlib hits. The new node records these results. Reuse is exact:
the definition node refers to the same declarations already used in the packet,
without copying any construction or claiming the existence theorem is a def.

## Second reading by NE

The dispatcher prohibits starting another agent; this is the required sequential
self-check of the node, module and new definition-node record. I checked the
hypotheses and all eight conclusion clauses above against the actual field types.
The R1 mismatch was the unjustified equality of two chosen limit vertices; its
replacement uses the very ordinary direct-image functor in the normalized
adjunction, with beta fixed by `mateEquiv`. For E≤L, pullback beta inverse has
source `T_X ⋙ i_L^*` and target `i_E^* ⋙ T_Z`; its mate has exactly source
`i_{*,E} ⋙ T_X` and target `T_Z ⋙ i_{*,L}`. This checks orientation, not only
existence of a natural isomorphism. The finite adjunction/shift HEqs retain
canonical maps; changing the finite units/counits by a sign still fails their
normalization. Empty/identity closed and open cases and repeated fields are
included with the scalar-unit equation. Hom still allows independent original
E,F, arbitrary larger representatives, and every integer shift. No new
theorem hypothesis, universe equality, integral lattice, or category was added.
The new definition node owns only the six unchanged data definitions, while
the existence theorem is solely a proof dependency. No other mismatch found.
