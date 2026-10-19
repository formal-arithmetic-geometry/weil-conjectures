## Worker report

The module `Sheaf.Paper.ArbitraryFieldAdjunctionScalars` states
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.ScalarAdjunction.arbitrary_field_adjunction_scalars`.
Its proof alone is postponed. The helper structures unpack the clauses of this node;
no independent notion is introduced and no dependency record or natural statement changes.
The two restriction comparisons and the two normalized stage comparisons have real data:
conjugation of the specified balanced comparison, and composition with the specified
stage-normalization isomorphisms, respectively. No arbitrary functor or comparison is chosen.

Hypothesis-by-hypothesis and clause-by-clause reading:

- The theorem binds `k : Type u`, `[Field k]`, `l : ℕ`, `[Fact l.Prime]`, and
  `_hl : IsUnit (l : k)`. `Ω` has its field, rational-p-adic algebra and
  `IsAlgClosure ℚ_[l] Ω` structures. `Compatibility` quantifies over precisely
  `Padic.FiniteCoefficientFields l Ω` and inclusions `h : E ≤ F`.
- Schemes are the dependency's `DirectImage.Space k l`. Its `scheme.Over`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` fields say separated
  finite-type k-scheme. Its `Base` fields retain the derived consequences
  noetherianity, finite dimension and scheme-level invertibility, including the
  empty scheme. The quantified `f` has `f.IsOver (Spec (.of k))`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`, exactly a separated finite-type
  k-morphism. The extra base witnesses are consequences, not new restrictions.
- The input `r : ContinuousRational.Family l` and `p : DirectImage.Package k l r`
  are the normalized realizations referred to by the statement. They exist by
  the two dependency theorems. The assertion is uniform in any such normalized
  witnesses; it does not assume the desired scalar mate equality.
- Each raw category is exactly `PbcRationalCategory W (pbcIntegralDatum l H)
  (pbcUniformizer l H)`, the existing scalar localization with unchanged integral
  objects and tensor-localized Hom modules. There is no Karoubi construction.
- `P_H` is `(r.along H f).raw l H`, using the actual completed integral pullback;
  `D_H` is `DirectImage.rawPush l H f (p.along H f).preserves`, the scalar
  localization of the ordinary completed-ring derived direct image. The latter's
  tower identification and the former's completion-unit normalization are retained
  by the realization dependency. `h_H` and its inverse are the actual
  `(p.along H f).rawAdjunction.homEquiv` and `.symm`. Its actual `.counit` is epsilon.
- `stagePullComparison` is `a⁻¹`, and `stagePushComparison` is `b`. They compose
  the published `Mixed.raw` / `DirectImage.FieldChange.raw` with precisely
  `pbcStageNormalization`. Thus the scalar functor really is
  `pbcStageTransition`, whose repeated-field case is literally identity. The
  unnormalized tensor maps remain separately visible in `Equations`.
- `HomEquations.mate` specialized by `StageEquations` is the displayed counit/mate equality.
  Its `forward` and `inverse` fields are exactly the two displayed Hom
  equations for every A, B, u, v. Lean's `x ≫ y` means the source's `y ∘ x`.
  The `mate`, `forward`, `inverse` fields of `Equations.raw` give the identical equations before
  conjugating by the published tensor unitors.
- The ambient coefficient sheaf is the existing `rationalCoefficientSheaf l W H`.
  The input `r` identifies it with the completed coefficient sheaf localized at
  the uniformizer and with continuous coefficient functions. The ambient functors
  are `derivedPull f (r.along H f).coefficient`, `derivedPush ...`,
  `pbcDerivedExtend (r.fieldChange E F i W).coefficient`, and `pbcDerivedRestrict ...`.
  These are the actual derived module operations, not arbitrary functors.
- `restrictionComparison` constructs d as the conjugate of `Mixed.ambient.symm`
  under the composite, tensor-unit-normalized geometric/coefficient adjunctions.
  `moduleRestrictionComparison` is its underived counterpart.
  `Equations.restriction_normalization` identifies d with the canonical
  right-derived comparison: it intertwines the two actual derived pushforward
  units with the localization of the underived comparison. This is the universal
  composition normalization, on every complex and hence on K-injective resolutions.
- `Equations.coefficient_transpose` says precisely that the coefficient adjunct
  of the specified ambient b is `D_E(eta_X)` followed by d inverse. The unit is
  that of `pbcDerivedScalarAdjunction`, normalized on K-flats by x ↦ x tensor 1.
  `Equations.ambient_mate` is the displayed ambient geometric mate equality.
- Restriction to the raw comparisons is the input `Mixed.compatibility` and
  `DirectImage.FieldChange.compatibility`, with their integral normalization
  fields. The input `Comparison.unit` and `.counit` identify the actual raw and
  ambient adjunction maps; no new unspecified realization is substituted.
- `LinearHomEquations.forward_add`, `.inverse_add`, `.forward` and `.inverse`, specialized by `Linearity`, express additivity and H-linearity for each direction of
  h_H, using the existing field actions on actual raw Hom modules.
- `ShiftCompatibility` gives operation shift structures together with the
  universal derived counit/unit normalizations, compatibility with the actual
  realization and coefficient comparisons, and `Adjunction.CommShift` for both
  raw and ambient adjunctions at both fields. The latter means actual unit and
  counit commute with every integer shift, equivalently both Hom bijections do.
  Its four final fields assert that a, b and their ambient versions commute with
  these shifts. The canonical scalar associators already commute with shifts
  by the imported scalar-extension proposition.
- `IdentityExtension.raw_pull` and `.raw_push` assert the identity-extension
  equations with the published tensor unitors. Its ambient unitors are fixed
  on ordinary tensors by multiplication and on derived complexes by the actual
  universal counits, and its ambient equations give the same identity case
  there. `pbcStageNormalization` converts the raw equations to literal identity
  transitions; it is exactly the normalization used in `StageEquations`.
- `Tower.raw_pull`, `.ambient_pull`, and `.direct_image` assert pasting of
  these very comparisons for E ⊂ F ⊂ G under the published raw and ambient
  associators. The embeddings are actual `pbcSubfieldInclusion` maps;
  `pbcSubfieldInclusion_comp` identifies their composite with the direct
  inclusion. Pasting the forward Hom equations gives the composite forward
  equation; the inverse bijection gives the inverse and counit equations.
  The scalar proposition's existing pentagon handles longer towers and repeated
  fields. No assertion is conditional on the fields being distinct.

Dependency declarations and source readings:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported actual coefficient
  integer rings, quotients and uniformizer. Finite subfields and their algebra
  structures are the existing `Padic.FiniteCoefficientFields`.
- `Sheaf.Paper.PbcRationalCategory`:
  `AlgebraicGeometry.Scheme.PbcRationalCategory`, `PbcRationalDerivedCategory`,
  and `pbcRationalization`.
- `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains
  `pbcActualCompletedPull` and `pbcActualCompletedPullUnit` from the strict-tower
  module. The item uses their finite-field-stage restriction via
  `ContinuousRational.integralPull`, `Along.raw` and `Along.completion_unit`;
  it does not use the Qbar pair-category specialization as a raw category.
- `Sheaf.Paper.SfCommonStageDirectImage` retains the actual integral direct-image
  construction through `SfDerivedDirectImage`; the item uses its arbitrary-field
  raw restriction, already exposed by `DirectImage.integralPush`, `rawPush`,
  `Comparison.integral_transpose` and the direct-image realization theorem.
  It does not specialize to a finite-field datum.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `Family`, `Base`, `At`, `Along`, `Mixed`, `FieldChange`, `FieldComposition`,
  `modulePull`, `derivedPull`, and `continuous_rational_derived_realization`.
- `Sheaf.Paper.RationalDirectImageRealization`:
  `Space`, `Ordinary`, `Comparison`, `FieldChange`, `FieldComposition`, `Package`,
  `modulePush`, `derivedPush`, `pushUnit`, `rawPush`, and
  `rational_direct_image_realization`. Their full signatures and normalization
  docstrings were read, including the actual raw unit/counit and ambient mate fields.
- `Sheaf.Paper.PbcScalarExtension`: `pbcRationalScalarExtension`,
  `pbcRationalScalarCompComponent`, `pbcRationalScalarUnit`, `pbcStageTransition`,
  `pbcStageNormalization`, `pbcSubfieldInclusion`, and its identity/composition
  equations. The existing ordinary and completed scalar comparisons are retained
  by the realization structures, not restated as unrelated isomorphisms.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; its concrete same-site
  universal-unit-normalized specialization is the existing
  `pbcDerivedScalarAdjunction` from `BoundedConstructibleTower`, used in the data.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, read with its entire
  comparison-unit and K-injective normalization. The helper d is on the actual
  pro-etale module categories, including the object/morphism universe difference,
  and its universal-unit equation states that same canonical comparison. No
  equality of the site's object and morphism universes is imposed.
- The morphism-properties node is explicitly a convention node. The actual
  scheme and morphism properties are Mathlib's recorded classes. Proof-only
  imports also retain the stated shift, ringed comparison and rational transport
  dependencies and their proof route.

Source: I read the ancestor blueprint unit's affine-curve statement and the actual
Bhatt–Scholze PDF at Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15. The latter
explicitly distinguishes ordinary ambient derived module pullback from naive
pullback. This delivery uses the tensor module inverse image in the dependency.

Edge cases checked mathematically: E = F and repeated adjacent fields in towers
(use the actual tensor unit, then literal stage normalization); f = identity;
empty X or Y (no nonemptiness assumption); A = 0, B = 0 and zero morphisms;
all cochain shifts, including negative shifts; ramified finite coefficient
extensions (no unramified or flatness hypothesis is added); arbitrary k with
l invertible, with no finite/algebraically closed base-field restriction. The
small pro-etale site retains object universe u+1 and morphism universe u. All
variables and universes are explicitly bound; the inherited common ambient
universe is the coefficient/geometry size convention of the realized interfaces.

Searches (2026-10-18):

- msearch LeanSearch: `Scalar extension of coefficients preserves the normalized
  derived pullback direct image adjunction` — eight hits on ordinary module or
  presheaf scalar adjunctions; none states the normalized adic/raw comparison.
- msearch LeanFinder: `Scalar extension of coefficient fields commutes with the
  completed pullback direct image adjunction Hom bijection` — eight hits including
  ordinary sheaf and scheme module adjunctions, and generic composition conjugacy;
  no match to this node.
- msearch Loogle: `CategoryTheory.Adjunction, CategoryTheory.NatTrans` — no hits.
- msearch grep: `mateEquiv|conjugateEquiv|homEquiv.*naturality`, Mathlib
  `CategoryTheory/Adjunction` — 25 generic adjunction hits. Use existing
  `conjugateIsoEquiv`, not a new definition of conjugation.
- rg over upstream `WeilConjectures/` and side `lean/Sheaf/`: exact item id and
  `ordinary_adjunction_scalar` — no exact existing declaration; concept searches
  show the two normalized realization interfaces and scalar-extension module,
  which this file uses. Searches for the new declaration name and namespace in
  both libraries and `dag/lean_names_upstream.json` found no collision.

No STATEMENT-DISPUTED issue or natural-language correction was needed.

## Second reading by Q14

I reread the complete node against the file as a separate pass. No other agent was
started, as required by the dispatcher; the maintainer supplies the independent
review. The main correction during this pass was to make the algebraic closure
and its actual finite intermediate fields explicit, and to add `StageEquations`
using `pbcStageTransition`: the realization interfaces initially express tensor
extension before the proposition's literal identity normalization. The added
`stagePullComparison` and `stagePushComparison` perform exactly that normalization,
so the identity case now uses the node's specified functor. I also checked the
orientation of d, a inverse, b, the order of every `≫`, both Hom equations, both
linearity directions, and that the ambient coefficient transpose is stated in
addition to the geometric mate identity. The ambient d is constructed and tied to
the universal right-derived units, rather than introduced as an arbitrary map.
The tower includes the ambient pull comparison and the existing direct-image
composition equations. Shift data are explicitly resolution-normalized and tied
to the actual realization maps, not just existence of unspecified shift structures.

The repeated Hom and linearity formulas are defined once in `HomEquations` and
`LinearHomEquations`. `Equations.raw`, `StageEquations`, and `Linearity` substitute
the recorded canonical functors and adjunctions directly into these predicates.
This avoids repeatedly elaborating the long raw-category expressions; the
formulas, their coefficient actions, and every quantified object are unchanged.
These predicates only unpack clauses of this node, not new independent notions.

## Repair verification by Q14

The retained packet was tested first, as the repair handoff requests. The current
`deliver2.py Q14 lem-per-arbitrary-field-adjunction-scalars --no-push` passed
preflight and compilation (dry-run commit `c16815180b`). The returned immutable
head `5605075fd6ea` failed while compiling imported infrastructure
(`RingedSiteDualityMaps` and `RingedDerivedMonoidalComparisons`); those failures
do not reproduce against the current published dependency closure. No dependency
module is copied or replaced in this packet.

I then reread the retained node, its full 449-line module, and the clause mapping
above. The three raw Hom equations have the displayed orientations; the actual
ambient coefficient transpose and universal-unit normalization are retained;
identity, repeated-field towers, shifts and both linearity directions remain
explicit. Comparing the saved node with the current shared DAG shows that only
`lean` differs; the mathematical statement and dependency fields are unchanged.
The separate prescribed `scompile.py` check also passed both sandbox and library
module compilations (27.5 s and 24.0 s respectively), without errors or warnings.
The Lean module is retained unchanged, following the handoff's instruction for
a saved packet whose initial dry run passes.
