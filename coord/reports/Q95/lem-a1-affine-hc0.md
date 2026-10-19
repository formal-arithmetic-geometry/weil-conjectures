## Worker report

`Sheaf.Paper.AffineCurveHcZero` states
`RealSheaves.Setup.subsingleton_affineCurveHcZero`, with the sole theorem proof
`sorry`. Its conclusion uses exactly the recorded
`WeilConjectures.qbarWeilSheafCohomology`, compact-support component, in degree zero.
The node's statement and proof are unchanged. Its stmt_deps gains the definition
node `def-a1-common-stage-lisse-lattice`, for the lisse-model interface explained below.

Hypothesis and clause correspondence:

- The finite-field and coefficient conventions are `S : RealSheaves.Setup.{u,u}`.
  This retains p prime, a positive, the actual field k0 with cardinality p^a,
  its chosen algebraic closure k, the distinct coefficient prime l, its chosen
  coefficient closure, and the chapter's plain embedding into C. No choices of
  a different geometric fibre, coefficient closure, or field embedding are made.
- `U₀ : Over (Spec (.of S.k₀))` is the scheme over the specified base field.
  `hU : S.IsCurve U₀.left` is the dependency's full chapter curve predicate:
  nonempty, separated, smooth, finite type, pure dimension one, and connected
  after base change to the chosen algebraic closure. In particular neither the
  empty scheme nor a zero-dimensional scheme is admitted as a curve.
- `LocallyOfFiniteType U₀.hom`, `QuasiCompact U₀.hom`, and
  `IsSeparated U₀.hom` expose the corresponding source curve hypotheses as
  instances needed to form the recorded Weil categories. These repeat properties
  already contained in hU; they add no geometric assumption.
- `IsAffine U₀.left` is exactly the additional affineness hypothesis.
- `F : sfCommonStageWeilSheaf S.cohomologyFieldDatum S.l S.l_ne_p U₀ S.Qbar`
  is the dependency's actual fixed-pair Weil sheaf, with carrier in the standard
  heart. It retains its Frobenius isomorphism; the statement does not concern
  an arbitrary complex or an independently supplied cohomology space.
- `hF : HasCommonStageLisseLattice ... ((sfCommonStageWeilForget ...).obj F.obj)`
  renders lissity of the underlying sheaf in the recorded completed coefficient
  model. It permits a finite coefficient stage different from F's literal stage,
  and an isomorphism in the actual common-stage category. It requires no
  Frobenius-stable lattice. This is the inverse-system lisse convention of
  def-pod-lisse-l-adic-sheaves in its completed presentation. In this smooth
  curve application the scheme is normal/geometrically unibranch, so lissity
  does admit a global integral lisse lattice: Bhatt--Scholze 7.4.10 identifies
  the pro-etale group with the profinite etale group; its continuous finite-stage
  representation has compact image and preserves a lattice. Proposition
  6.8.4(1) identifies the lattice with its finite quotient systems, and
  6.8.4(4) identifies its rationalization. Removing integral torsion from an
  inverse-system lattice does not change its rationalization. No such global
  lattice assertion is made here for arbitrary singular schemes.
- `c : Compactification (S.cohomologyFieldDatum.geometricFiber U₀).hom`
  is any compactification used by the recorded cohomology definition. This
  auxiliary choice is universally quantified. Finite type and separatedness over
  a field guarantee compactifications, so this is not an additional restriction
  on the curves or sheaves covered by the node.
- The conclusion `Subsingleton ((qbarWeilSheafCohomology ... c F 0).2)` says
  H_c^0(U,F)=0. The second component is compact-support cohomology, not ordinary
  cohomology. This is a module with zero, so Subsingleton is precisely vanishing.

The actual field-datum conversion `Setup.cohomologyFieldDatum` fills the fields
of the recorded `FiniteFieldDatum` from S; its cardinality proof is the existing
`Nat.card_eq_fintype_card` followed by S.card_eq. The three exported instance
helpers expose the existing finite-type, quasi-compact and separated pullback
instances on the bundled geometric fibre. Each is just `inferInstanceAs` on the
standard second projection. These are interface constructions, with no new
postponed proof, new mathematical hypothesis, or arbitrary chosen object.

Dependency declarations read and used:

- `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, `.IsCurve`,
  `.geometricCurve`; read their full definitions. The comparison datum uses the
  same `pullback` and second projection as the chapter's geometricCurve.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilForget`, and their Frobenius
  pullback and heart definitions (publicly imported by cohomology).
- `Sheaf.Paper.OrdinaryCompactCohomology`:
  `ordinaryCompactCohomology`, `qbarWeilSheafCohomology`,
  `qbarCompactCohomology`, `qbarCompactSections`, and the component ordinary
  constructions. They use the recorded integral completion, raw rationalization,
  common finite coefficient stages, point fibre, and coefficient homology.
- `Sheaf.Paper.LisseAdicSheaves`: `LisseIntegralSheaf`,
  `IsLisseIntegralDiagram`, `LisseRationalSheaf`, and `LisseAlgebraicSheaf`.
  Their inverse-system, reduction, rationalization and coefficient-stage
  definitions were read. The module is imported for the ordinary lisse sheaf
  in the recorded proof plan, not replaced by the older WeilSheaf.IsLisse.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.Stage` and `.inclusion`.
- `Sheaf.Paper.SfIntegralConstructible` and
  `Sheaf.Paper.SfRationalizationKaroubi`: `sfIntegralConstructibleCategory`,
  `sfRationalConstructibleLocalization`. The ambient category is
  `scalarReductionSource` from DerivedScalarExtensionRestrictionAdjunction,
  modules over the completed coefficient sheaf, not a discrete coefficient ring.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`; local ranks may vary and rank zero is allowed.

Available proof dependencies are imported: Mathlib's
`Algebra.FiniteType.isNoetherianRing`, geometric-integrality and smooth-relative-
dimension permanence modules; the upstream fixed-dimension, smooth-geometrically-
reduced and proper-affine-finite modules; and
`Sheaf.Paper.GaloisLisseRepresentations`. The degree-zero support comparison
`lem-a1-degree-zero-compact-support-sections` has no recorded Lean module on the
base, so there is no import for it. It is only a proof prerequisite, not a missing
notion needed to type this statement. Its role remains explicit in the theorem's
five-step proof docstring. No import cycle is introduced.

Edge cases checked before writing and on rereading:

- The zero lisse sheaf is included: the lattice may have rank zero. No nonzero
  rank, purity, irreducibility, or semisimplicity is assumed.
- The empty scheme and Spec k0 are excluded by the recorded nonempty pure-one-
  dimensional curve convention. The latter would have nonzero H_c^0 for the
  constant sheaf, so dimension one is essential and retained.
- The affine line with its constant sheaf is included. A proper smooth connected
  curve with a nonzero constant sheaf would have nonzero H_c^0; affineness is
  retained and used to rule out properness in the proof.
- A skyscraper sheaf could have nonzero H_c^0 on an affine curve, so the lisse
  hypothesis is substantive. Arbitrary constructible sheaves are not substituted.
- The lattice is required only for the underlying sheaf: geometric Frobenius
  may rescale every lattice. Requiring an invariant lattice would be stronger
  than the node and is deliberately absent.
- Scalar extensions can enlarge a coefficient field; the model quantifies every
  finite stage and its isomorphism in the common-stage category. It does not
  demand a model at the particular stage stored in F.
- Any compactification is allowed; the coefficient prime is distinct from p as
  part of S, and no finite coefficient exponent, weight, or cohomological range
  restriction is introduced.
- All universes and variables are explicit. The theorem uses the recorded
  cohomology API's common ambient universe for schemes and coefficient closure;
  the lisse-lattice definition itself allows independent scheme/coefficient
  universes and does not equate site object and morphism universes.

Searches made (full wrapper output is in searches.jsonl in the sandbox):

- LeanFinder: “The zeroth compactly supported cohomology of a lisse Weil sheaf
  on a smooth geometrically connected affine curve vanishes”: eight unrelated
  singular/group/continuous cohomology hits; no match.
- Loogle: `Subsingleton, cohomology`: no hits, unknown identifier cohomology.
- Mathlib grep: `compactlySupportedCohomology|compactSupport.*lisse|hc0`,
  AlgebraicGeometry: three unrelated local-variable hc0 occurrences in
  ProjectiveSpectrum/Basic.lean.
- Direct rg in upstream WeilConjectures and lean/Sheaf located the old
  `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`
  in WeilConjectures.WeilSheaf.Curve. Its full signature and docstring were read.
  It uses the older derived-of-Weil-sheaves coefficient model, not the recorded
  fixed-pair/common-stage model; no comparison identifies these definitionally.
  The same mismatch affects the older wider-range theorem in AffineCurveUpper,
  read with `scompile.py --source` because its local file is absent. These are
  not exact existing bindings for this node with its current dependencies.
- The dependency record for sfWeilComplex explicitly explains that older-model
  defect and excludes the older derived-of-pairs construction. The new statement
  follows that recorded repair.
- For the missing lisse-lattice interface: LeanSearch returned eight generic
  module-sheaf finite-presentation and tilde hits; LeanFinder returned eight
  perfectoid/condensed hits; Loogle `SheafOfModules.IsFiniteLocallyFree` reported
  no hits/unknown identifier. Mathlib, upstream and side rg for
  `IsSfLisse|sfLisse|IsLisseCommonStage` and the common-stage lisse patterns found
  no matching predicate. `blueprint_refs.py search lisse` and DAG rg found the
  related inverse-system definition and realization comparison nodes, not this
  predicate. The new node records these searches.

No statement correction, dependency-node repair, or STATEMENT-DISPUTED flag.
The sole postponed theorem matches lem-a1-affine-hc0 and carries its complete
natural-language proof. Both definitions contain actual data or propositions,
with no sorry-backed choice.

## New nodes

`def-a1-common-stage-lisse-lattice`, module `Sheaf.Paper.CommonStageLisse`, defines
`WeilConjectures.HasCommonStageLisseLattice`. It expresses that a common-stage
object is isomorphic to the recorded rationalization and inclusion of an integral
constructible complex isomorphic to N[0], where N is finite locally free over
completed coefficients. Its source is Weil II (1.1.1) b)--d) and Bhatt--Scholze
6.8.3, 6.8.4(1),(4). This is an interface between already recorded notions;
it constructs no alternative inverse-system category, coefficient ring, derived
category, rationalization, or common-stage localization. The geometric curve
application is normal, where 7.4.10 ensures the global lattice presentation is
exactly the full lisse hypothesis. General lisse rational sheaves on singular
schemes need only admit such lattices etale locally: no global-lattice equivalence
for that generality is asserted. Searches and source comparison are detailed
above and recorded in the new node.

## Second reading by Q95

This is the author's self-check; the dispatch brief assigns the independent
review to the maintainer. I reopened the node, the module, the definition node,
the four original dependency records and their actual declarations, and both
blueprint snapshots (identical statements). The conclusion uses the compact,
second component at degree zero; F is a heart-carrier fixed pair and hF concerns
its forgotten carrier. The field-datum conversion preserves S's literal fields.
The curve binder retains nonempty, dimension one and connected geometric fibre.
The three explicit source-morphism instances are implied by the curve predicate.
The lisse-model condition permits a different coefficient stage and does not
require Frobenius invariance. Rank-zero and non-lisse skyscraper tests distinguish
the intended cases. The initial compile exposed missing synthesis through the
bundled geometric-fibre interface; the final helpers use standard pullback
instances and the field-datum conversion is reducible. No mathematical hypothesis
was added to repair that elaboration issue. The old upstream theorem was rejected
because its coefficient model disagrees with the recorded dependencies.

Validation: `scompile.py Q95 lem-a1-affine-hc0` compiled both delivered modules
separately in dependency order, including their sandbox and library forms. The
final run completed with exit status zero and no diagnostics or warnings. The
main node differs from the shared record only in lean and the added stmt_deps
entry, and both lean.statement signatures occur verbatim in their source files.

The first delivery dry run compiled both files successfully and found one
metadata issue: this item's blueprint ancestor is the item itself, so the new
node's blueprint.from.via must be the empty list rather than repeat that root.
The ancestry metadata has been corrected; no Lean declaration changed.

The repaired `deliver2.py Q95 lem-a1-affine-hc0 --no-push` completed with
`OK (dry run)`: preflight accepted the node records and both modules compiled.
