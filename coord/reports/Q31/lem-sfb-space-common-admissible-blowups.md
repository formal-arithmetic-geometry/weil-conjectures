## Worker report

Stage 2 statement of `lem-sfb-space-common-admissible-blowups`, preserving the
accepted Q114 stage-1 split. The inherited BLOCKED ending was a stage-1 unchanged-item
rejection, not a stage-2 blocker: the current node has no Lean attachment and appears
in `coord/queue.tsv` at stage 2. No released repair note is present for this item.

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommonAdmissibleBlowups` states
`AlgebraicGeometry.AlgebraicSpace.exists_common_admissible_blowups`. Its only theorem
proof is `sorry`. There are no new definitions, axioms, helpers or dependency repairs.
The mathematical statement and its proof split are unchanged. Four already landed
definition nodes are added to `stmt_deps` to record the interfaces now used.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-find-common-blowups`, Tag 088Q, statement and complete proof including the
four-part diagonal footnote; `spaces-divisors.tex`, definition-blow-up (085Q),
lemma-blowing-up-affine (085R), and definition-admissible-blowup (086B).

Hypothesis and conclusion correspondence, clause by clause:

- The base scheme S is `{S : Scheme.{u}}`; all spaces are `AlgebraicSpace S`.
  `universe u` is explicit and `autoImplicit` is false. The site's objects retain
  universe u+1 and its section rings universe u, as in the recorded space framework.
- B is quasi-compact: `hBqc` supplies a surjective representable etale atlas
  `a : yoneda.obj V ⟶ B.obj.obj` with `CompactSpace V.left`, exactly the node's
  atlas definition. This is absolute quasi-compactness, with no condition on S.
- B is quasi-separated: `hBqs : IsAbsolutelyQuasiSeparated B`, the recorded
  equivalent affine-test condition for its absolute diagonal, independent of S.
- X₁, X₂ and U are spaces over B: `x₁`, `x₂`, `v` give their structure morphisms.
  The six hypotheses `hx₁s`, `hx₁ft`, `hx₂s`, `hx₂ft`, `hvs`, `hvft` use precisely
  `MapIsSeparated` and `MapIsFiniteType` for these three maps, with none omitted.
- The maps `j₁`, `j₂` are representable open immersions: `hj₁`, `hj₂` test
  `AlgebraicGeometry.IsOpenImmersion p.left` on every scheme base change via the
  recorded `IsRepresentableWith`. The equations `hj₁B`, `hj₂B` say they are over B.
- The centre ideals are `I₁ : QuasiCoherentIdeal X₁`, `I₂ : QuasiCoherentIdeal X₂`.
  These are actual subobjects of the respective structure modules with the existing
  quasi-coherence predicate. The first two conjuncts require
  `(Iᵢ.val : Xᵢ.Modules).IsFiniteType`, Mathlib's local finite generation predicate.
- The two universal chart clauses express `jᵢ^* Iᵢ = O_U`: on every etale chart V
  whose map factors through jᵢ, `idealSectionImage Iᵢ.val.arrow V = ⊤`. This is the
  sectionwise expansion of the existing `IdealIsUnitAbove` condition for a given
  open immersion U → Xᵢ, rather than an OpenSubspace supplied as a subfunctor.
  An ideal inclusion is a monomorphism, so its section image is already an ideal;
  taking its ideal span changes nothing. These charts cover U and its restrictions,
  so the condition is exactly equality of the restricted ideal with O_U.
- `D₁ : BlowupPresentation I₁`, `D₂ : BlowupPresentation I₂` specify Xᵢ' and pᵢ:
  `Dᵢ.space`, `Dᵢ.projection`. This existing structure requires their pullbacks
  to every affine etale chart to be the ordinary scheme blowup of the given ideal.
  It therefore specifies exactly the descended relative Rees Proj, up to isomorphism
  over Xᵢ. There is no independently chosen centre or unconstrained projection.
- `W : AlgebraicSpace S` and `w : W ⟶ B` supply W over B. The conjuncts
  `MapIsSeparated w` and `MapIsFiniteType w` are both required.
- The maps `e₁`, `e₂` are representable open immersions, with the same scheme-test
  predicate as jᵢ. The two equations `eᵢ ≫ w = Dᵢ.projection ≫ xᵢ` say they are over B.
- `s₁`, `s₂` are open immersions from the original U to the two blowups. Each has
  its own representable open-immersion condition. The squares
  `IsPullback sᵢ (𝟙 U) Dᵢ.projection jᵢ` say that U is the entire inverse image
  pᵢ⁻¹(jᵢ(U)), identified by sᵢ. Their commutativity is exactly `sᵢ ≫ pᵢ = jᵢ`.
  Together with the preceding equations it also makes sᵢ a morphism over B.
- Finally `s₁ ≫ e₁ = s₂ ≫ e₂` is the common-open compatibility in W. There is no
  density hypothesis, joint-cover requirement on eᵢ, or extra property of W.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `.IsEtale`, `.IsSurjective`, `.EtaleSite`,
  `.structureSheaf`, `.Modules` (the space and site definitions are reused).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `.IsClosedImmersion`, used
  by the recorded separation predicate, and `.IsClosedImmersion.of_isPreimmersion`
  for the Mathlib proof-dependency leaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsFiniteType`, `MapIsSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its existing
  `SheafOfModules.IsQuasicoherent` predicate; no private quasi-coherence notion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`: `idealSectionImage`, owned by
  the landed definition node `def-sfb-space-ideal-power-products`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`:
  `blowupChartIdeal`, `BlowupPresentation`, `IdealIsUnitAbove` (the last is expanded
  for an open with a specified source U). Its chart ideals use actual restrictions
  on every affine open, and the same `WeilConjectures.Blowup.Gluing` declarations
  `Scheme.IdealSheafData.blowup` and `.blowupMap` recorded for scheme blowups.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType`, local finite generation with no Noetherian assumption.
- `def-weil-size-convention` has no declaration; it is rendered by explicit universes.

The four added, already landed statement dependencies are
`def-sfb-space-quasi-coherent-ideal`, `def-sfb-space-absolute-quasi-separated`,
`def-sfb-space-ideal-power-products`, and `def-sfb-space-blowup-presentation`.
Their existing node records and full source declarations were read; none is delivered
again. The recorded public modules cover all original statement dependencies.

Plain imports retain the proof-dependency modules which have recorded declarations:
`AlgebraicSpaceFourPropertyFppfDescent`, `SpaceFiniteTypeComposition`,
`AlgebraicSpaceComposeAdmissibleBlowups`, `SchemeEtaleSourceTargetProperties`, and
Mathlib's `ClosedImmersion`. The other proof nodes have no Lean or Mathlib attachment
on the read base; their ids and complete mathematical role remain in the proof docstring.
No missing proof theorem was invented as an extra hypothesis.

Edge cases checked before writing and again on rereading:

- U empty: the unit restriction condition is vacuous on nonempty charts and true
  on the empty chart, whose ring is zero. Identity blowups and a disjoint union of
  the Xᵢ give the expected existence. No Nonempty or density binder excludes this.
- U = Xᵢ: admissibility forces the unit ideal there, and its blowup is the identity;
  the statement includes this case with the canonical pullback square.
- Xᵢ or B empty: no assumption requires nonempty spaces or a nonempty atlas.
- Unit centre: its scheme blowup is the identity on every chart. Zero or nilpotent
  centre: its Rees Proj can be empty; the existing presentation does not exclude it.
- Non-Noetherian, nonreduced spaces and a non-quasi-separated S remain allowed;
  no coherence, density, noetherianity or separatedness over S was added.
- The atlas scheme and every affine chart range over `Over S` in the same universe
  as the original framework; no universe equality or smaller test universe is imposed.

Searches for an exact existing statement and the notions it needs:

- `msearch.py ... leanfinder "Common admissible blowups of two separated finite type
  algebraic spaces sharing an open subspace embed in a separated finite type algebraic
  space"`: eight scheme separation hits, no common algebraic-space modification result.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace,
  AlgebraicGeometry.Scheme.IdealSheafData.blowup"`: no hits; AlgebraicSpace unknown
  to the Mathlib-only service. The source scheme blowup is used through the existing
  landed presentation, not treated as a Mathlib algebraic-space construction.
- `msearch.py ... grep "IsBlowup|algebraic.space.*blowup|SpaceBlowup"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "Blowup of an algebraic space defined by ordinary
  blowups on affine etale charts"`: scheme/etale hits, no space blowup notion.
- `msearch.py ... leanfinder "blowup algebraic space quasi coherent ideal etale
  descent"`: eight scheme/etale hits, no algebraic-space blowup result.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `blowup|Blowup`, the item id, `exists_common_admissible_blowups`,
  `BlowupPresentation`, and common-modification terms: upstream
  `Compactification/CommonModification.lean` is for schemes over a qcqs scheme,
  not arbitrary algebraic spaces over B. No exact theorem match exists. Reading
  the recorded composition proof dependency located the landed general
  `AlgebraicSpaceBlowupPresentation.lean`, which is reused.
- `tools/blueprint_refs.py search blowup`: existing scheme and specialized blowup
  nodes; the subsequent direct DAG/source check found the landed space-presentation
  definition. No new node is needed. A tentative sandbox chart helper was removed
  before delivery to avoid duplicating that definition.

No STATEMENT-DISPUTED flag or mathematical correction is needed. The preserved
stage-1 split supplies the proof plan; the statement matches Tag 088Q and the
node's explicit canonical-open clauses.

## Second reading by Q31

The dispatcher explicitly prohibited starting other agents, so this is a fresh
second pass by the same worker, not a claimed independent review. The maintainer's
independent delivery reader remains separate.

I reopened the node, the complete signature and the landed presentation definitions.
Checked each of the six separation/finite-type assumptions separately; checked the
base's absolute qcqs conditions, both jᵢ being open and over B, both finite-type
quasi-coherent centres and both unit restrictions. Checked that each Dᵢ includes its
projection and scheme blowup charts for precisely Iᵢ, that W has both required
properties, and that both embeddings are open and over B. Finally checked both open
sᵢ and the pullback-square orientations: their top-left and bottom-left are U,
their right maps are pᵢ, and bottom maps jᵢ. Thus commutativity reads sᵢ ≫ pᵢ = jᵢ,
not the reverse composition, and cartesianness gives the full preimage, not merely
an arbitrary lift. The final equality uses the same U on both sides. No density or
covering conclusion was introduced. No signature change was needed in this pass.
The report records explicitly why the sectionwise unit clauses and presentation
existentials are equivalent to the node's ideals and blowup objects.

Validation: the final module was compiled with the prescribed `scompile.py`, both
as its sandbox module and at its library module name. It passed without errors or
unexpected warnings. Delivery dry-run and final delivery results follow below.

`deliver2.py Q31 lem-sfb-space-common-admissible-blowups --no-push` returned
`OK (dry run): commit ac3052d4fa8 passes the preflight and compiles; nothing pushed`.
The final signature, including the explicit Mathlib proof-leaf import, passed the
wrapper's separate sandbox and library-name compilation. No remaining preflight fault.
