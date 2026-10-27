## Worker report

The module `Sheaf.SixFunctors.SupportedWeilMateLift` states
`WeilConjectures.sf_supportedWeilMateLift` and the coefficient-compatibility clause
`WeilConjectures.sf_supportedWeilMate_coefficient`. Both proofs are `sorry`.
The four owning helper declarations package this node's specified input, its literal
mate, its underlying triangle, and its conclusion. No new independent notion or
replacement coefficient category is introduced. Definitions have real data.

Source read: main-20261015/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.proof.md, final Weil-structures paragraph, together
with the complete expanded seven-step proof in the assigned node. The node is a
conditional assertion: its adjoints and supported triangles are given, rather than
asserted to exist by this lemma. The source's construction of the exceptional
operation is the parent proposition, not an extra premise of this delivery.

Hypothesis and conclusion correspondence:

- The finite field, its fixed closure, and characteristic are `D : FiniteFieldDatum`.
  `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` express the coefficient restriction.
  `E` has the field, Padic algebra and finite-dimensional instances; `Ω` has the
  field, Padic algebra and algebraic-closure instances. The two conjuncts cover
  respectively Λ=E and Λ=Ω, with independent scheme and closure universes.
- `X₀,Z₀,U₀ : Over (Spec (.of D.k₀))`, their finite-type instances, and the
  separatedness instance on X₀ express the schemes in the question. Finite type
  on the closed and open subschemes follows geometrically from the stated pair
  (finite-type schemes over a field are Noetherian, so their opens are qc).
  `i₀,j₀`, the immersion instances, and `_complement` express the pair. The
  recorded `fieldWeilPull`/`zlPull` use the actual geometric-fibre map.
- `SfSupportedWeilInput` has iPush, exceptional=J and jPush=Rj*, with `ip`=i*,
  `jp`=j*, and the three adjunction fields. `closedCounit` and `openCounit`
  express the invertible counits; `closed_open_zero` says j*i*=0 with i* here
  meaning the closed pushforward iPush (namely jPull(iPush M) is zero).
- Shift data for all eight functors and their exactness are explicit fields.
  The three `Adjunction.IsTriangulated` fields require their units and counits
  to commute with those shifts. `dShift,djShift,rShift` retain the prescribed
  pullback and open-direct-image comparison shifts.
- The endofunctors are precisely `sfWeilFrobeniusPullback` and
  `sfCommonStageWeilFrobeniusPullback`. The pullback squares are precisely
  `fieldWeilPullSquare` and `zlFrobeniusSquare`, not arbitrary isomorphisms.
  `a_mate` fixes the closed comparison to `mateEquiv closedAdj closedAdj d.inv`.
  The open comparison `r` is given; `openUnit` is its required unit equation.
- `boundary`, `distinguished`, and `unique_middle` are the supplied supported
  triangle and its uniqueness on morphisms with prescribed middle component.
  `sfSupportedWeilTriangle` retains exactly the counit, unit and boundary.
- The first conjunct of `SfSupportedWeilConclusion` is `∃! b` satisfying the
  counit normalization. The second conjunct uses that same unique normalized
  isomorphism via `b.hom = sfSupportedWeilMate S` and the three-factor formula.
  `NatTrans.CommShift b.hom ℤ` is exact-shift compatibility for every integer.
- The existential lifted adjunction uses the existing `IsoAlgebra.mapOfNatIso`
  functors. The unit and counit equalities fix their underlying arrows to the
  original adjunction maps; therefore both are equivariant. The following
  equation says that the underlying Hom bijection intertwines conjugation by
  the source and target Frobenius structures, on every underlying Hom arrow.
- For each `K : IsoAlgebra P`, the unique triangle isomorphism has middle
  component `K.str.hom`. Its first component is a followed by iPush of the mate
  structure, and its third is r followed by Rj* of the prescribed j* structure.
  Being a triangle morphism includes all three commuting squares, including
  the shifted boundary. Applying ip and conjugating by any isomorphism whose
  hom is the closed counit gives exactly `b_K` followed by J(theta_K).
- The final two clauses give the action of the lifted J on every Weil arrow,
  its intertwining equation, and naturality of the unique triangle comparison
  against the unique supported-triangle morphism with that middle arrow.
  All triangles are `Triangle X`; no triangulation of fixed pairs is used.
- `sf_supportedWeilMate_coefficient` is the coefficient clause, universally
  quantified over the given comparison functors and invertible comparison
  squares. `_counit` is preservation of the exceptional counit and `_closed`
  is commutation of the prescribed closed Frobenius comparison. The conclusion
  is the literal b/scalar/Frobenius square. The given comparisons that preserve
  all adjunction maps and triangles satisfy these two hypotheses. This universal
  square includes each given identity comparison and each direct or composite
  comparison in a tower; the original coherence data are unchanged, and no new
  choice of comparison can disturb them. This theorem also covers finite-stage
  inclusions into the common-stage category. It states the necessary equality
  rather than assuming the desired b-compatibility.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient conventions
  and its imported field/valuation-ring constructions; no duplicate coefficient ring.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback` and their uniquely normalized object/morphism actions.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and
  its inherited pretriangulation; no Karoubi completion.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its common-stage structure.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`; `sfWeilComplex` and its common-stage
  analogue are definitionally the `IsoAlgebra` types used here.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `mateEquiv_counit`;
  `Mathlib.CategoryTheory.Triangulated.Adjunction`: exact adjunctions, together
  with `Triangle`, `distTriang`, `Functor.mapTriangle`, `NatTrans.CommShift`.
- `Sheaf.Paper.FieldWeilShriekShiftData`: `fieldWeilPull`, `fieldWeilPullSquare`;
  `Sheaf.Paper.WeilIndSheafCategory`: `zlPull`, `zlFrobeniusSquare`. The already landed Weil-ind-sheaf owner and the
  triangulated-category owner were added to stmt_deps. The field-Weil owner is
  reached through the recorded imports; its additional direct edge was omitted
  because it would close a dependency cycle. No existing field is removed.
- Proof imports: `AutomorphismConstructibleStageEquivalence`,
  `MateIsoAlongEquivalences`, and the recorded
  upstream `IsoAlgebraAdjunction`. Their signatures and docstrings were read.
  Mate pasting and pretriangulated completion are in the imported Mathlib modules.
  The convention node for scheme properties has no module; its named Mathlib
  immersion, finite-type and separatedness classes are used directly.

Edge cases checked: the empty closed subscheme and empty open complement impose
no nonempty hypothesis; zero objects and zero Weil pairs are admitted. Identity
Frobenius structures and arbitrary intertwining arrows are included. The shift
statement quantifies over all integers (including zero and negatives), and the
triangle uses shift one. Coefficient comparisons may be identities or composites;
no proper extension or nonidentity assumption is made. Ω's universe is independent.
The inverse orientation in the mate was checked against `mateEquiv_counit` and
against the source formula: b goes QJ→JP and transposes to a inverse followed by Pe.

Searches made (2026-10-23):

- msearch leanfinder: `Frobenius equivariant closed right adjoint supported triangle
  unique mate lift Weil complexes`: eight generic adjunction/triangulated/monoidal
  results; none state this lemma.
- msearch leansearch: `unique Frobenius equivariant right adjoint mate closed
  supported triangle`: eight right-adjoint-uniqueness results; none contain the
  supported triangle, fixed-pair and coefficient clauses.
- msearch loogle: `CategoryTheory.mateEquiv,
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`: no combined hit;
  the latter is project upstream, not Mathlib.
- msearch grep in Mathlib CategoryTheory/Adjunction:
  `supported.*[Ww]eil|[Ww]eil.*[Mm]ate|mateEquiv`: five mateEquiv hits, reused.
- rg in both lean/WeilConjectures and lean/Sheaf for supported/Weil/mate words
  and the exact new declaration names. No exact existing statement. The related
  `SupportedTriangleMateIdentification` is finite-coefficient étale scalar support
  comparison, with no Frobenius fixed-pair or all-stage assertion. The existing
  open-closed mate statement concerns the other localization triangle and was
  retained as a proof dependency. Exact item-id search in WeilConjectures had no hit.

No statement correction, disputed statement, new node, or dependency repair.
Compilation uses only the prescribed scompile.py server wrapper.

## Second reading by Q131

A separate second pass by the assigned worker, with the JSON node and final Lean
open, was made under the dispatcher's explicit prohibition on starting other agents;
this is not claimed to be an independent second worker's review. The maintainer's
independent review remains required.

The pass checked the full finite-field and coefficient binders, immersion pair,
canonical P/Q/H and d/dj, all adjunction/counit/zero/triangle hypotheses, and each
conclusion as mapped above. It found that the first draft's triangle `∃!` included
extra component conditions in the uniqueness predicate. This was changed to
uniqueness under the middle component alone, followed by assertions about every
such comparison's outer components. It also added the explicit naturality square
on supported-triangle morphisms, so functoriality is asserted for both J and its
triangle comparison. The coefficient square was checked component by component
for its domains and against the normalized exceptional counit. The three-factor
mate uses a inverse; the recovery formula uses d in its stated direction and the
inverse/forward closed counit in the proper order. No object data uses sorry, and
only the two named theorems postpone proofs. No new mathematical fault remained.

## Delivery validation

The resumed worker retained the saved Lean and node packet and first ran the
prescribed deliver2.py --no-push. On 2026-10-23 it passed the current server
preflight and every per-file compilation, producing dry-run commit a5ba3ee26c8.
The inherited-cycle rejection from the earlier attempt no longer occurs.

The required self-check reopened the final Lean, the node statement and proof,
and the blueprint's final Weil-structures paragraph. It checked the two literal
coefficient cases, the canonical pullback comparisons, the adjunction inputs,
the normalized mate formula, the Hom action, the underlying triangle comparison
and its naturality, and the universal coefficient square against the report's
clause correspondence. It verified that the main signature in lean.statement is
verbatim, that only lean and the two added landed stmt_deps differ from the read
repository, and that the only two sorry occurrences are the two named theorems.
All definitions have explicit data. No Lean or node change was needed on retry.
The omitted open/closed mate proof import remains omitted to avoid an import cycle,
as allowed by stages/2-statements.md §3.7; its accepted DAG proof edge is retained.
