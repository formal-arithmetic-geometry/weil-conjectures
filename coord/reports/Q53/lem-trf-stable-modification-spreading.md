## Worker report

Repaired the retained packet returned at immutable head
`fbac4a3a9cba8d670b0b739ee3ce016fa3992c2e`. The saved packet's initial
`deliver2.py Q53 lem-trf-stable-modification-spreading --no-push` passed
mechanical preflight and compilation as dry-run commit `9720409773`. That did
not resolve its mathematical return: all six findings have now been repaired.
The sandbox node was compared with current shared main: outside `lean`, the
only difference is the retained addition of the two existing definition nodes
`def-trf-multipointed-curve` and `def-trf-multipointed-curve-modification` to
`stmt_deps`. The natural statement and proof are unchanged.

The module `Sheaf.TraceFormula.StableModificationSpreading` states
`AlgebraicGeometry.stable_modification_spreading`, with the sole theorem proof
`sorry`. Its auxiliary `AlgebraicGeometry.BaseChangePair` is the retained
presentation of a multipointed curve's base change by actual isomorphisms to
Mathlib pullbacks, preserving both structure maps and the marking inclusion.
It has real fields, no chosen unknown data and no postponed helper theorem.

Clause-by-clause rendering of the node, including the inline definitions:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Integral base of finite type over the integers | `T : Scheme.{u}`, `[IsIntegral T]`, `t : T ⟶ Spec (.of (ULift.{u} ℤ))`, `[LocallyOfFiniteType t]`, `[QuasiCompact t]`. Finite type is the conjunction of the last two properties. |
| Separable closure of the function field | `L : Type u`, `[Field L]`, `[Algebra T.functionField L]`, `[IsSepClosure T.functionField L]`. |
| RZ point for the specified generic map and its valuation ring | `η` with `hη : η = Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫ T.fromSpecStalk (genericPoint T)`; `x : RiemannZariski.Point T L η`, `v : RiemannZariski.ValuationPoint T L η`, and `hx : RiemannZariski.Corresponds x v`. The equality constrains the named map to the canonical one; it adds no mathematical restriction beyond the node's generic map. `v.V` is a valuation subring of the given `L`, and `v.fac` fixes its generic restriction. |
| Multipointed curve | `P : MultipointedCurve T`. Its `x`, `d`, `i`, and `comm` give the two structure maps and marking inclusion. `flat_X`, `flat_D`, the `lfp`, `qc`, `qs` fields, `pure_X`, `pure_D`, and `closed` give flatness, full finite presentation, pure fibre dimensions 1 and 0, and a closed immersion. |
| Smooth generic curve, etale generic marking | `hgenX : Smooth (P.x.fiberToSpecResidueField (genericPoint T))` and the analogous `hgenD : Etale ...`. |
| Specified source and base-changed target over the valuation ring | `PV : MultipointedCurve (Spec (.of v.V))`, `QV : BaseChangePair P v.centre`. `QV.curveMap` and `QV.markingMap` are isomorphisms onto the canonical pullbacks, preserving the structure maps and marking. |
| Specified compatible pair map | `f : MultipointedCurve.Hom PV QV.pair`, including `curve_over`, `marking_over`, and `comm`. |
| Specified stable eta-modification | `hf : f.IsStable (Spec.map (CommRingCat.ofHom v.V.subtype))`. The argument is now the canonical `Spec L → Spec V`, not the identity of `Spec V`. Thus only the generic fibre must be an isomorphism. |
| Proper modifications and schematic density | The imported `Hom.IsEtaModification`, included in `IsStable`, imposes properness of both maps, an isomorphism over opens schematically dense in both source and target, and the two generic-fibre isomorphisms. Schematic density is injectivity on sections on every open. |
| Semistability and stability | The imported `IsStable` requires `PV.IsSemistable`, respectively `Y.IsSemistable` below, with geometric nodal fibres, etale marking and marking in the relative smooth locus; it excludes contracted geometric projective-line components meeting marking plus singular points in at most two points. The existing predicate uses the recorded geometric fibres, maximal-ideal adic completion, two-variable power series, and pure topological dimension. |
| Integral L-quasi-model | `∃ U : RiemannZariski.QuasiModel T L η`. The structure includes integrality, separated finite type over `T`, a generic map taking the point to `genericPoint U.X`, and its factorization to `η`. |
| Compatible valuation lift | `∃ lift : Spec (.of v.V) ⟶ U.X`, followed by `lift ≫ U.map = v.centre` and `Spec.map (CommRingCat.ofHom v.V.subtype) ≫ lift = U.generic`. This same bound lift is used by the later recovery clause. |
| Stable descended modification | `Y : MultipointedCurve U.X`, `QU : BaseChangePair P U.map`, `g : MultipointedCurve.Hom Y QU.pair`, and `g.IsStable U.generic`. |
| Pullback recovers the prescribed curve and marking over Spec V | `∃ eX : pullback Y.x lift ≅ PV.X`, `eD : pullback Y.d lift ≅ PV.D`, with `eX.hom ≫ PV.x = pullback.snd Y.x lift` and the analogous marking equation. |
| Recovery preserves the closed marking inclusion | `eD.hom ≫ PV.i = Y.markingBaseChange lift ≫ eX.hom`. The right-hand marking arrow is the dependency's canonical pullback map. |
| Recovery of the prescribed curve map | `eX.hom ≫ f.curve ≫ QV.curveMap ≫ pullback.fst P.x v.centre = pullback.fst Y.x lift ≫ g.curve ≫ QU.curveMap ≫ pullback.fst P.x U.map`. |
| Recovery of the prescribed marking map | The corresponding equation with `eD`, `f.marking`, `QV.markingMap`, `Y.d`, `g.marking`, `QU.markingMap`, and `P.d`. |
| One common dense base open and generic-fibre containment | `∃ Uo : U.X.Opens`, `Dense (Uo : Set U.X) ∧ genericPoint U.X ∈ Uo ∧ IsIso (g.curveBaseChange Uo.ι) ∧ IsIso (g.markingBaseChange Uo.ι)`. These are both maps after base change to the same open of the base. They identify the restrictions over the preimages under the respective target structure maps. Generic-point membership means the inverse images contain the entire generic fibres of source and target. |
| RZ neighbourhood contains x | `RiemannZariski.ValuationPoint.LiftsTo v U`, together with `hx`, using the point correspondence and open-image characterization of `finite_refinement`. |

The two recovery equations use projections, not arbitrary target comparison
maps. To see precisely that they express the required canonical comparison,
put `a = QU.curveMap ≫ pullback.fst P.x U.map`. The canonical comparison from
the iterated target pullback to `pullback P.x v.centre` has projections
`pullback.fst QU.pair.x lift ≫ a` and
`pullback.snd QU.pair.x lift`; their compatibility follows from
`QU.curveOver`, `pullback.condition`, and `lift ≫ U.map = v.centre`.
The displayed curve-map equation equates the first projections of the two
maps from `pullback Y.x lift` to `pullback P.x v.centre`. The second
projections agree by the structure-map equation for `eX`, `f.curve_over`,
`QV.curveOver`, and the canonical base-change projection identity for `g`.
The pullback universal property therefore gives equality of the maps into
the full target pullback. The marking equation does exactly the same for
`P.d`. The target presentations are isomorphisms, so these are also equalities
under the canonical iterated-pullback isomorphisms. No extra arbitrary map,
existence assumption or separately chosen target comparison is used. This
is the projection-based presentation already used in the landed
`exists_stable_modification_finite_presentation_spread` conclusion.

Dependency declarations read and used:

- `Sheaf.TraceFormula.MultipointedCurve`:
  `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `Hom.IsStable`, `Hom.IsEtaModification`,
  `Hom.curveBaseChange`, `Hom.markingBaseChange`, `markingBaseChange`,
  `IsSemistable`, `specialPoints` (all in `AlgebraicGeometry`).
- `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`:
  `RiemannZariski.GenericScheme`, `QuasiModel`, `Point`, `ValuationPoint`,
  `Corresponds`, `ValuationPoint.LiftsTo`, and `finite_refinement`.
- `Sheaf.AlgebraicGeometry.StableModificationFinitePresentationSpread`:
  `AlgebraicGeometry.exists_stable_modification_finite_presentation_spread`,
  imported for the first and third proof steps.
- `Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange`:
  `AlgebraicGeometry.MultipointedPair.isMultipointed_baseChange` and
  `generic_smooth_etale_baseChange`, imported for the second proof step.
  The other proof dependency, `lem-trf-stable-modification-stability-locus`,
  currently has no Lean record in shared main; its node is named in the
  complete proof docstring and there is no unavailable-module import.
- The recorded Mathlib component notions: `IsIntegral`, `Smooth`, `Etale`,
  `LocallyOfFinitePresentation`, `LocallyOfFiniteType`, `QuasiCompact`,
  `Flat`, `IsClosedImmersion`, `IsProper`, `CategoryTheory.Limits.pullback`,
  `AdicCompletion`, `MvPowerSeries`, and `topologicalKrullDim`. Their
  signatures and uses in the existing curve/modification interfaces were read.

The theorem docstring now follows all four node proof steps: prescribed
finite-presentation descent; generic smooth/etale base change and stable-locus
refinement followed by composition of quasi-models; the prescribed-model
comparison preserving both maps and marking; and the RZ image and common
open's generic-fibre containment. Source checked: [Temkin, Stable Modification
of Relative Curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
§1.2, §3.1 and Remark 3.1.1(ii), Lemma 3.2.2, Lemma 5.1(ii), and the second
paragraph of the proof of Theorem 1.5 (printed p. 36). The source retains the
chosen valuation model when approximating it, then arranges stability. Its
eta condition concerns the fraction-field fibre.

Edge cases checked against the repaired signature: empty marking (also an
empty curve) is allowed; pure dimensions are vacuous on empty fibres; the
original curve may be nonseparated and nonproper; there is no characteristic
restriction, no restriction on valuation height or rank, and no requirement
that the valuation be nontrivial. For height zero, the generic map and identity
agree up to isomorphism; this previously concealed finding 1. For a nontrivial
valuation, nontrivial modifications on special fibres are now allowed because
`hf` only requires generic isomorphisms. The identity modification is allowed,
but the recovery equations also retain arbitrary prescribed nontrivial models.
The two isomorphisms identify the closed inclusion even for empty markings.
The same base open works for both maps, including when a marking fibre is
empty. All universes and variables are explicit with `autoImplicit false`.

Search evidence retained from the original packet (the review found no H4
fault); the searches were not restarted on repair:

- `msearch.py Q53 lem-trf-stable-modification-spreading leanfinder` with query
  "A stable modification of a multipointed relative curve over a valuation ring
  spreads to a generically etale quasi alteration neighbourhood of the valuation
  point": 8 hits, headed by `AlgebraicGeometry.ValuativeCriterion.existence`
  and etale infrastructure; no match.
- The same tool with `leansearch`, query "Constructibility of stable fibres of a
  modification of marked curves and finite presentation approximation of its
  stable model": 8 finite-presentation/base-change hits; no match.
- The same tool with `loogle`, query `"ConstructibleSet"`: 12 hits for
  `PrimeSpectrum` constructible-set infrastructure; no stable spreading result.
- The same tool with `grep`, query
  `stable.modification|exceptional.component|semistable`: no Mathlib hit.
- The original `rg` searches in `WeilConjectures/` and `lean/Sheaf/` found the
  existing multipointed-curve, modification and RZ interfaces, no duplicate.
  During repair, repeated `rg` for `BaseChangePair`,
  `stable_modification_spreading`, and the item ID in upstream, side sources
  and Mathlib algebraic geometry. No duplicate declaration was found. The
  related landed finite-presentation theorem was read and reused as a proof
  import and as the precise projection-equation convention for recovery.

Validation after the repair:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q53 lem-trf-stable-modification-spreading /home/ubuntu/weil-newtargets-stage2-sandbox/Q53/lem-trf-stable-modification-spreading/lean/Sheaf/TraceFormula/StableModificationSpreading.lean
```

Exit 0, no errors or warnings. The wrapper compiled the needed
`StableModificationFinitePresentationSpread` overlay in 2.8 s, sandbox file
in 3.1 s, and library-path file in 3.4 s, each within its 60 s limit.
Exact comparison of `lean.statement` with the theorem signature succeeds;
maximum Lean line length is 87. Only the named theorem contains `sorry`.
There is no natural-statement correction and no `STATEMENT-DISPUTED` flag.

## Second reading by Q53

Reopened the full node, repaired module and returned review, and checked every
row of the clause table against the actual signature. This is the Q53 worker's
second pass; no additional agent was started under the dispatcher's instruction.

1. Finding 1: read the actual `IsStable` and `IsEtaModification` definitions.
   Their generic-isomorphism fields now receive
   `Spec.map (CommRingCat.ofHom v.V.subtype)`. The identity of `Spec V` is
   absent. This corrects the earlier false interpretation in the report.
2. Finding 2: the bound `lift` is in scope for `eX` and `eD`, whose endpoints
   are the actual pullbacks of `Y.x` and `Y.d` and the prescribed `PV.X` and
   `PV.D`. Two structure-map equalities make them isomorphisms over `Spec V`;
   the marking equality identifies the inclusion. Both map equalities mention
   the supplied `f` and the two given target presentations `QV` and `QU`.
   Checked the canonical target comparison through both pullback projections
   as detailed above; the equations retain the full prescribed pair map,
   rather than only isomorphism classes of its source schemes.
3. Finding 3: the existential open is now `Uo : U.X.Opens`, with both density
   and `genericPoint U.X ∈ Uo`. The two isomorphism predicates apply to
   `g.curveBaseChange Uo.ι` and `g.markingBaseChange Uo.ι` for this very same
   open. These are the restrictions required by the node; inverse images
   contain all generic fibres because the open contains the generic point.
4. Finding 4: `hη` identifies the formerly free map with the exact canonical
   expression in `RiemannZariski.finite_refinement`. All RZ objects, the valuation
   centre, `hx`, and the resulting quasi-model are indexed by that same map.
5. Finding 5: the docstring now has the node's four steps and names all their
   cited nodes. In particular Step 2 checks generic smoothness/etaleness and
   composes the two quasi-models, Step 3 recovers both prescribed arrows and
   the marking, and Step 4 accounts for the common open and RZ neighbourhood.
6. Finding 6: replaced the prior inaccurate report and second reading with
   the actual clause audit and item-specific compiler evidence above. The
   integral finite-type base, separable closure, multipointed structure,
   generic smooth/etale assumptions, stable source and descended map are
   unchanged in meaning. The repairs restore the four missing or misrendered
   clauses without changing the node's natural statement. Checked the empty,
   trivial-valuation, nontrivial-special-fibre, and nonproper/nonseparated
   cases, explicit binders, real helper data, exact signature record, source
   tags and line lengths. Clean per-file compilation is recorded above.
