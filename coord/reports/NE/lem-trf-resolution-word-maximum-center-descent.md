## Worker report

Item: `lem-trf-resolution-word-maximum-center-descent` (NE, stage 2).

The module `Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent` states
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_maximum_center_descent`.
Its only proof is `by sorry`. The real helper definition
`EmbeddedResolutionHistory.ResolutionWordChart.finalMap` composes the recorded
final intrinsic chart map with the equality transport from `C.last`; it introduces
no chosen scheme or arbitrary map. Both declarations are listed in `lean.declarations`.
The item's node changes only in `lean`. There are no new nodes, dependency repairs,
or statement corrections.

Sources read: the node and all its statement dependencies; ILO, Travaux de Gabber,
Exposé VIII 2.3.11 and 2.3.13, printed pp.93–94 (PDF pages 99–100), including the
regular centers in the singular locus and the synchronization caveat for arbitrary
smooth morphisms. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md`
is the Frobenius local-vanishing unit: this node is a subordinate historical
resolution input, not that unit's statement. The existing local-presentation,
normalized-word, engine and history source modules were read in full at the relevant
interfaces. The proof docstring follows the node's seven steps, with its cited
Noetherian, reduced-descent, regularity and coherence inputs.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Work over Q with X closed in smooth separated finite-type P and X reduced | `A : EmbeddedResolutionPair.{u}`; its fields are `X`, `P`, `base : P ⟶ Spec (.of (ULift.{u} ℚ))`, `inclusion`, `closed`, `reduced`, `smooth`, `separated`, `finiteType`, `quasiCompact`. These are exactly the initial data, without a connectedness or dimension condition. |
| Fix the simultaneous normalized assignment of the gluing lemma | `R : MarkedIdeal.NumericalResolution.{u}`, `ν : ValueFamily.{u} HilbertSamuel.ResolutionWord`, and `hν`. The type of `hν` is verbatim the predicate on the witness `ν` in `normalized_resolution_word_gluing R`: every admissible history has charts at singular points, every chart has leading 1 and `ν G x = C.word`, finite image, closed upper levels, regular-bottom equivalence, and the common-summation order/equality clauses. No resolution calculus or center theorem is assumed. |
| Bottom at regular points; otherwise normalized head and actual marked tail with leading 1 deleted | `hν`'s regular-bottom clause and `ν G x = C.word`; the imported `ResolutionWordChart.word` is `some (toLex (normalizedHead G.X x, C.tail))`, and `C.tail` is `(R.value C.history ⟨C.supportPoint, C.cosupport⟩).drop 1`. The corresponding leading entry is explicitly `some (MarkedIdeal.rational 1)`. |
| Any finite admissible history H | `{n : ℕ}`, `H : EmbeddedResolutionHistory A n`, `hH : Admissible ν H`. The history retains actual ambient blowups, schematic strict transforms and all earlier center ideals in order. |
| Current P_H smooth, separated and finite type, current X_H reduced | `hP : Smooth H.base ∧ IsSeparated H.base ∧ LocallyOfFiniteType H.base ∧ QuasiCompact H.base`, `hX : IsReduced H.X`. These are hypotheses, not unstated properties of raw histories. |
| X_H nonregular | `hNR : ¬ IsRegularScheme H.X`, using the recorded locally-Noetherian-plus-regular definition. |
| Greatest positive word m and T its full equality locus | Existential `m`, `IsGreatest (Set.range (ν H)) m`, `⊥ < m`, and `T : TopologicalSpace.Closeds H.X` with `(T : Set H.X) = {x | ν H x = m}`. Existence/closedness are asserted, not assumed. |
| Reduced induced M = T_red in X_H | The actual existing `Scheme.IdealSheafData.vanishingIdeal T`, with `.subscheme` and `.subschemeι`. Its reduced structure and canonical immersion are supplied by the recorded reduced-induced construction, not arbitrary existential data. |
| M nonempty and regular | `Nonempty (vanishingIdeal T).subscheme` and `IsRegularScheme (vanishingIdeal T).subscheme`. Nonemptiness also entails that the maximum locus is attained. |
| Étale neighbourhoods with local Hilbert–Samuel presentations | For every `x ∈ T` there exists `C : ResolutionWordChart R H x`, and `Etale C.finalMap`. Its domain is the final local intrinsic scheme of the actual controlled presentation history. `C.pointed` and `C.last` place its distinguished point above `x`. `C.presents`, `minimal`, `maximal`, `maximalStages`, `retainedHead`, `earlierPullback`, `boundary` and `births` retain the existing local presentation and ordered exceptional information. |
| Smooth full-maximum presenting marked-word center | There exist `K : MarkedIdeal.History (C.length + 1)` and `E : MarkedIdeal.Extension C.history K` with `MarkedIdeal.IsMaximumStep R.value E`. Its definition is the nonempty full greatest-value locus on cosupport, with the same fixed engine word. The local center is the actual `(K.step (Fin.last C.length)).step.center.subscheme`; its reducedness and `Smooth (E.centerMap ≫ C.history.last.marked.j ≫ C.history.last.ambient.p)` are explicit. No completed tower or termination hypothesis enters. |
| Normal crossings with ordered exceptional data | `HasAdaptedNormalCrossingsCenter (E.centerMap ≫ C.history.last.marked.j).ker (fun i ↦ C.history.last.ambient.boundary.get i)`. This applies the recorded adapted-center condition to the actual transported ambient center ideal and the ordered boundary, allowing centers contained in exceptional components. It is not a transversality assertion about every component. |
| Scheme-theoretic pullback of M equals the local center | An actual closed immersion `i` from that center into `C.history.last.ambient.X`, the equation `i ≫ C.history.last.ambient.i = E.centerMap ≫ C.history.last.marked.j`, and an actual `c` to M with `IsPullback i c C.finalMap (vanishingIdeal T).subschemeι`. |
| Reduced ideal structures, not just point sets | In addition to the pullback square, the equality `i.ker = (vanishingIdeal T).comap C.finalMap` explicitly identifies quasi-coherent ideals. The local center is explicitly reduced. The ambient defining ideal is the kernel of the composite closed immersion of this same M; it is not a different center selected from its support. |
| No regular point in T | `∀ x ∈ T, ¬ IsRegularLocalRing (H.X.presheaf.stalk x)`. |
| No irreducible component contained in T | `∀ Z ∈ irreducibleComponents H.X, ¬ Z ⊆ (T : Set H.X)`, using Mathlib's maximal irreducible subsets. |
| No nonempty open subset | `interior (T : Set H.X) = ∅`, exactly the equivalent topological formulation. |
| Coherent defining ideals in X_H and P_H | `RingedSpace.IsCoherent H.X.toRingedSpace (vanishingIdeal T).toModules` and `RingedSpace.IsCoherent H.P.toRingedSpace ((vanishingIdeal T).subschemeι ≫ H.inclusion.app (op (Fin.last n))).ker.toModules`. The latter is the actual composite M → X_H → P_H. |

Dependency declarations reused (module → declaration/interface):

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` → `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties` → `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` → `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` → `IsSeparated` (the initial-pair module publicly imports it).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact` → `LocallyOfFiniteType`, `QuasiCompact` (publicly exposed through the existing interfaces).
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory` → `EmbeddedResolutionHistory`, `.ValueFamily`, `.Admissible`, `.X`, `.P`, `.base`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` → `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing` → `normalized_resolution_word_gluing`, `HilbertSamuel.ResolutionWord`, `sumResolutionWord`, `ResolutionWordChart`, `.word`, `.tail`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` → `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, using the existing `vanishingIdeal` construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` → `Etale` (exposed through the presentation modules).
- `Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels` → its public `HilbertSamuelLocalPresentations` declarations, including `local_presentations`, `local_minimal_presentations`, `presentation_full_maximalOrder`, `presentation_history_comparison`.
- `Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine` → `MarkedIdeal.exists_numerical_resolution`, with its public `NumericalResolution`, `History`, `Extension`, `IsMaximumStep` interfaces.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` and `WeilConjectures.AlgebraicGeometry.Coherent` → the recorded exact `RingedSpace.IsCoherent` predicate and existing ideal `.toModules`.

All stated proof dependencies are exposed through the statement imports or explicitly
imported without `public`: `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.RingTheory.Noetherian.Basic`, `Mathlib.RingTheory.Localization.Submodule`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`,
`Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent`,
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.RingTheory.FlatUnderRegular`,
`WeilConjectures.RingTheory.SerreCriterionReduced`, and
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.

Edge cases checked before finalizing:

- The empty or regular current scheme does not satisfy `hNR`; the theorem makes no
  spurious positive-center claim in these cases. The assignment and histories themselves
  continue to allow both. The zero-length history is included (`n = 0`).
- Reducible, disconnected and mixed-dimensional schemes are allowed. There is no
  equidimensionality, fixed dimension bound, or constant-relative-dimension binder.
- Zero and unit ideals remain allowed in the engine interface. A global positive maximum
  point forces a nonempty cosupport in the selected chart; empty-center charts away from
  the maximum need no nonempty local model. Pullbacks are not assumed surjective globally.
- Normal crossings allows the center to lie inside exceptional divisors; it is not
  replaced by transversality. The boundary list retains its actual order and birth history.
- All schemes use the arbitrary universe `u`, and the rational base is `ULift.{u} ℚ`.
  The alphabet has its already recorded fixed universe. No relation between independent
  site/coefficient universes is introduced. `autoImplicit` is false.
- Ideal equality and a cartesian square rule out a merely set-theoretic or thickened
  center identification. Both coherence conclusions use Stacks coherence, not only
  quasi-coherence or finite presentation.

Searches actually run with `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

1. `leansearch`: “The full maximum stratum of a normalized desingularization word is
   regular nowhere dense and has coherent ideals, descending from etale marked ideal
   centers”. Eight hits: `Algebra.smoothLocus`, normalization properties/maps, and
   `isReduced_ofLocalizationMaximal`; none states the maximum-center theorem.
2. `leanfinder`: “Descent of smooth full maximum centers of marked ideal resolution
   words along etale local Hilbert Samuel presentations”. Eight hits about standard
   étale/smooth presentations, standard-smooth affine charts and étale polynomial maps;
   no marked resolution-word maximum-center statement.
3. `loogle`: `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal,
   AlgebraicGeometry.IsRegular`. Zero hits; it reported the project-specific
   `AlgebraicGeometry.IsRegular` as an unknown identifier, not an exact-match result.
4. `grep`: `resolutionWord|normalized_resolution_word|maximumLocus`, Mathlib
   `AlgebraicGeometry`: zero hits.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for
   `resolutionWord|normalized_resolution_word|maximumLocus` and the exact item id:
   the existing normalized-word and marked-invariant interfaces were found; no
   existing theorem states this node. Searches of the DAG additionally found the
   parent invariant calculus and downstream progress node, neither an exact attachment.

Validation: prescribed `scompile.py NE lem-trf-resolution-word-maximum-center-descent
<module>` compiled the final module both as `Sheaf.Stage2.Sandbox0` and under its actual
library module name, cleanly (8.3 s and 4.2 s with all proof imports). The final file has
no diagnostic commands, auto-bound variables, local notation, private definitions or
suppressed warnings. The real helper is a composition/equality transport, and the only
postponed theorem has the matching DAG node and seven-step proof docstring.

## Second reading by NE

This is the author's second pass, not a claim of an independent agent review; the
brief dispatches one worker and explicitly prohibits starting other agents. The
maintainer supplies the independent delivery review.

I reopened the final Lean module alongside the node. The initial pair bundles exactly
the five initial geometric hypotheses; `hP`, `hX` and `hNR` separately bind the current
stage hypotheses. `hν` matches the existing gluing theorem's witness predicate,
including its quantification over all admissible histories. In particular the theorem
assumes neither a resolution calculus nor regularity of its maximum center.

The second pass replaced the first draft's insufficient local assertion by an actual
marked-history maximum extension, the current chart's given étale map, a closed
immersion into the chart's strict transform, equality of its ideal with the pulled-back
vanishing ideal, and the cartesian square over X_H. It also corrected the boundary
condition to concern that actual center ideal with the chart's ordered exceptional
boundary. The final ambient coherence clause uses the composite inclusion at the final
index, so it concerns M in P_H. Regular points, components, interior, and both coherence
clauses are all explicit. The `finalMap` definition only transports the existing map
along `C.last`; no data is supplied by `sorry`. The node text and dependencies did not
need to change. No unresolved statement fault or STATEMENT-DISPUTED flag remains.
