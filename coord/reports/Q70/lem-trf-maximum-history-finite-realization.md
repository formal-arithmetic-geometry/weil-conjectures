## Worker report

The module `Sheaf.AlgebraicGeometry.MaximumHistoryFiniteRealization` states
`AlgebraicGeometry.maximumHistory_finite_realization` and
`AlgebraicGeometry.maximumHistoryRealization_comparison`, both with `sorry` proofs.
`MaximumHistoryRealization` is the bundle of witnesses and conditions in this lemma's
conclusion, not a new independently assumed resolution algorithm. It contains actual
histories, extensions, labels, a tower, and diagram isomorphisms. No data definition uses
`sorry`, and no calculus is chosen from an existence assertion.

The item node is unchanged outside `lean`. No new node, dependency repair, statement
correction, or disputed statement is required. The declarations are in namespace
`AlgebraicGeometry`; all universes and variables are explicit, with `autoImplicit false`.

Hypotheses and clauses, with their exact Lean counterparts:

| Node clause | Lean rendering |
| --- | --- |
| Totally ordered value set with least element, with no well-foundedness assumption | `{V : Type w} [LinearOrder V] [OrderBot V]`; there is no `WellFounded` binder. |
| Fix the calculus on all embedded rational pairs | `(ν : ResolutionInvariantCalculus.{u} V)`; its simultaneous `value` is used directly. |
| Every reduced input closed in a smooth, separated, finite-type rational ambient | `(A : EmbeddedResolutionPair.{u})`, the recorded dependency structure with `X`, `P`, `base`, `inclusion`, `closed`, `reduced`, `smooth`, `separated`, `finiteType`, `quasiCompact`. |
| Finite history starting empty | `∃! r : ℕ, Nonempty (MaximumHistoryRealization ν A r)`; its `history i` has length `i.val`, including `history 0` of length zero. |
| Extend by the ordinary ambient blowup, with scheme-theoretic strict transform | `extension i : Extension (history i.castSucc) (history i.succ)`. Each recorded history has `ambientBlowup`, `ambientBlowupMap`, `strictTransform`, `strictTransformMap`, `strictTransformToSource`. |
| Admissible histories | `admissible : ∀ i, Admissible ν.value (history i)`. |
| The reduced full positive maximum locus, without a partial-center choice | `maximum : ∀ i, IsMaximumStep ν.value (extension i)`. The recorded predicate requires a greatest value, its positivity, the reduced center, and equality of the center image with the entire equality locus. |
| Label the ith extension by its maximum in the common reverse order | `label : Fin r → OrderDual {v : V // v ≠ ⊥}`, `positive`, and `greatest`. Uniqueness of greatest values ties these labels to the maxima in `maximum`. |
| Finite strictly increasing active labels | `increasing : StrictMono label`, finite domain `Fin r`, and `activeLabels : ∀ l, l ∈ tower.labels ↔ ∃ i, label i = l`. |
| Center contained in the current strict transform | The history's `centerToIntrinsic`, `centerClosed`, `centerInclusion` and the extension's `centerMap` express the factorization through that strict transform. |
| Nonempty, regular, nowhere dense centers, coherent on ambient and strict transform | `centerGeometry` gives respectively `Nonempty`, `IsRegularScheme`, `interior (Set.range (extension i).centerMap) = ∅`, and `IsFiniteTypeWithFiniteTypeKernels` for the actual ambient ideal module and intrinsic kernel ideal module. |
| All intermediate pairs embedded rational pairs | `intermediateGeometry` gives smooth, separated, finite-type (`LocallyOfFiniteType` plus `QuasiCompact`) ambient rational structure maps and reduced transforms; history data give the closed immersions. Extensions identify the entire earlier diagrams, so these statements about the prefix endpoints cover every stage of the full history. |
| Last transform regular | `finalRegular : IsRegularScheme (history (Fin.last r)).X`. |
| Stop at the first regular stage; no exceptional cleanup | `nonregular : ∀ i : Fin r, ¬ IsRegularScheme (history i.castSucc).X`, together with `finalRegular`. The tower also retains its dependency's `stopAtRegular`. |
| Empty and regular inputs have length zero | `emptyInput : IsEmpty A.X → r = 0` and `regularInput : IsRegularScheme A.X → r = 0`. |
| Finite disjoint unions use the full maximum on the union in the same values | The quantifier over `A` has no connectedness, equidimensionality, or component hypotheses. Every step evaluates the single `ν.value` on the entire input history. Neither labels nor maxima are indexed separately by components. |
| A lower cut gives the stage after exactly the active labels it contains | `cutIndex : LowerSet (OrderDual {v : V // v ≠ ⊥}) →o Fin (r + 1)` and `cutCount` with `Set.ncard {i : Fin r | label i ∈ D}`. The set is automatically finite; `Set.ncard` excludes no infinite value sets or lower cuts. |
| The finite labeled tower with its actual diagrams | `tower : LabeledEmbeddedResolutionTower ... A`; `ambient` and `intrinsic` are natural isomorphisms to `cutIndex.toFunctor.op ⋙` the final full history diagrams. `inclusion`, `initialAmbient`, `initialIntrinsic` fix their compatibility with inclusions and the given initial pair. `cutFirst` and `cutLast` identify empty and full cuts. |
| Correct active transitions | `cutBefore i` and `cutAfter i` identify the two principal cuts with `i.castSucc` and `i.succ`. Thus the tower's blowup and strict-transform transitions are those of the chronological history. |
| Unit center and identity at inactive labels | The recorded tower's `absentCenter` is the unit-ideal equation. `inactiveAmbient` identifies the two principal-cut indices, so both reindexed diagrams have the identity transition, under the specified natural isomorphisms. `constantAmbient` and `constantIntrinsic` also apply to arbitrary inactive intervals. |
| Retain ideals and chronological order, including identity intrinsic blowups | `Extension.centers` retains all earlier ambient ideals. `ambientCenters` and `intrinsicCenters` identify every chronological ideal with the corresponding tower ideal under the cut isomorphisms. The labels are strictly increasing; no condition tests whether an intrinsic transition is an isomorphism, so no such center is deleted. |
| Determined up to canonical blowup isomorphisms | The main theorem gives unique length. `maximumHistoryRealization_comparison` gives equality of labels and a unique pair of natural ambient/intrinsic isomorphisms normalized over the initial pair, compatible with inclusion, and preserving all ambient and intrinsic ideals. After identifying the unique lengths this compares any two realizations. |
| Conditional realization, not existence of a calculus | Both theorems take the supplied `ν`; neither concludes `Nonempty (ResolutionInvariantCalculus V)`. |

Dependency declarations read in full and reused:

- `Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData`:
  `AlgebraicGeometry.ResolutionInvariantCalculus` and its `value`, `maximumExists`,
  `maximumGeometry`, `nextGeometry`, `strictProgress`, `smoothValues`, `termination` fields.
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory`:
  `EmbeddedResolutionHistory`, `X`, `base`, `Extension`, `Extension.centerMap`,
  `IsMaximumStep`, `Admissible`. The raw history retains the blowup/strict-transform
  isomorphisms and their structure maps; the extension retains earlier ideals.
- `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`:
  `EmbeddedResolutionPair`, `LabeledEmbeddedResolutionTower`, with its unit-center,
  coherence, stopping, and initial/final conditions. No second pair, history, admissibility,
  maximum-step, or labeled-tower definition is introduced.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  locally Noetherian and stalkwise regular, reexported by the statement dependencies.
- Proof imports follow all recorded proof dependencies:
  `WeilConjectures.Blowup.BlowupUniversal` (`exists_lift_blowup`,
  `hom_ext_of_isInvertible_comap`), `WeilConjectures.Compactification.StrictTransform`
  (`AlgebraicGeometry.strictTransform` and the ideal-sheaf specialization),
  `WeilConjectures.Blowup.Principalization` (`isInvertible_comap_blowupMap`), and
  `WeilConjectures.Blowup.InvertibleCenter` (`isIso_blowupMap_of_isInvertible`).
- Mathlib's `OrderDual`, subtype order, `StrictMono`, `LowerSet`, `OrderHom.toFunctor`,
  `Set.ncard`, natural isomorphisms, and `Functor.whiskerLeft` supply the indexing and
  diagram notation. No private notation or instance is used.

Source reading: ILO Expose VIII, printed pp. 91--94, specifically 2.3.1 (trivial tower
exactly for regular inputs), 2.3.4 (canonical comparisons), 2.3.5 (disjoint-union
synchronization), 2.3.11 (stop before exceptional-divisor cleanup), and 2.3.13 (smooth
functoriality and invariant synchronization). This is the node's conditional elementary
history argument, not a claim that these pages prove existence of the supplied calculus
from termination alone. Both theorem docstrings carry the full natural-language proof,
including dependent choice for finiteness and canonical comparison of the ordinary blowups.

Edge cases checked before finalizing:

- `r = 0`: `Fin r` is empty, there are no extensions or labels; the lower-cut diagram
  reindexes a single stage, and regularity is required at that stage.
- Empty and regular input: explicit zero-length clauses, with no additional step. The
  empty scheme is regular under the reused locally Noetherian/stalkwise definition.
- `V` a singleton: there are no nonbottom labels; a supplied calculus therefore permits
  only zero-length realizations on its regular inputs. No nonempty label type is assumed.
- Infinite or non-well-founded `V`, and infinite lower cuts: only the active index set
  is finite, and the proof uses the calculus's termination, not order well-foundedness.
- Disconnected inputs of different dimensions: no connectedness or dimension restriction;
  maxima and labels use the entire history in the same `V`.
- Empty/full cuts, cuts before/after each active label, inactive labels and inactive
  intervals: the explicit endpoint/count fields and diagram isomorphisms cover all cases.
- Identity intrinsic blowup with a nonempty center: the step and its ideal remain in
  `Fin r`, in the final history and at its active label.
- Independent scheme and value universes: `u` and `w` remain independent throughout.

Searches for an existing exact statement (all returned declarations inspected):

- `msearch.py` LeanFinder query: "A terminating maximum center rule on embedded resolution
  histories has a finite realization indexed by reverse invariant values". Eight hits,
  all `Computation` termination/results declarations; none contains embedded pairs,
  blowups, ideals, or labeled lower-cut diagrams.
- `msearch.py` LeanSearch query: "A terminating maximum stratum rule on embedded blowup
  histories gives a finite labeled embedded resolution tower". Eight generic Hahn
  embedding/ideal-height hits; none states the supplied-calculus realization lemma.
- `msearch.py` Loogle query: `"blowup"`. Zero hits.
- `msearch.py` Mathlib grep query:
  `maximum.history|MaximumHistory|finite.realization|maximum.center`. Zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for maximum history/finite realization
  terminology found the existing dependency interfaces and unrelated coefficient/adic
  finite-realization declarations; none states this lemma.
- `grep -rn "lem-trf-maximum-history-finite-realization" lean/WeilConjectures` returned
  no match. `rg` for `MaximumHistory|maximumHistory|maximum.history` in
  `dag/lean_names_upstream.json`, the upstream sources and the Sheaf sources returned
  no existing declaration with the proposed names.

Validation: the prescribed `scompile.py Q70 lem-trf-maximum-history-finite-realization`
compiled the sandbox probe and the actual module on the server cleanly (5.8 s and
11.5 s reported respectively). The first attempt diagnosed an unqualified
`whiskerLeft`; using Mathlib's `Functor.whiskerLeft` fixed it. No warnings remain.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
