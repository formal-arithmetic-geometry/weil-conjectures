## Worker report

Item: lem-trf-normalized-resolution-on-normal-inputs. Group: Q78. Stage 2.

The module `Sheaf.AlgebraicGeometry.NormalizedOrdinaryResolution` states
`AlgebraicGeometry.nonempty_normalizedOrdinaryResolutionRule`. Its only theorem has
proof `sorry`. It asserts the existence of the simultaneous levelwise normalization of
an arbitrary fixed `SmoothFunctorialOrdinaryResolution`, with its prescribed centers,
normalization squares, contracted smooth pullbacks, and identity/composition laws.

The source was read in the local ILO PDF, Exposé VIII, printed pp. 90--93:
Proposition 2.2.4(ii), 2.2.6--2.2.9, 2.3.3(i), 2.3.4--2.3.5(i), and Remark 2.3.12.
The current blueprint ancestor proof was also read under `literature/blueprint/latest/`.
As the accepted node already records, that current ancestor now uses contracting
correspondences; this node retains the historical toric-resolution supporting branch.
No unit statement, item statement, or accepted natural-language proof is changed.

The auxiliary declarations belong to this specific normalization operation. They reuse
`Monoscheme.NormalizedTower`, `QENormalizedResolutionTower`, and
`QENormalizedResolutionComparison`; they do not define competing blowup, normalization,
coherence, tower, pullback, or contraction notions. No construction selects data from the
postponed existence theorem. `normalizedLevel`, `normalizedProjection`, `projection`,
and `toResolution` have complete bodies. The two structures package the conclusion's
specified comparisons and properties. Their declarations are listed in `lean.declarations`.

Hypotheses and clauses, matched to Lean:

| Node text | Lean rendering |
| --- | --- |
| Fix an ordinary smooth-functorial resolution rule R on all reduced finite-type rational schemes, including finite disjoint unions | The theorem's sole argument is `R : SmoothFunctorialOrdinaryResolution.{u}`. Its existing `tower`, `resolves`, and `comparison` fields have exactly that domain and those laws. `RationalResolutionInput` supplies a reduced scheme and its locally finite-type, quasi-compact rational structure map, with no separation assumption. All finite disjoint unions in that class are already included. |
| Normal input means all local rings are integrally closed domains | Each `realization S` takes `∀ x : S.scheme, IsDomain (S.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (S.scheme.presheaf.stalk x)`. Comparisons take both `hnS` and `hnT`. No irreducibility or nonemptiness is required. |
| Ordinary levels and ordered centers | Exactly `(R.tower S).level`, `.center`, `.length`, and `.transition`, from the recorded dependency. |
| N₀=S; Nᵢ=Sᵢ^ν for positive i | `OrdinaryBlowupTower.normalizedLevel` matches the index: zero gives the input scheme, a positive index gives that ordinary level's `reducedNormalization`. `levelIso` specifies the corresponding canonical models in the existing normalized tower. |
| ν₀ is the identity under S₀=S, and νᵢ is componentwise normalization otherwise | `normalizedProjection` is `A.initial.inv` at zero and `.fromReducedNormalization` at positive indices. Its composite with the initial ordinary identification is the identity of S. `projection` precomposes with the specified `levelIso`. |
| Kᵢ=Iᵢ O_Nᵢ | `NormalizedOrdinaryResolution.centers` uses the recorded ideal extension `.comap` along that very projection, as equality of ideal sheaves. |
| Finite tower of normalized blowups over each preceding level | `tower : NormalizedTower A.length`. Its existing `blowup` field is `IsNormalizedBlowup (tower.arrow i) (tower.center i)`, which contains an isomorphism to `.normalizedBlowup` and its factorization over the preceding level. `arrows` requires the induced map to commute with the ordinary transition and normalization projections. |
| Every level normal, reduced, finite type over Q | `normal` is the same stalkwise normal-domain condition at every level. Reducedness is `tower.reduced`. `finiteType` and `quasiCompact` apply to the recursive tower structural map followed by `S.structureMap`, jointly expressing finite type. |
| Centers coherent | `coherent` is `RingedSpace.IsCoherent` applied to the existing ideal module `(tower.center i).toModules`, not just finite generation. |
| Nonempty nowhere dense zero schemes | `nonempty` is nonempty support and `nowhereDense` is `tower.HasNowhereDenseCenters`. Ideal support is the underlying zero scheme. |
| Terminal Nₙ canonically equals regular Sₙ | `terminal` says the specified projection to the ordinary last level is an isomorphism; its map is exactly normalization transported by `levelIso`. `regular` uses `tower.IsDesingularization`, the recorded regular-scheme condition at the last level. |
| Length zero is trivial | The tower has `Fin (A.length+1)` levels and `Fin A.length` arrows and centers. For zero length it has one level, identified with S by `levelIso 0`, and no arrows or centers. |
| Empty input gets the trivial tower | `NormalizedOrdinaryResolutionRule.empty : ∀ S, IsEmpty S.scheme → (R.tower S).length = 0`. The normalization keeps exactly this length. |
| Every smooth h between normal rational inputs | `comparison S T hnS hnT h over [Smooth h]`. `over` is the existing rational-structure compatibility from the ordinary rule; morphisms between rational schemes are automatically over Q. |
| Canonical comparisons obtained from R and normalization | `normalization_square` identifies the normalized comparison map with the ordinary comparison after composing the prescribed normalization projections, including the equality transport from `count_eq`. |
| Identify R^ν(T) with contraction of the recursive pullback | The existing `QENormalizedResolutionComparison` supplies the full pulled normalized tower, initial identification with T, cartesian square at every level, compatibility of arrows and extended centers, and `NormalizedContraction` to the tower on T. The maps to the base are the actual recursive composites, via `toResolution`. |
| Exactly unit extended ideals deleted | `deleted_iff_unit` identifies omission from the ordinary retained embedding with the unit ideal of the pulled tower. `count_eq` identifies the contraction index with the ordinary count. |
| Unit normalized-blowup stages are isomorphisms | The existing comparison's `unit_isIso` states this for its pulled arrows. Its contraction's `deleted` condition includes both the unit ideal and the isomorphism condition. |
| Other centers are extended Kᵢ in original order | The comparison's `centers`, contraction's `keptCenter`, and `retained_before`/`retained_after` identify precisely the retained stages selected by the existing increasing `retainedStage`, with the required level transports. |
| Level maps and retained indices respect identities and composition | `identity_map`, `composition_map`, `identity_retained`, and `composition_retained`. Heterogeneous equality in the map laws expresses only source-level index transport. Normalized count laws follow directly from `count_eq` and the existing rule's `identity_count` and `composition_count`. Retained indices are exactly the original ones. |
| Surjective smooth h deletes no stage | `surjective_no_deletion` makes the contraction index injective; that index is already surjective by `NormalizedContraction`. The identical ordinary retained embedding is surjective by R's existing law. |

Dependency declarations used (their full signatures and docstrings were read):

- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`:
  `AlgebraicGeometry.RationalResolutionInput`, `OrdinaryBlowupTower`,
  `OrdinaryResolutionComparison`, `SmoothFunctorialOrdinaryResolution` and their fields.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `Mathlib.Algebra.Ring.Defs`: `IsDomain`. The normal-ring node's recorded inline
  normal-domain form is used for the stalks. `Localization.AtPrime` was also inspected.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalization` and `fromReducedNormalization`.
- `Sheaf.AlgebraicGeometry.NormalizedBlowup`:
  `AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup` and `normalizedBlowupMap`,
  through the published `IsNormalizedBlowup`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  through the existing last-level regularity predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `AlgebraicGeometry.Monoscheme.IsNormalizedBlowup`, `NormalizedTower`,
  `NormalizedContraction`, and `NormalizedTower.IsDesingularization`.
- `Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`:
  `AlgebraicGeometry.Monoscheme.NormalizedTower.toFirst` and `HasNowhereDenseCenters`.
- `Sheaf.AlgebraicGeometry.QENormalizedResolutionRule`:
  `AlgebraicGeometry.QENormalizedResolutionTower`, `toBase`,
  `QENormalizedResolutionComparison`, and `levelMap`. These tower/comparison structures
  are general in the base scheme; no quasi-excellence assumptions are introduced.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the shared
  `AlgebraicGeometry.RingedSpace.IsCoherent`; the existing ideal-module bridge is
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules`.

Four already-landed definition nodes are added to `stmt_deps` to name the existing
normalized-tower, based-comparison, recursive-composite, and coherence interfaces used
in the signature: `def-per-qe-normalized-resolution-rule`,
`def-trf-monoscheme-toric-realization`, `def-per-normalized-tower-descent-data`,
and `pqf-def-coherent`. This uses brief-stage2 §5's permission to add landed nodes.
There are no new DAG nodes and no dependency-module repairs.

The module imports all recorded, available proof-dependency modules, including
`NormalizedBlowupCalculus`, chart rings and chart covers, formal smoothness,
`ModulePullbackIdealQuotient`, and `CoherentFiniteTypeLocallyNoetherian`, as plain imports.
The Mathlib finite-type/Noetherian and permanence matches are likewise imported.
`lem-sfb-componentwise-normalization-generic-properties` has no recorded declaration or
Mathlib match, so has no module to import; this is a proof dependency only, not a missing
notion in the statement. The theorem docstring includes all eight natural-language
proof steps and their DAG citations.

Edge cases checked before writing and again after elaboration:

- Empty schemes: normality is vacuous, centers cannot be nonempty, and the explicit empty
  clause forces zero length. A map from the empty scheme deletes all ordinary stages.
- Zero length: `Fin 0` has no centers or arrows; `Fin 1` has just the input level. The last
  projection is the initial isomorphism inverse, so the terminal clause also covers this case.
- Disconnected normal inputs and finite disjoint unions: no integral-scheme hypothesis is
  imposed; normalization is the existing componentwise coproduct construction.
- Nonunit invertible/Cartier ideals: an isomorphic blowup does not force deletion; deletion
  is equivalent to the unit ideal. A nonunit Cartier center is retained in its original order.
- Nonnormal intermediate ordinary levels are allowed; only their normalized levels must
  satisfy the normal-domain stalk condition.
- Arbitrary universe u, with the existing `ULift.{u} Q` convention, no imposed universe
  equality, connectedness, separation, dimension, or surjectivity restriction on smooth maps.
- The theorem assumes no particular construction or existence theorem for R; it transforms
  every rule having the exact recorded ordinary interface.

Searches for existing statements/notions (2026-10-24):

- `msearch.py ... leanfinder "Normalizing each level of a smooth functorial ordinary blowup
  resolution on normal rational schemes gives a smooth functorial normalized blowup tower"`:
  eight general normalization morphism hits, including `Scheme.Hom.normalizationDiagramMap`,
  `normalization`, `toNormalization`, and `normalizationDesc`; no resolution-rule theorem.
- `msearch.py ... leansearch "normalization ordinary blowup resolution smooth functorial tower"`:
  eight general normalization hits; no rule transformation.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.reducedNormalization,
  AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup"`:
  zero hits, with unknown project identifier `reducedNormalization` in the Mathlib service.
- `msearch.py ... grep "normalizedBlowup|OrdinaryBlowupTower|SmoothFunctorialOrdinaryResolution"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normalized resolution/tower names:
  found the already-published normalized blowup calculus, normalized towers, QE based
  resolution comparison interface, and ordinary rule; these are reused. No exact theorem.
- `rg` for the item id in `lean/WeilConjectures`: no hit.
- `rg` for all newly introduced declaration names across Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no pre-existing names.
- DAG searches for `NormalizedTower` and `QENormalizedResolutionTower` found the existing
  definition nodes now added as statement dependencies; no new generic tower node is needed.

Validation: every compile used the prescribed `scompile.py`. After correcting evaluation
of equality between order homomorphisms and one overlong line, both sandbox and actual
module-name compilation succeeded without errors or warnings. No theorem was proved.
There is no disputed statement or source-based statement correction.

## Second reading by Q78

I reopened the complete accepted node and the final module for a separate author rereading.
No second agent was started, as the dispatch brief expressly forbids that; the maintainer's
independent review remains the required independent reading.

The fixed input rule is the recorded rule on all reduced rational finite-type schemes;
the realization/comparison fields impose normality only on the actual inputs, not on the
ordinary intermediate levels. Zero is the input model, positive levels are the exact
componentwise-normalization models up to specified isomorphisms, and every center equality
uses the canonical projection. `tower.blowup` is an over-the-previous-level statement,
not just an abstract scheme isomorphism. The separate finite-type, quasi-compact,
normality, reducedness, actual module-coherence, nonempty-support, nowhere-density,
regular-terminal, and terminal-projection-isomorphism clauses all remain present.

I traced the full recursive pullback and its contraction through the existing comparison
record, including unit-stage isomorphisms, ideal transport, base identification, and
retained-stage order. `normalization_square` prevents replacement by arbitrary maps;
`count_eq` and the two retained-endpoint equations identify the original ordered indices.
I checked both map laws and both retained-index laws; their retained-index fields were
restricted to normal inputs during this rereading to reflect the node's scope explicitly.
The count laws are inherited through exact equality with the ordinary count, rather than
being omitted. Surjective maps give an injective, already-surjective contraction count.
Length-zero and empty-input cases do not introduce a first center or a nonexistent arrow.

The compilation correction was a coercion issue: equality of order homomorphisms is
evaluated with `congrArg (fun c ↦ c i)`, rather than applying `congrFun` to a non-function
structure equality. One long line was wrapped. No mathematical hypothesis or clause was
changed, and no unbound implicit variable, extra axiom, hollow data definition, private
notion, or postponed helper theorem remains.
