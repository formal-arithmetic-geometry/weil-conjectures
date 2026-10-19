## Worker report

Repair of the independent return at ce13730536d7, H3. The saved packet was inspected
first and its prescribed dry run passed at dd8f7650ae. Its mathematical self-check
still found exactly the returned defects, so this delivery retains the original rule
domain and structures and repairs their interface. The current shared node agrees
with the saved node in every field other than `lean`; no mathematical node statement,
dependency, proof, or target has changed. The delivery wrapper rebases the packet on
the current published branch.

`Sheaf.TraceFormula.SharpeningFanBijection` now defines the actual sharpening map on
sections, image and inverse-image ideals, coherent-ideal equivalence, canonical
sharpened maps and ordered towers, and the precise tower/comparison and local descent
conditions on the rule equivalence. Every theorem has a `sorry` proof; every definition
has real data. The only choice of a map is from `existsUnique_sharpMap`, which determines
the complete map by equality, including its base and section maps. No rule or tower is
chosen from a bare existence proposition. All 35 declarations are listed in `lean`.

The returned points are repaired as follows:

- The previous bare `Nonempty (… ≃ …)` is replaced by `∃ e : … ≃ …` together with
  `RuleSharpens R (e R)` and `RuleSharpens (e.symm Q) Q`. These structures identify
  the ordered towers over the sharp base, their centers and arrows, and the indices
  and actual level maps of the contracted smooth-pullback comparisons. Thus an
  unrelated bijection does not satisfy the conclusion.
- The first paragraph is represented by `sharpSection`, `sharpIdeal`, `unsharpIdeal`,
  `sharpIdeal_properties`, `sharpIdealEquiv`, `sharp_blowup`, `Tower.toFan`, and
  `SharpeningGeometry`, which is an explicit conjunct of the main theorem.
- The local inverse is now a proposition in the theorem's type:
  `IsLocalRuleDescent` for every `AffineLiftCover`, in both directions. Existence of
  such covers for every input fan is also a conjunct; there is no global-lift assumption.
- The monoscheme `identityMap` now uses `ResolutionComparison.levelMap`, exactly as
  on the fan side, instead of fixing `contraction.iso.hom`.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| Fine monoscheme with finite affine cover | `Monoscheme.ResolutionInput.monoscheme : Fine`; `Fine` already has its finite affine cover, retained also as `ResolutionInput.finiteCover`. |
| Ordinary stalk group completions torsion free | `ResolutionInput.torsionFree : monoscheme.IsTorsionFree`. |
| Sharp stalk group completions torsion free | `ResolutionInput.sharpTorsionFree : (Fine.toFan monoscheme).IsTorsionFree`. |
| λ is quotient by units | `sharpSection`: `Associates.mkMonoidHom`, followed by `toSheafify` on `FineFan.sharpPresheaf`. |
| Image ideal and its inverse | `sharpIdeal` is the sheaf image: every germ locally has an ideal-section representative; `unsharpIdeal` is the sectionwise λ-preimage. |
| Bijection on all coherent ideals | `sharpIdeal_properties` gives coherence and both inverse equations; `sharpIdealEquiv` has exactly those two functions. `FineFan.IsCoherentIdeal` allows zero generators, just like the recorded monoscheme predicate. `SharpeningGeometry.ideals` includes both equations in the main theorem. |
| Corresponding saturated blowups | `sharp_blowup b I hb` states the saturated blowup property of `b.toFan` with the specified center `sharpIdeal I`; its construction uses the actual `Fine.toFan` levels. |
| Finite ordered tower bijection | `Tower.toFan` keeps length, order, levels, arrows, and centers explicitly; `SharpeningGeometry.towersExist` lifts any ordered fan tower over the specified base, and `towersUnique` identifies any two lifts over that base with every arrow and center retained. `IsSharpTowerLift` pins the sharpening identification at level zero. This is the source's identification of blowup towers over a fixed base, not arbitrary isomorphism of unrelated towers. |
| Nonempty centers | `sharpIdeal_properties` and `SharpeningGeometry.ideals` include equivalence of the two `IsNonemptyCoherentIdeal` predicates; `Tower.blowup` retains each nonempty center. |
| Whole-ideal stages | `SharpeningGeometry.ideals` explicitly reflects equality with `wholeIdeal`; it does not conflate a unit ideal with an identity morphism. |
| Smooth last level | `SharpeningGeometry.smoothLast` is the equivalence of the actual terminal objects' smoothness predicates, including length zero. `closedDomain` retains both torsion-free conditions at every level. |
| Recursive pullback | `idealPullback` equates the prescribed image ideals; `recursivePullback` supplies a `FineFan.PullbackTower` whose every lift is exactly `Hom.toFan` of the original lift. |
| Smooth maps | `sharpSpaceMap_properties` includes the valid forward implication from smooth monoscheme maps to smooth fan maps. `RuleSharpens` compares the rules along these actual maps. No false reflection of arbitrary morphism smoothness is asserted. |
| Contraction convention | `unitStages` equates the conjunction of whole ideal AND isomorphism; `contraction` supplies the sharp contraction with the same index map and sharpened level isomorphisms. A nonisomorphic initial saturation is therefore retained. |
| Rules on the full corrected monoscheme category | `Monoscheme.SmoothFunctorialDesingularization` quantifies over every `ResolutionInput` and every smooth `Hom`; no saturation or global affineness assumption is added. |
| Rules on all fine torsion-free fans with finite cover | The recorded `FineFan.SmoothFunctorialDesingularization` and `FineFan.ResolutionInput` are used directly. |
| Natural bijection from sharpening | The witness `e` is required to satisfy `RuleSharpens` forward and inverse. `SharpResolutionIdentification` fixes the base, arrows, centers and order. `comparisonIndex` identifies contracted indices and `comparisonMap` equates the actual sharp level map through these identifications. |
| Identity/composition compatibility | Both rule structures carry the same identity/composition index and level-map laws; `RuleSharpens.comparisonIndex` and `.comparisonMap` transport the actual comparisons, so they preserve these laws as well as towers. |
| Finite disjoint union of sharp affine lifts | `AffineLiftCover` supplies a finite fan chart cover with sharp coordinate monoids and a corrected-domain monoscheme covered by pairwise disjoint affine charts with those same monoids. Its `onChart` equation identifies its map with sharpening the chart isomorphisms and the given fan chart inclusions. |
| A fan need not have a global monoscheme lift | The theorem asserts `Nonempty (AffineLiftCover F)` for every fan input; only a smooth surjective cover map from the disjoint union is used, never an isomorphism with the entire fan. |
| Glue the uncontracted restrictions | `IsLocalRuleDescent` identifies the recursive pullback of the single global fan tower with sharpening the single tower `R(C.total)`, with an order isomorphism rather than a contraction. The base comparison is the specified cover map. Restricting to the disjoint components therefore retains every inherited center and index. |
| Finite, cover-independent output | `Q.resolution F` has a finite length; the same fixed tower satisfies `IsLocalRuleDescent` for every affine lift cover `C`, in both directions of `e`. Hence a cover is not extra input to the resulting rule. |

Dependency declarations used, with signatures and source docstrings read:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `Monoscheme.Fine`, `Chart`,
  `Hom`, `Fine.toFan`, `Fine.IsTorsionFree`, `Fine.IsSmooth`, `Hom.IsSmooth`,
  `IsCoherentIdeal`, `IsNonemptyCoherentIdeal`, `IsSaturatedBlowup`, `IdealFamily`,
  `pullbackIdeal`, `pullbackAlong`, `wholeIdeal`, `Tower`, `PullbackTower`, `Contraction`.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.Fan`, `Chart`, `Hom`, `affine`,
  `sharpPresheaf`, `sharpSheaf`, the actual ideal/pullback/blowup/tower/contraction
  declarations, and `ResolutionInput`, `Resolution`, `ResolutionComparison`,
  `ResolutionComparison.levelMap`, `SmoothFunctorialDesingularization`.
- Proof dependencies retained: `Sheaf.GroupTheory.FineMonoidUnitSplitting`,
  `FineFan.fine_monoid_unit_splitting`; `Sheaf.GroupTheory.FineMonoidFiniteSaturation`,
  `fine_monoid_finite_saturation`; `Sheaf.TraceFormula.FsFaceSharpening`,
  `AlgebraicGeometry.face_sharpening`;
  `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`,
  `FineFan.affineFan_localization_sections`;
  `Sheaf.AlgebraicGeometry.AffineFanHomUniversal`, `FineFan.affine_hom_universal`.

Source reread for the repair: ILO arXiv:1207.3648, Exposé VIII, §§3.1.17--3.1.28,
printed pp.101--102 (PDF pp.106--107), especially Lemma 3.1.25 and §3.1.26/Theorem
3.1.27. The existing corrected domain is retained, including the deliberate omission
of the invalid reverse morphism assertion in §3.1.15. The main theorem docstring
now carries all fourteen proof steps, including synchronization, common local product
lifts, gluing, cover refinement, and both inverse composites.

Searches for the repair (2026-10-19):

- `msearch.py ... leanfinder "sharpening monoid sheaf quotient units coherent ideals saturated blowup tower"`:
  eight hits about Zariski's main theorem, scheme ideals, and scheme structure sheaves;
  none is a monoidal-space sharpening/tower correspondence.
- `msearch.py ... leansearch "monoid quotient by units sheaf coherent ideal bijection saturated blowup fan"`:
  eight hits, including `Associates.quotient_mk_eq_mk`, `Associates.isUnit_mk`, units,
  localization and Picard quotients; none supplies the sheaf ideal/tower correspondence.
- `msearch.py ... loogle "Associates.mkMonoidHom, toSheafify, sheafifyLift"`:
  zero hits, reports unknown `toSheafify`; source lookup then found the actual
  `CategoryTheory.toSheafify` and `Associates.mkMonoidHom` APIs and used them.
- `msearch.py ... grep "sharpIdeal|TowerIdentification|SmoothFunctorialDesingularization"`:
  zero hits. `rg` over `WeilConjectures`, `lean/Sheaf`, and the chapter DAG found the
  recorded fan/monoscheme framework, the existing log-structure-specific sharpSection,
  and the monoscheme coherence definition. None provides the repaired correspondence
  or its helper maps. The log helper has a different domain, and the existing
  monoscheme coherence and tower definitions are reused.
- Mathlib source `rg` found `toSheafify`, `sheafifyMap`, and `sheafifyLift` in
  `CategoryTheory/Sites/Sheafification.lean` and `Associates.mkMonoidHom` in
  `Algebra/GroupWithZero/Associated.lean`. These implement λ's prescribed operations;
  no duplicate quotient or sheafification construction is introduced.

Edge cases checked: empty ideal and zero local generators; empty open, where image
membership is vacuous and gives the unique section; length-zero towers; empty fan
and empty affine cover (`Fin 0`); disconnected covers; rank-zero monoids and free unit
groups; whole-ideal isomorphisms versus nonidentity initial saturation; a smooth fan
with no global monoscheme lift; and the failure of smoothness reflection for arbitrary
monoscheme morphisms. The local clause allows zero charts precisely for the empty fan,
uses no global lift, and keeps full ordered towers before contraction.

No STATEMENT-DISPUTED or node statement correction is needed. Helpers express the
clauses of this one node, with source/blueprint docstrings and theorems recorded in
its own `lean.declarations`; no new independent notion or dependency module is added.

## Second reading by NP

Author self-check against the returned head, current shared node, source, and repaired
file (the maintainer supplies the independent review). The original domain, resolution
and comparison structures are retained. The minor identity-map mismatch was fixed to
use `levelMap`. The former size-only statement was insufficient: it omitted the first
paragraph and put the local inverse only in prose. The repaired theorem explicitly
contains `SharpeningGeometry`, existence of finite affine lift covers for every fan,
and a witness equivalence with forward/inverse `RuleSharpens` and universal local
descent clauses. Reading their fields verifies actual λ images, inverse ideals,
base-preserving tower lifts, all centers and arrows, identical deletion tests,
recursive pullbacks, and comparison index/map equations. The local cover data really
are finite pairwise disjoint affine monoscheme charts with the same sharp monoids
as the fan charts and a prescribed chartwise covering map. Its descent identification
is uncontracted and quantified over every cover, so both the no-global-lift and cover
independence clauses are now in the type. No extra hypothesis or dropped edge case
was found. Universes are explicitly `{u}` throughout, `autoImplicit` is false,
every theorem proof is exactly `by sorry`, and every definition has real data.
