## Worker report

The new module `Sheaf.AlgebraicGeometry.CompleteLocalRigidificationComparison` states
`AlgebraicGeometry.completeLocal_rigidification_comparison`, with proof `sorry`.
It compares the complete underlying normalized blowup towers of two rigidifications,
over their common original scheme, including every arrow and actual ordered ideal
sheaf. It does not compare their different log structures. The helper
`RigidifiedQuotient.Construction.UnderlyingIso` unpacks this equality for the already
recorded `Construction` type; it is a structure of comparison witnesses, with no
chosen objects or postponed data. Both declarations belong to the item's statement.
No new independent definition node or mathematical statement correction is needed.

Read the node's accepted four-step proof, all six statement-dependency records and
all additional proof-dependency records. Read the declarations and docstrings of
`RigidifiedQuotient.Pair`, `.Construction`, `.IsFanInduced`, `.ComparisonSystem`,
`InducedNormalizedLogResolution`, `RegularFunctorialNormalizedResolution`,
`IsRegularScheme`, `IsStrictNormalCrossingsBoundary`, `FineSaturatedLogScheme`,
`IsSaturatedLogBlowup`, `IsAdicComplete`, and the recorded comparison theorems.
The source PDF was read directly with pdftotext: physical pages 133--134 are
printed pp.127--128 (5.4.4--5.5.3), and physical pages 119--120 are printed
pp.113--114 (3.4.15 and its synchronization argument). The source explicitly
uses one common finite union, rather than independent component contractions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fix one normalized characteristic-zero algorithm functorial for regular maps | `F : RegularFunctorialNormalizedResolution.{u}` |
| Use its induced saturated fan rule | `D : InducedNormalizedLogResolution F`; `hP : RigidifiedQuotient.IsFanInduced D.fanRule P` |
| Fix the rigidified quotient construction | `P : StrictEtaleLogBlowupProcedure IsLogBlowupInput`; `C₁ : Construction P X`, `C₂ : Construction P Y` |
| Finite group | `G : Type v`, `[Group G]`, `[Finite G]` |
| A finite disjoint union of spectra | `m : ℕ`, `A : Fin m → Type u`, `components : X.logScheme.scheme ≅ ∐ fun i ↦ Spec (.of (A i))` |
| Each ring commutative, Noetherian regular local | `[∀ i, CommRing (A i)]`, `[∀ i, IsRegularLocalRing (A i)]`; the last class extends both `IsLocalRing` and `IsNoetherianRing` |
| Complete for the maximal ideal | `[∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i)]` |
| Separably closed residue fields | `[∀ i, IsSepClosed (IsLocalRing.ResidueField (A i))]` |
| Two rigidifications of the same scheme/action/original boundary | `X Y : RigidifiedQuotient.Pair G`, `sameScheme`, `sameAction`, `sameBoundary` |
| Tame action, abelian geometric inertia | `Pair.tame`, `Pair.abelianInertia` for the actions in the two presentations |
| Free outside the original G-strict SNC boundary B | `Pair.boundary`, `Pair.snc`, `Pair.groupStrict`, `Pair.freeOutside`, `Pair.boundaryInvariant` |
| Invariant NC enlarged boundaries containing B | each pair's `enlargedBoundary`, `normalCrossings`, `enlargedInvariant`, `contains` |
| Enlarged divisorial log structure is very tame | `Pair.divisorial` includes its structure-map-compatible isomorphism with the actual divisorial presheaf; `Pair.veryTame` |
| Resolve the log quotient and pull back in fs log schemes | `Construction.quotient`, `.quotientMap`, `.invariantQuotient`, `.input`, `.tower`, `.pullback`, `.fullPullback` |
| Underlying normalized blowup towers with actual centers | `Construction.center`, `.normalized`, `.algebraized` |
| Equal complete towers on X | `Nonempty (Construction.UnderlyingIso C₁ C₂ (eqToIso sameScheme))` |
| Same original order and no deleted stages | `UnderlyingIso.index` and `.stage` are order equivalences of the FULL finite index sets; `.first`, `.before`, `.after` fix adjacency |
| Identify underlying stages, arrows and their maps to X | `.iso`, `.arrows`, `.base` |
| Same defining ideal sheaves | `.centers` is equality with the comap under the stage isomorphism, not equality of radicals or supports |
| Finite union with component permutations; not separately contracted | No action on individual `A i` is required; the group acts on the whole `Pair`. There is one global tower index and no contraction in the conclusion |

`Pair`'s Noetherian, regular, separated, admissible and generically-free certificates
are the interface of the prescribed construction, not extra mathematical restrictions
here. A finite union of affine spectra is affine and separated; regular local rings
are Noetherian and regular on localization. The whole affine scheme is invariant,
giving admissibility. An effective Cartier boundary misses all generic points of
the regular scheme, so freeness on its complement implies generic freeness. These
same properties hold for either presentation of the same scheme and action. The
isomorphism presenting the components is data describing X, not an equivariant
identification that would forbid component permutations. `sameScheme` identifies
only the underlying schemes; it does not equate enlarged boundaries or log schemes.

Used dependency declarations (the modules named here are imported, directly or
through the recorded public dependency interfaces):

- `Sheaf.AlgebraicGeometry.RigidifiedQuotientTowerComparison`:
  `AlgebraicGeometry.RigidifiedQuotient.Pair`, `.IsFanInduced`, `.Construction`,
  and `AlgebraicGeometry.rigidifiedQuotient_tower_comparison`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  the ring clause is Mathlib's `IsRegularLocalRing` from
  `Mathlib.RingTheory.RegularLocalRing.Defs`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (the completion
  dependency's companion recorded declaration).
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `AlgebraicGeometry.FineSaturatedLogScheme`, `IsSaturatedLogBlowup` and log towers.
- `Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence`:
  `AlgebraicGeometry.characteristicZero_log_resolution_independence`, with
  `InducedNormalizedLogResolution` and `RegularFunctorialNormalizedResolution`
  from its now-public signature imports.
- Proof imports: `Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift`,
  `AlgebraicGeometry.exists_simultaneousCohenRigidificationLift`; and
  `Sheaf.AlgebraicGeometry.LogBlowupNormalization`,
  `AlgebraicGeometry.exists_saturatedLogBlowup_normalization`.

Edge cases checked before writing: m=0 is allowed (no `Nonempty` binder), m=1,
dimension-zero fields, empty original and enlarged boundaries, identical enlarged
boundaries, the trivial group, a nontrivial permutation of isomorphic components,
and both positive and zero residue characteristic. No characteristic restriction is
imposed on the original rings. Proper principal centers remain as stages even when
the corresponding normalized blowup is an isomorphism. The ordered equivalences
cannot delete a stage globally or on a component. The group universe v is independent
of the ring/scheme universe u, just as in the recorded construction; no universe
is equated to make an interface typecheck. No STATEMENT-DISPUTED finding.

Searches made using the required launcher msearch.py wrapper, group Q92/item:

- LeanFinder: `Complete strictly local regular schemes independence of very tame rigidification normalized blowup resolution towers`.
  Eight unrelated normalization-map results, no rigidification independence theorem.
- Loogle: `"IsAdicComplete", "IsRegularLocalRing"`. Zero matches; the individual
  classes are nevertheless available through the dependency records.
- Mathlib grep: `rigidification|Rigidification|NormalizedResolution` in
  AlgebraicGeometry. Zero matches.
- LeanSearch: `Independence of very tame rigidifications over complete regular local rings gives identical centered normalized blowup towers`.
  Eight unrelated unramified/residue-field/normalization declarations; no match.
- `rg -n 'rigidification|Rigidification|completeLocal.*[Cc]omparison'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: found existing rigidified construction,
  simultaneous lift and unrelated line-bundle rigidifications; no theorem for this
  node. The exact node id in `lean/WeilConjectures` had no match.
- Exact proposed declaration and helper names searched in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`: no collisions.

Server compilation: all nine delivered modules compiled cleanly using scompile.py,
including each repaired dependency separately and the consumer with module mode.
The first compiler failure diagnosed the legacy characteristic-zero module; the
second exposed its legacy toric-realization proof import and monoid-algebra chain.
All are repaired in this packet, without modifying the read-only library.

## Dependency modules

Every node below changes only its `lean` record. Every repaired module changes
only module mode, declaration exposure and import visibility. The mathematical
signatures, definition bodies, proof docstrings and `sorry` proofs remain unchanged.
The older recorded interfaces were unusable because Lean rejects importing a
legacy non-module file from a required module-mode file. All repairs are in the
item's existing statement/proof prerequisite closure, and supply no new axioms,
hypotheses, specialized replacement definitions or altered statements.

- `lem-per-characteristic-zero-log-resolution-independence`:
  `Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence` becomes
  a module with exposed theorem and public imports of its signature's induced
  normalized resolution and log-stratum notions. It states exactly the existing
  characteristic-zero independence theorem, unchanged.
- `lem-trf-toric-realization-finite-type`:
  `Sheaf.AlgebraicGeometry.ToricRealizationFiniteType` becomes a module exposing
  the existing torus group abbreviations and theorem. Its canonical Hopf-defined
  groups and all finite-union/base-change clauses are unchanged. This is the
  characteristic-zero theorem's required proof import.
- `lem-trf-affine-monoid-algebra-normalization`:
  `Sheaf.RingTheory.AffineMonoidAlgebraNormalization` becomes a module exposing
  the five actual canonical monomial/fraction maps and the exact normalization
  theorem. This is required by the toric-realization module.
- `lem-trf-integral-support-saturation`:
  `Sheaf.RingTheory.IntegralSupportSaturation` becomes a module exposing the exact
  support-in-saturation theorem; required by affine monoid algebra normalization.
- `lem-trf-integral-support-weighted-initial-degree`:
  `Sheaf.RingTheory.IntegralSupportWeightedInitialDegree` becomes a module exposing
  its negative-weight nonintegrality theorem; required by support saturation.
- `lem-trf-monoid-algebra-domain-fraction`:
  `Sheaf.RingTheory.MonoidAlgebraDomainFraction` becomes a module exposing its exact
  domain/common-fraction-field theorem; required by the preceding two algebra modules.
- `lem-trf-monomial-integrality`:
  `Sheaf.RingTheory.MonomialIntegrality` becomes a module exposing its exact
  monomial and saturation integrality theorem; required by normalization.
- `lem-trf-saturated-monoid-algebra-normal`:
  `Sheaf.RingTheory.SaturatedMonoidAlgebraNormal` becomes a module exposing its exact
  integral-closedness theorem; required by normalization.


## Second reading by Q92

Independent second reading by the maintainer's review (the delivered section was a
self-audit by the worker; it is replaced by this reading). Read: the item node, its six
stmt_deps (rigidified-quotient-tower-comparison with its module
`RigidifiedQuotientTowerComparison.lean`: `Pair`, `Construction`, `IsFanInduced`,
`Comparison`; def-weil-regular-scheme; def-weil-pbc-adic-completion;
def-trf-strict-normal-crossings-boundary; def-trf-fs-log-blowup;
characteristic-zero-log-resolution-independence with `InducedNormalizedLogResolution`,
`RegularFunctorialNormalizedResolution`, `NormalizedResolutionOver.IsIsoOver`), the
procedure structures `LogBlowupTowerOver`, `LogBlowupComparison`,
`FSLogGroupAction`, Mathlib `IsRegularLocalRing`, `IsAdicComplete`, and ILO VIII 5.5.2
(printed p.127--128, PDF pp.133--134).

Clause by clause (node → Lean → verdict):

1. Fixed construction of [rigidified-quotient-tower-comparison] with the fan rule induced
   by one normalized regular-functorial char-0 algorithm → `F`, `D : InducedNormalizedLogResolution F`
   (pinned by `realizes`/`sharpens`/`onCharts`), `P`, `hP : IsFanInduced D.fanRule P`. Correct.
2. X = ∐_{i<m} Spec A_i, m finite → `m : ℕ`, `A : Fin m → Type u`,
   `components : X.logScheme.scheme ≅ ∐ fun i ↦ Spec (.of (A i))`. Correct; m = 0 allowed.
3. A_i complete Noetherian regular local, separably closed residue field →
   `IsRegularLocalRing` (extends `IsLocalRing`, `IsNoetherianRing`), `IsAdicComplete 𝔪 A_i`
   (Hausdorff + precomplete), `IsSepClosed (ResidueField A_i)`. Correct, nothing stronger.
4. Finite G acting tamely, abelian geometric inertia, free outside a G-strict SNC B →
   `G : Type v`, `[Group G] [Finite G]`, `Pair.tame/abelianInertia/boundary/snc/groupStrict/freeOutside/boundaryInvariant`,
   with `sameAction : HEq X.action.baseAction Y.action.baseAction` (baseAction : G →* Aut X.scheme)
   and `sameBoundary`. Correct.
5. Pair's further fields (Noetherian, regular, separated, admissible, generically free) are
   consequences here: a finite coproduct of spectra of regular local rings is affine,
   Noetherian, regular and separated; the whole affine X is an invariant affine open;
   B is SNC hence nowhere dense on the regular X, so freeness off B gives generic freeness.
   No added hypothesis.
6. B̄, B̄' invariant NC boundaries ⊇ B, enlarged divisorial log structure very tame → the two
   pairs' `enlargedBoundary`, `contains`, `normalCrossings`, `enlargedInvariant`, `divisorial`,
   `veryTame`; only `sameScheme` identifies the schemes, log structures may differ. Correct.
7. Resolve, pull back in fs log schemes, keep underlying normalized towers with ordered centers →
   `C₁ C₂ : Construction P _`: fs-Cartesian `LogBlowupComparison` with bijective count (full
   pullback), `center`, `normalized`, `algebraized`. Determined up to unique isomorphism, so
   quantifying over all presentations is the right (not a stronger) claim.
8. Towers equal including order and center ideals; not contracted per component →
   `Nonempty (UnderlyingIso C₁ C₂ (eqToIso sameScheme))`: order isos of the full index
   sets, stage isos commuting with arrows, base fixed to the identity of X, and
   `centers` equality of ideal sheaves by comap. Same content as `CenterIso` +
   `IsIsoOver` of the independence node, restated because `Construction` towers do not
   carry the `reduced` field of `NormalizedTower`. One global indexing. Correct.

Edge cases: m = 0 (empty scheme, both towers length 0), dimension-0 A_i (fields; B empty),
trivial G, B̄ = B̄', components permuted by G (no component-wise action assumed), residue
characteristic 0 or p (no restriction on A_i), proper principal centers retained (no
contraction in the conclusion). Universes: rings/schemes u, group v, as in `Pair.{u,v}`.

Records: item record complete, statement verbatim (whitespace-normalized equality checked);
characteristic-zero dependency record changes only `lean` (by/branch/declarations/note),
module body identical to live with only `module`, `public import` and
`@[expose] public section` added; the seven trf algebra modules are the same header-only
conversions required by its private import chain, with unchanged node records.
Searches: the worker's msearch queries cover LeanSearch/LeanFinder/Loogle/grep; my own
grep of lean/Sheaf and lean/WeilConjectures for `UnderlyingIso`, `CenterIso`,
`completeLocal` found only `Monoscheme.NormalizedTower.CenterIso` (different tower type)
and no existing statement of 5.5.2.
No mismatch in the Lean; only change: this section.
