## What changed

Replaced the sole sorry of `IntegralTensorPullback.preserves_and_completed` by a
complete combining proof with its original signature. Exact inverse image preserves
bounds and homology; the existing generic `pullback_constructible` proof pulls back
the constructible stratification and its finite constant local models. The internal
integral residue criterion supplies derived completeness of the ordinary inverse
image. The native K-flat pullback lemma and `mapDerivedCategoryFactors` identify its
representative. The completion criterion, the ordinary normalization equation and
cancellation of isomorphisms prove invertibility of the specified comparison.
Localization of the separate constant normalization equation proves the final clause.

The two remaining strict normalization steps are named public theorems in separate
modules, with complete proof plans and DAG nodes. They are chain-level identities
for arbitrary complexes, independent of bounded constructibility or completeness.
Each is strictly one part of the original argument: neither proves preservation of
constructibility, derived completeness, invertibility of the original map, or the
other normalization clause. The main theorem contains the actual Lean assembly.

Moved the existing data declarations and their proved helper lemmas verbatim to
`Sheaf.Paper.IntegralTensorPullbackData`, publicly re-exported by the original module.
This permits the two new lemmas to depend on the comparison data without importing
the theorem that uses them. This extraction resolves that import cycle; it is not a
split to avoid a compile-time limit. Existing names, signatures, bodies, attributes
and public dependencies are preserved. No downstream source or adopted source-library
module changes. The node attachments and original proof route now follow the code.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.IntegralTensorPullback.preserves_and_completed`
(node `det-lem-int-tensor-pullback`). Its complete proof uses the two new statements.

Added exactly two holes, each with body `:= by sorry`:

- `AlgebraicGeometry.ProEtale.IntegralTensorPullback.ordinary_roos_unit`, in
  `Sheaf.Paper.IntegralPullbackInternalRoosUnit`, node
  `lem-sfb-internal-pullback-roos-unit`.
- `AlgebraicGeometry.ProEtale.IntegralTensorPullback.constant_roos_unit`, in
  `Sheaf.Paper.IntegralPullbackConstantRoosUnit`, node
  `lem-sfb-internal-pullback-constant-roos-unit`.

This is a decomposition: one original hole closed and two strictly simpler holes
added, not a net proof or a claim that the theorem is axiom-free. The original item
and the extracted data module contain zero sorry. No definition contains sorry.
The split statements were checked on the zero complex, empty schemes and the identity
morphism; their constructions require no excluded or additional hypotheses.

## No longer needed

Removed the private proof imports `Sheaf.Paper.CartesianCoefficients`,
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` and
`Sheaf.Paper.IntegralModels` from the relocated data. Their declarations are not used
by its helper proofs. Retained all seven original public imports and the other
private proof imports actually used by the data constructions.

The original proof assembly no longer needs these declared proof dependencies:

- `lem-sfb-integral-bounded-stratum-base-change`
  (`Sheaf.Paper.IntegralBoundedStratumBaseChange`),
  `det-lem-int-tensor-shriek` (`Sheaf.Paper.IntegralTensorShriek`), and
  `sk-lem-int-integral-heart` (`Sheaf.Paper.IntegralConstructibleHeart`): the already
  proved generic constructibility pullback lemma applies directly to cohomology.
- `lem-sfb-scalar-matrix-inverse-image`
  (`Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage`) and
  `lem-sfb-pullback-constant-model-constructible`
  (`Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible`): the stronger
  admissible-coefficient statement and specified-presentation clauses are unnecessary;
  the generic proved helper uses the existing pullback of finite constant models.
- `sk-lem-integral-models` (`Sheaf.Paper.IntegralModels`): its embedded-coefficient
  specialization is replaced by the existing actual internal residue criterion's
  completeness implication, never its preservation clause.
- `lem-sfb-integral-pullback-strict-roos-normalization`
  (`Sheaf.Paper.IntegralPullbackStrictRoosNormalization`): this is formulated for
  sectionwise ring-sheaf modules. The two new nodes state only its actual internal
  coefficient normalization steps, so no presentation equivalence is silently assumed.
- `def-weil-pbc-completed-pullback` remains a statement dependency/context for the
  comparison data, but its sectionwise construction is not applied in the proof.

Removed obsolete top-level tool approvals for
`lem-weil-pbc-condensed-open-closed-recollement`,
`lem-weil-pbc-proetale-ringed-open-closed`, `sk-lem-integral-models`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`lem-weil-pbc-constant-completion-equivalence`, and
`lem-sfb-scalar-matrix-inverse-image`, and
`lem-sfb-pullback-constant-model-constructible` from the original node. The finite coefficient
limit remains in the new constant normalization node's proof plan, where it is needed.
No new top-level approvals are added or existing approvals reordered.

No library module is withdrawn or claimed globally unreachable: these nodes may have
other consumers, including unfinished parent proofs. No adopted source declaration is
removed, weakened, or replaced by sorry. Final module pruning count: none.

## Where the brief, the DAG or earlier work was wrong

The old strict Roos normalization dependency uses sectionwise `SheafOfModules`,
whereas this theorem uses internal modules over the actual continuous condensed
coefficient. It cannot be applied directly. Its mathematical normalization argument
is valid, but its internal instance and augmentation equations still require proof;
the two new nodes record precisely those parts.

The older devissage proof plan is longer than needed for the existing definition of
bounded constructible: exact pullback commutes with homology, and the generic proved
helper in `UnboundedLocalizingPullback` already handles arbitrary commutative condensed
coefficients. This is a use of its private, fully proved constructibility helper,
not of its larger unbounded theorem or any extra conclusion. The internal residue
criterion is likewise used only for completeness of an already constructible object.
These are generic tools for the existing local-model/completeness steps; the unit
record has no assigned `realized` entries, and no unit statement is changed. Any
additional maintainer approval for these already proved generic tools is left to the
independent review; top-level `tool_uses` additions are not made by this worker.

## New nodes

`def-sfb-integral-pullback-comparison-data` attaches the verbatim relocated comparison
data and its already proved well-definedness lemmas. It introduces no new mathematical
construction and no hole.

`lem-sfb-internal-pullback-roos-unit` is the chain isomorphism from the pulled quotient
Roos cocone to ordinary completion, retaining its augmentation. Its proof plan uses
the point-pullback coefficient isomorphism, the monoidal tensorator, product comparison
and the explicit cocone-to-Roos coordinate sign.

`lem-sfb-internal-pullback-constant-roos-unit` is the independent scalar-restriction
chain isomorphism and its augmentation equation. Its proof plan uses finite quotient
coefficient comparison, associativity of balanced tensor products, the normalized
restriction square, and preservation of products and cocones.

Change record: `coord/changes/A2-integral-pullback-comparison-data.md`. Three forms of
Mathlib search and blueprint duplicate searches were performed; only generic cone
and ordinary ring-completion tools matched, not these internal augmented comparisons.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
