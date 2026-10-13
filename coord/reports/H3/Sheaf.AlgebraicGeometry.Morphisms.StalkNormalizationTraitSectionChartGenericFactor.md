## What changed

Replaced the sorry in `GaloisCover.stalk_normalization_trait_section_chart_generic_factor`
by a proof from a concrete local root-algebra presentation. Added a proof-only import of
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation` and
`WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian`. The original signature,
public imports and visibility are unchanged. The main module contains the completely
proved private helper `root_maximalIdeal`.

The helper evaluates the defining polynomial to get the power relation, contracts the
maximal ideal along the local base map, and decomposes every polynomial into its constant
term plus a multiple of X. This proves the maximal-ideal formula. The valuation is the
existing proved `Ring.ordOfUnits`; its uniformizer value follows from
`Ring.ordOf_algebraMap_of_irreducible`. The remaining geometric theorem returns an actual
AdjoinRoot algebra and an auxiliary DVR uniformizer, rather than the target's abstract
ring generator or valuation conclusions. No data definition is chosen from its existence
statement: all witnesses are eliminated inside the theorem proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_chart_generic_factor`
(node `lem-sbc-stalk-normalization-trait-section-chart-generic-factor`).
The item's module has no remaining sorry.

Added one hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_root_presentation`
(node `lem-sbc-stalk-normalization-trait-section-root-presentation`). Its proof is exactly
`:= by sorry`. This is a decomposition: one hole closed and one added, net zero. The
local maximal-ideal calculation, power-membership assertion and valuation construction
are fully proved; the geometric normal-form construction remains open.

Compiled the sandbox modules in import order using lcompile.py. The dependent
normalization stalk expressions need an increased heartbeat budget, documented in the
main module. No signatures or definitions were changed.

## No longer needed

None. There were no proof-dependency imports or proof_deps in the original item. No
original import, node or module was removed. The existing `StalkNormalizationTraitCharts`
and `TraitGenericNormalizationCharts` interfaces were read but not imported: they do not
assert that the divisor equation pulls back to a uniformizer on the section, so they do
not supply the required geometric refinement. No unit-level route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node has three substantial proof steps but no proof dependencies. In
particular, the existing product-chart statements retain no compatibility between f and
the closed divisor or the transverse section. A root-chart theorem without that
compatibility cannot imply the generic-section factor in this item. The new theorem
records the needed concrete geometric input separately from its local algebra.

Read Stacks Tags 0EYH and 0EYI, especially the choice of the etale chart and the
unramified local section DVR preceding parts (1) and (2). Checked the new normal form
on an unramified factor (e=1), a ramified factor (e>1), and an empty cover (there is no x).
For a local R and f in m_R, the monic root algebra is finite integral and has unique
maximal ideal because its closed fibre is k(R)[T]/(T^e). Thus using the whole AdjoinRoot
algebra as the local stalk is valid. No rational-point hypothesis was added. The unit
record's realized arrays are empty, and its trait/section route is retained.

LeanFinder returned standard-etale-presentation results, not tame normalization.
LeanSearch returned an internal server error, recorded as unavailable. Logged grep in
Mathlib/AlgebraicGeometry found no tame root-presentation theorem. Library searches
found the weaker existing product-chart statements and the proved order-of-vanishing
homomorphism used here.

## New nodes

`lem-sbc-stalk-normalization-trait-section-root-presentation`, in
`dag/nodes/sec-smooth-base-change/`, states the geometric normal form as one public
 theorem in the new module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation`.
It retains the concrete root quotient, local flat normalization-stalk map, compatibility
of the base ideal, and the auxiliary section DVR and its generic open factor. It omits
the maximal-ideal formula, power-membership conclusion and valuation construction;
these are proved by the item. Its docstring gives the full geometric proof from the
source. No change record is needed because no existing interface changed.

## Second reading by H3

1. **Unchanged interfaces — pass.** Read the repository/sandbox diff of every delivered
   module. The sole existing public declaration's signature is byte-for-byte identical,
   including hypotheses, conclusion and visibility. All existing public imports remain.
   The added imports are proof-only. The other module is new; there are no changed data
   definitions, forced adaptations or undeclared interface changes.
2. **Proof and axioms — pass as a decomposition.** Independently compiled both modules
   in import order through lcompile.py, without errors or warnings. The item has no sorry;
   the new presentation theorem has exactly the reported `:= by sorry`. Scanned both
   files for forbidden declarations and kernel bypasses: none. A scratch-copy axiom
   check reports only propext, Classical.choice and Quot.sound for root_maximalIdeal and
   Ring.ordOfUnits. The item and presentation theorem additionally use sorryAx, exactly
   as expected from the one named geometric hole. No existence witness is used to define
   data: the presentation witnesses are eliminated only inside the theorem proof.
3. **Split statement — pass.** Read the complete new signature, docstring and node against
   [Stacks 0EYH](https://stacks.math.columbia.edu/tag/0EYH) and the construction before
   parts (1) and (2) of [0EYI](https://stacks.math.columbia.edu/tag/0EYI). The latter uses
   an unramified local section DVR before imposing the rational-point or splitting
   assumptions. Localizing the chart base at its point makes the entire finite root
   algebra local: all maximal ideals lie over the local base maximal ideal and the
   closed fibre is k[T]/(T^e). The etale local base map extends the original maximal
   ideal, giving the stated equality with J. The section pulls the divisor equation
   back to a uniformizer, giving the required generic open factor. Checked e=1,
   ramified e>1, nontrivial residue extensions and empty covers (no x). The lemma omits
   the three ideal/power/valuation conclusions now proved locally, so is a genuine
   geometric part of the argument, not a renamed copy of the item. It remains a
   substantial open theorem and cannot be closed in a few minutes. Independent
   LeanFinder (etale neighborhood/root of uniformizer), Loogle (AdjoinRoot.root and
   maximalIdeal), logged grep and direct library searches found no matching theorem.
4. **Route and pruning — pass.** Followed the proof from the item downward. Its ideal
   calculation is a direct polynomial constant-term decomposition, and its valuation
   is the already proved Ring.ordOfUnits. Read the existing trait product-chart and
   root-model interfaces: they lack the divisor/section compatibility needed here,
   so cannot replace the new geometric input. Both newly added imports are used.
   Original proof_deps is empty; no original dependency is pruned, and “No longer
   needed” is complete. Read sk-prop-input-spreading.json: its realized arrays are
   empty and the tame-chart/transverse-section route is retained.
5. **DAG agreement — pass.** Compared both recorded Lean statements verbatim with the
   source and checked that each proof_deps is the union of the proof-step uses. The
   existing node changes only proof, proof_deps and proof_origin. The new node has
   source, complete proof steps, all three search records, creation/blueprint/unit/
   chapter data and its matching Lean record. Its geometric steps agree with the
   docstring; the existing node describes the actual private-helper calculation and
   the proved valuation construction.

Second reading changes: appended this independent review and logged independent
searches. No Lean or node repair was necessary. Removed the temporary axiom-check
scratch copy. The delivery closes one named hole and adds one named hole (net zero),
with the local algebra and valuation calculations fully proved.
