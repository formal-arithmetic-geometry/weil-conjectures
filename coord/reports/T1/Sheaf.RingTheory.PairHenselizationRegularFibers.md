## What changed

`Sheaf.RingTheory.PairHenselizationRegularFibers`: replaced the proof hole in
`RingTheory.pair_henselization_regular_fibers` with a complete reduction, keeping its
signature and both public imports unchanged. Two proved private helpers transfer regularity
and geometric regularity to an `IsLocalization`. The latter proves Noetherianity and handles
every finite purely inseparable scalar extension by Mathlib tensor localization. The main
proof constructs the canonical fibre map, verifies its pure-tensor formula, applies the
structural calculation, and uses `Algebra.isGeometricallyRegular_of_isSeparable`.

Added `Sheaf.RingTheory.PairHenselizationFiberLocalization`, containing the one remaining
structural calculation: the canonical residue extension is separable algebraic and the
canonical fibre map is a localization. This is steps 1–2 and the idempotent description
from the old plan, independent of any regularity hypothesis. It does not assert geometric
regularity, flatness, or regularity of a ring map. Thus it is strictly a part of the original
argument, rather than the original statement with different notation.

Proof imports added to the item: `Sheaf.RingTheory.PairHenselizationFiberLocalization`,
`Mathlib.RingTheory.Localization.Submodule`, and
`Mathlib.RingTheory.Localization.BaseChange`. Both delivered modules compile together with
`lcompile.py --all`; verification is repeated by the delivery dry run. No existing public
statement, definition, visibility, or instance is changed. No forced adaptations are needed.

## Proved and sorry left

Closed the original hole:
`RingTheory.pair_henselization_regular_fibers`
(node `lem-weil-pbc-pair-henselization-regular-fibers`). There is no `sorry` in the item.

The private helpers `regular_localization` and `geometricallyRegular_localization` are proved.

Added exactly one hole:
`RingTheory.pair_henselization_fiber_localization`
(node `lem-weil-pbc-pair-henselization-fiber-localization`), in its own new module.
Its proof is exactly `by sorry`, with the source and full natural-language proof in the
public theorem's docstring. No definition is added and no data is chosen from an unproved
existence theorem. The localization submonoid is used only within a proof of a proposition.

Accounting: one upper hole closed and one structural hole added; this is a decomposition,
net zero holes closed, not an unconditional proof of the original result.

Edge cases checked mathematically: for B=A the canonical fibre map is an isomorphism and
M={1} works; a finite product projection localizes at its selected idempotent; a zero
selected fibre localizes by the same idempotent even when its image is zero=one. A prime q
provides an index, so the empty-product case supplies no q to check. The generic transfer
proof imposes no nontriviality condition on the rings being localized.

## No longer needed

Removed from the item's proof imports:

- `Sheaf.RingTheory.PairHenselizationFiltered`;
- `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`;
- `Mathlib.RingTheory.TensorProduct.Pi`;
- `Mathlib.RingTheory.Noetherian.Basic`.

The first two modules and the product/tensor cancellation facts remain part of the new
structural node's plan and are retained as proof-only imports of its module after second
reading; they are relocated dependencies, not mathematical pruning.
The item directly uses neither
`lem-weil-pbc-pair-henselization-filtered`,
`lem-weil-pbc-henselization-finite-separable-fibres`,
`lem-weil-pbc-tensor-cancel-base-change`, nor
`lem-weil-pbc-algebra-tensor-product-distributes-product`; those four dependencies are
now below `lem-weil-pbc-pair-henselization-fiber-localization`.

`lem-weil-pbc-surjective-image-noetherian` is genuinely unnecessary for this route:
Noetherianity follows from localization, rather than a separate quotient argument.
Its recorded Mathlib declaration needs no new proof. The retained project proof imports
are `LocalizationOfRegularRing` and `GeometricRegularitySeparableExtension`, both applied
explicitly. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement or changed target was found. The old plan omitted the
universe conversion required to apply the existing finite-separable-fibres theorem:
its indexing category and algebra carriers share a universe, whereas the full category of
rings under A has its objects one universe higher. A scratch experiment successfully
constructed the transported cocone and its colimit proof, embedded the indexing category
fully faithfully in `FGAlgCat A`, used `equivSmallModel`, reindexed the cocone, constructed
the colimit-point algebra equivalence, transported Noetherianity, and applied
`CommAlgCat.finite_separable_fibers_of_etale_colimit` to the small diagram. The existing
`RingTheory.pair_henselization_essentiallySmall` supplies the smallness fact directly;
its node is included in the new structural proof plan. The subsequent canonical
residue-field/product and tensor identifications remain to be proved in the new item.

The supplied literature path is absent in this clone. The Stacks source was read at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/more-algebra.tex`, labels
`lemma-filtered-colimit-etale-noetherian-fibres` and `lemma-henselization-pair-G-ring`.
These are the cited Tags 0AH1 and 0AH3. No source was fabricated or downloaded into the
read-only repository.

LeanSearch was attempted and returned Internal Server Error; the unavailable result is
recorded honestly. LeanFinder, Loogle and the Mathlib grep ran through the supplied search
wrapper, and repository/blueprint searches found no existing statement of the combined
canonical fibre-localization calculation. The fixed unit `sk-thm-p1` is unchanged.

## New nodes

`lem-weil-pbc-pair-henselization-fiber-localization` states the separable residue extension
and the localization description of the canonical fibre map, without a regularity premise.
Its proof plan retains filteredness, essential smallness, finite-separable fibre decomposition,
tensor cancellation and tensor distribution; the final projection calculation spells out
all three localization axioms. Its Lean record points to
`lean/Sheaf/RingTheory/PairHenselizationFiberLocalization.lean`.
No change record is required: all existing signatures and public imports are unchanged.

## Second reading by T1

1. **Interface: pass.** Compared the complete item with the repository using `diff -u`.
   The text from `theorem pair_henselization_regular_fibers` through its result type
   is byte for byte unchanged; a separate Python assertion checked this. Its docstring,
   universes, section visibility and both public imports are unchanged. There are no
   existing definition changes, statement changes, or forced adaptations. The only
   new public declaration is the structural lemma in its own module.

2. **Proof and trust: pass as a decomposition.** Both delivered modules compiled
   together with the mandatory `lcompile.py --all`, including after the import repair.
   Read the fraction/kernel argument in `regular_localization`, the scalar tower and
   mapped-submonoid construction in `geometricallyRegular_localization`, and the main
   proof's canonical residue map, tensor lift and pure-tensor compatibility equation.
   In a scratch copy, `#print axioms` for both private helpers returned exactly
   `propext`, `Classical.choice`, `Quot.sound`; for both public theorems it additionally
   returned `sorryAx`. The sole delivered hole is exactly the named structural theorem
   listed above. There are no new definitions, data witnesses chosen from an unproved
   existence theorem, or forbidden trust mechanisms. The submonoid witness is used
   only inside a proof of a proposition. One upper hole closed and one lower hole
   added is net zero, not an unconditional proof.

3. **Split statement and source: pass.** Read Stacks `more-algebra.tex` at the available
   local source path recorded above, labels `lemma-filtered-colimit-etale-noetherian-fibres`
   (0AH1) and `lemma-henselization-pair-G-ring` (0AH3). The first supplies the finite
   canonical product and separable algebraic residue extensions for a Noetherian
   filtered etale colimit. Tensoring that product over B with arbitrary C, rather
   than the completion in 0AH3, gives the stated canonical map. Its selected factor
   is localization at the pulled-back coordinate idempotent. The Lean hypotheses
   fix rho to the canonical residue map and phi on all pure tensors, so an arbitrary
   different ring map is not allowed. Checked identity B=A, a two-factor projection,
   C the zero ring, and a zero selected component; denominators still map to one,
   extension by zero gives surjectivity, and multiplication by the idempotent kills
   precisely the projection kernel. If B is zero there is no prime q. The lemma has
   no regularity hypothesis or regularity conclusion, and isolates the structural
   part of the argument rather than restating the item. Its named hole has a source,
   complete docstring proof and matching new node. Fresh LeanFinder, Loogle and grep
   searches used projection/idempotent terminology. Mathlib provides
   `IsLocalization.away_of_isIdempotentElem` and related APIs for the last step;
   `FinitePresentationLocal.lean` and upstream `ProEtale/StalkIso.lean` use them.
   None provides the whole fibre decomposition and residue-extension calculation.
   Recorded these partial matches in the new node; no small isolated hole was
   available to close without undertaking the remaining transport/tensor calculation.

4. **Route and pruning: pass after repair.** The main proof applies the existing
   regular-localization and separable-extension theorems directly. No shorter complete
   route was found in Mathlib or either project root. Checked `sk-thm-p1.json`'s
   `realized` statement and steps: this decomposition stays below them and bypasses
   none. The five old proof dependencies absent from the item's new `proof_deps`
   are all accounted for in `No longer needed`: four move below the structural
   lemma, while surjective-image Noetherianity is replaced by Mathlib localization
   Noetherianity. No whole project module is claimed pruned. Found and repaired a
   discrepancy: the structural module had not actually retained its planned proof
   imports. Added plain imports of `PairHenselizationFiltered`,
   `PairHenselizationEssentiallySmall`, `FiniteSeparableFibersOfEtaleColimit`,
   `Mathlib.RingTheory.TensorProduct.Maps` and `Mathlib.RingTheory.TensorProduct.Pi`.
   These deliberately retain the unresolved theorem's proof-dependency plan and
   its import closure; none is public. Other imports support signatures or the
   implemented proof. Existing public imports are preserved.

5. **DAG: pass.** Compared both Lean signatures with their node `lean.statement`
   records and checked that each node's `proof_deps` equals the union of its steps'
   `uses`. The existing node differs only in `proof`, `proof_deps`, `proof_origin`.
   The new node has the required source, statement dependencies, elementary
   projection step, search records, creation record, blueprint ancestry, split status,
   matching chapter/unit and complete Lean record. Its Noetherian, canonical-map,
   separability and localization clauses match the Lean declaration. The existing
   node describes the actual tensor lift, localization after finite purely
   inseparable scalar extension, and separable-field ascent in the proof.

Second reading changed only the structural module's five retained proof imports,
its node's independent search evidence, and this report (including the dependency
relocation clarification). It changed no theorem statement or definition.
