## What changed

Replaced the sorry in `AlgebraicGeometry.diagonalConormalComparison_bijective_on_affine`
with a complete Lean proof from two affine coordinate theorems. The proof compares
linear maps on all Kähler generators using `CommRingCat.KaehlerDifferential.ext` and
`Scheme.Hom.relativeDifferentialsHomEquiv_symm_app_d`, then identifies the section
map with the composite of two linear equivalences and proves it bijective.
The original statement, universes, visibility and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSections` and
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineSections`, each containing one
public theorem with its source and complete proof in words. Updated the original
DAG proof and dependencies to record this decomposition. No definition or existing
interface was changed; no adaptations or change records are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.diagonalConormalComparison_bijective_on_affine`
(`lem-sc-diagonal-conormal-affine-comparison`). No sorry remains in the item's module.

Added and left:

- `AlgebraicGeometry.relativeDifferentials_affine_sections`
  (`lem-sc-relative-differentials-affine-sections`): the affine differential
  coordinate equivalence, with the formula on the universal derivation.
- `AlgebraicGeometry.diagonalConormal_affine_sections`
  (`lem-sc-diagonal-conormal-affine-sections`): the affine conormal coordinate
  equivalence, with its formula for every normalized derivation.

This is a decomposition: one upper hole closed, two lower holes added; net holes
closed minus added is −1. It is not an unconditional proof. Neither new statement
mentions the bijectivity of the original comparison. The first is independent of
the conormal sheaf and of D; the second is independent of the differential sheaf.
They are strictly separate parts of the original argument.

Edge cases checked mathematically: empty affine opens give zero section modules;
for the identity morphism both sides are zero; closed diagonal charts work without
assuming f is separated; changing the affine base only changes the displayed ring
map. The conormal identification is constructed independently of D, whose
normalization is used only for the generator formula. No data definition or arbitrary
choice of a witness of an unproved existence theorem was introduced.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.AffineConormalSections`,
`Sheaf.AlgebraicGeometry.BaseChangeConventions`,
`Sheaf.AlgebraicGeometry.DiagonalConormal`, and
`WeilConjectures.AlgebraicGeometry.Modules.Differentials`.
Replaced them with the two new proof imports. The original public import of
`Sheaf.AlgebraicGeometry.DiagonalConormalDerivation` is preserved.

Old direct `proof_deps` no longer used directly by the comparison proof:
`lem-weil-pbc-affine-conormal-sections`, `def-sc-diagonal-conormal`,
`def-pc-base-change`, `lem-sc-kahler-differentials-diagonal-ideal`, and
`lem-sc-diagonal-conormal-derivation-exists`. Their relevant constructions remain
in the new conormal coordinate plan or in the unchanged signature. The old direct
`def-sc-relative-differential-sheaf` dependency remains. Generator extensionality
uses `def-weil-pbc-kahler-differentials`, rather than the diagonal-ideal formula.

No mathematical dependency is globally pruned; pruned modules: none. The four removed direct imports
remain available or needed below the new chart statements. The original affine
conormal theorem, the ring-level Kähler/diagonal-ideal identification, the conormal
definition, base-change conventions, relative differentials and normalized
conormal derivations are still used in the decomposed plan. The unit route is kept;
no unit-level statement or proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing affine-conormal-sections theorem applies to an actual closed immersion
and its quasi-coherent ideal sheaf. The diagonal here need not be globally closed,
and its conormal uses the actual module-sheaf kernel. Thus it cannot be applied
directly: the ambient affine product chart, restriction of this kernel, and
compatibility of tensor pullback and its unit must first be identified. This is
recorded explicitly in the new conormal theorem, rather than assuming f separated.
No false statement was found.

The upstream differential restriction, base-open and Spec isomorphisms construct
the required differential-chart equivalence. A sandbox attempt constructs it and
its scalar transport; the remaining generator formula caused single-file compile
attempts to time out when transported through the concrete chart. No timed-out
proof or partial sorry is in the delivered modules. The attempt is retained only
under scratchpad for the second reader, outside the delivered Lean tree.
The work used about sixty minutes before finalization, including repeated single-file
compilations and attempts to close the differential-coordinate formula. A further
attempt generalizing the affine section-ring morphism also timed out, so the final
delivery keeps that chart statement as a single named theorem with a whole-proof sorry.
LeanSearch returned Internal Server Error; actual searches and unavailable responses
were recorded by msearch. The cited Stacks pages were read online.

## New nodes

`lem-sc-relative-differentials-affine-sections`, in
`dag/nodes/sec-picard-framework/lem-sc-relative-differentials-affine-sections.json`,
records the derivation-preserving affine differential equivalence (Tag 01UT).
Its Lean module is `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSections`.

`lem-sc-diagonal-conormal-affine-sections`, in
`dag/nodes/sec-picard-framework/lem-sc-diagonal-conormal-affine-sections.json`,
records conormal affine coordinates and the normalized derivation formula
(Tags 08S2, 01KJ, 01R3 and 00RW). Its Lean module is
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineSections`.

Both are sourced steps of the original plan. Each has three recorded kinds of
Mathlib searches, a statement with explicit dependencies, a complete proof plan,
and its exact Lean signature. There are no change records.

## Second reading by S1

1. **Existing interfaces — pass.** Read the diff against the repository version.
   The only existing module changes are the four replaced plain proof imports and
   the body of `AlgebraicGeometry.diagonalConormalComparison_bijective_on_affine`.
   Its signature, variables, universes, visibility, and docstring are byte-for-byte
   unchanged. Neither new module exists in the repository. No definition is added
   or altered, and no target or existing statement changes. No change record is needed.

2. **Proof and axioms — pass as a decomposition.** Compiled all three delivered
   modules through `lcompile.py --all`, in dependency order, without errors or
   warnings (5.8, 8.0, and 10.4 seconds). Read the comparison proof: generator
   extensionality proves `φ ∘ eΩ = eC`, evaluation at `eΩ.symm x` identifies the
   section map with a composite of equivalences, and composition gives bijectivity.
   Scratch copies with `#print axioms` for all three public declarations show only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Removed the scratch
   copies afterward. The only delivered sorries are the two named theorems listed
   above, each with a node and complete sourced proof docstring. No forbidden
   declarations, hidden holes, data definitions, or choices of arbitrary witnesses
   were introduced. The comparison consumes the existential equivalences only
   within a proposition proof.

3. **Split statements — pass.** Read the actual kernel-based `diagonalConormal`,
   the normalization predicate, the canonical tensor-pullback unit theorem, and
   `affine_conormal_sections`. Independently read Stacks
   [01UT](https://stacks.math.columbia.edu/tag/01UT),
   [08S2](https://stacks.math.columbia.edu/tag/08S2),
   [01KJ](https://stacks.math.columbia.edu/tag/01KJ),
   [01R3](https://stacks.math.columbia.edu/tag/01R3), and
   [00RW](https://stacks.math.columbia.edu/tag/00RW).
   The first split is solely differential coordinates with their generator formula;
   the second is solely conormal coordinates and the normalized difference formula.
   Neither asserts bijectivity of the original comparison. The second's chart is
   constructed before choosing a derivation, so its universal quantifier over D
   is justified. For the empty source chart both modules vanish; for an identity
   morphism the diagonal kernel and relative differentials vanish. For a
   nonseparated morphism the affine product chart still has a closed restricted
   diagonal, so no global closed-diagonal assumption is missing. The signs agree:
   `snd - fst` is `1 ⊗ a - a ⊗ 1`. No false or weakened statement was found.
   Searched again via msearch with different words using Lean Finder, Loogle, and
   grep, and searched the repository's scheme differential/conormal modules with
   rg. Read the upstream Spec, restriction, and base-open isomorphisms and their
   derivation formulas. The results are component lemmas, not an existing theorem
   with either split signature. The first worker's concrete chart attempt records
   the outstanding scalar transport/generator compatibility; it is not a small
   missing tactic that can be closed within this review pass. Both holes remain.

4. **Route, imports, and pruning — pass after reporting repair.** The proof takes
   the generator-extensionality route from the two separate affine identifications.
   Existing proved Spec/restriction/component results were checked; there is no
   shorter exact theorem found. Only imports needed by public signatures are
   public. The conormal module's plain proof imports retain its stated dependency
   plan. Checked `dag/units/sk-thm-picard-duality.json`: its `realized.statement`
   and sole `realized.steps` entry are empty in the baseline, so this delivery
   changes no realized unit node or fixed route. The local affine calculation
   below that unit is preserved. Expanded `No longer needed` to enumerate all
   five removed old direct proof dependencies and distinguish them from global
   pruning. Pruned modules: none. This closes one upper hole and adds two lower
   holes (net −1), and remains a decomposition, not an unconditional proof.

5. **DAG agreement — pass after dependency repair.** Checked all three node
   statements against their Lean signatures, and checked the new nodes' source,
   proof steps, dependency unions, search records, creation records, blueprint
   ancestry, chapter, unit, and Lean records. The original node incorrectly cited
   the diagonal-ideal identification for the extensionality step. Replaced that
   direct dependency with `def-weil-pbc-kahler-differentials`, which supplies the
   ring differential universal property used by `CommRingCat.KaehlerDifferential.ext`,
   and regenerated the exact union in `proof_deps`. The diagonal-ideal theorem
   remains a dependency of the new conormal coordinate node, where its quotient
   and generator formula are actually used.

Second-reading changes: corrected the comparison node's extensionality dependency
and its dependency union, completed the direct-pruning report, and added this
independent review. No delivered Lean proof or signature needed repair.
