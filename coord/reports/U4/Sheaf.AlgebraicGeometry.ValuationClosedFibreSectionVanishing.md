## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_nonzero_maximalIdeal_section_eq_zero`
in `Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing` without changing its
signature or public imports. The proof uses affine ideal kernels and compactness rather
than an inverse-limit diagram. Updated the existing node
`lem-sc-valuation-closed-fibre-section-vanishing` to describe this route.

Added proof imports of `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`,
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`,
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`,
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.

Three proved private helpers implement the affine kernel comparison, directed union of
principal ideal multiples, and finite principal upper-bound induction. In particular, the
first helper compares the canonical chosen adjunction with the adjunction used by the
closed-immersion quotient theorem; no assumption identifying these adjunctions is made.
All elaboration options are scoped to individual declarations. Single-file compilation
passes without warnings in approximately 21 seconds.

The source read was Stacks Tags 0EX8 and 01Z0 on their official pages. Searches through
msearch (LeanFinder, Loogle, grep) and rg on the source and Sheaf libraries found no exact
section-vanishing theorem. The directed-supremum calculation is already in Mathlib.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_nonzero_maximalIdeal_section_eq_zero`
(node `lem-sc-valuation-closed-fibre-section-vanishing`).

No sorry remains in the delivered module. No holes were added or split off. This is a
complete proof from existing declarations. The current compiled library has also
closed `AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`
(node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`). The final theorem and
all three private helpers use only `propext`, `Classical.choice`, and `Quot.sound`,
as checked with `#print axioms` in a scratch copy. The two other principal inputs are
the existing quotient-base-change ideal and closed-immersion unit-quotient declarations.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent`
and the proof dependency `lem-sc-valuation-limit-qcoh-section-descent`.
This proof also needs no inverse-limit cone, affine-transition limit theorem,
affine-pushforward colimit theorem, or directed-colimit cohomology calculation:
`Sheaf.AlgebraicGeometry.LimitAffineTransition`,
`Sheaf.AlgebraicGeometry.AffinePushforwardColimit`, and
`Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit` are unnecessary along
this proof route. This is pruning from this item, not a claim that these modules have
no other users. All original public imports were preserved. The second reader also removed the
redundant proof import `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`; its needed
declarations are already available through the retained imports.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old docstring records the planned inverse-limit
proof; the executable proof and updated node instead use the elementary affine
ideal-kernel route. The unit `sk-prop-av-cube` has no realized statement or proof-step
nodes here, so this change bypasses no fixed unit step.

The proof includes zero among the principal stages and inserts a separate nonzero
maximal-ideal element when taking the finite upper bound. This handles a zero section,
a zero local stage, and an empty scheme/empty finite cover. It does not assume flatness,
properness, a discrete valuation, or a finitely generated maximal ideal. The finite
presentation and quasi-separatedness assumptions remain unchanged even though the
finite-cover argument only uses quasi-compactness.

## Second reading by U4

1. Compared the delivered module and node with the repository using `diff`. The sole
   existing theorem signature is byte-for-byte identical (checked separately by extracting
   the text through `:= by`); all public imports and visibility are unchanged. Only three
   proved private helpers and declaration-scoped elaboration options were added. No
   definitions, target statements, or change records were introduced.
2. The module compiled without warnings. A scratch copy with `#print axioms` checks the
   theorem and each helper: only `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   or `extern`. Its local data are actual constructions or choices from proved results;
   no arbitrary witness is chosen from an unproved existence statement.
3. No statements were split off and no new holes were added. Read the three private
   helper proofs: the closed-immersion kernel is evaluated through a kernel isomorphism;
   the comparison automorphism makes the two adjunction units have equal kernels; the
   directed supremum and finite upper-bound arguments are elementary. Checked zero local
   sections, the zero global section, and an empty scheme/finite cover: the separate
   nonzero element in the finite bound handles all of them. Non-discrete valuation rings
   and non-finitely-generated maximal ideals are allowed by the directed-union argument.
4. Searched with LeanFinder for affine quasi-coherent closed-immersion kernels, Loogle for
   directed submodule membership, and `rg` on both Lean roots and Mathlib. No direct shorter
   section-vanishing theorem was found. Mathlib's `exists_of_res_zero_of_qcqs` concerns
   structure-sheaf sections on basic opens, so does not replace this argument. The proof
   already uses `Submodule.mem_iSup_of_directed`. Counterfactual compilation shows the
   ProjectionFormula import is needed for `IsInvertible.isQuasicoherent`; the LocalRing
   import is redundant and was removed. Every old dependency removed is listed above:
   only `lem-sc-valuation-limit-qcoh-section-descent`. The unit `sk-prop-av-cube` has empty
   `realized.statement` and `realized.steps` entries, so no fixed unit route is bypassed.
5. Read the changed node alongside the Lean proof. Its four proof steps describe the
   actual affine kernel, directed principal stages, compact finite bound, and sheaf
   uniqueness arguments. `proof_deps` is exactly the union of the steps' `uses`;
   `proof_origin` records the changed route. Other node fields are unchanged. No new
   nodes are needed because all helpers are proved and introduce no public interface.

Changes by the second reader: removed one redundant private Mathlib import; corrected
this report's stale claim that the affine ideal-times-module theorem still has a sorry;
recorded the axiom checks and the five review verdicts. The mathematical proof was sound
and was retained. The existing theorem docstring describes the old planned limit route;
the executable proof and node, and the affine argument documented in this report, give
the implemented route.
