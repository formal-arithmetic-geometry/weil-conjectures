## What changed

Completed `AlgebraicGeometry.affine_cap_section_open_algebra` without changing its signature
or public imports. All added helpers are private and fully proved in the same module.
On a rank-one principal chart, explicit evaluation and localization maps give inverse
algebra homomorphisms between the localized section quotient and the localization at the
section coefficient. Mathlib transports this calculation to the restricted spectrum map;
its Zariski-local criterion proves the global open-immersion assertion.

The image equality is proved directly, independently of the chart calculation. The quotient
relation excludes vanishing primes. A projective splitting supplies a coordinate functional
nonzero modulo any nonvanishing prime; its normalized residue-field evaluation yields a
prime of the quotient lying above that prime. Neither argument uses a holed declaration.

Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`.
The other four imports in the first worker's draft were redundant through retained imports
and were removed at second reading. Updated the existing node's proof, proof dependencies,
and proof origin to match the constructions. No new public statement or definition.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.affine_cap_section_open_algebra`
(node `lem-sc-affine-cap-section-open-algebra`). Added zero holes. No sorry remains in the
item or in any delivered file. This is a proof, not a decomposition.

Private helpers `section_quotient_localization`, `affine_cap_section_trivializing_chart`,
`section_not_mem_comap_smul`, `exists_dual_not_mem`, and `section_mem_range` are all proved.
The main theorem compiles with the original universes, binders, statement, and visibility.

Edge cases: for `N=R` and `s=a`, the construction is `R[t]/(at-1)=R_a`.
At `a=0`, both the section quotient and its localization are zero rings, and the image is
empty; the inverse-map argument requires no nontriviality hypothesis. At `a=1`, evaluation
and the structural map are inverse and the image is the whole spectrum. A chart with `f=0`
is empty and its rings are subsingleton; the localization argument still applies.
For the zero base ring the prime-indexed covering condition is vacuous, as required.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent`
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`

The following former proof dependencies are no longer needed by this item:
- `lem-weil-pbc-localization-quotient-commute`
- `lem-weil-pbc-symmetric-algebra-base-change`
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-localization-away-polynomial-quotient`
- `def-weil-pbc-fpqc-covering`
- `lem-galois-fpqc-descend-open-immersion`

The explicit maps replace the quotient/base-change/polynomial-identification route; target
Zariski locality replaces fpqc descent. The corresponding modules leave this item's import
closure; whether other targets still need them is for the global ledger to determine.
The unit `sk-thm-curveestimate` and its realized theorem are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt already contained the complete algebraic proof. This session checked it
against the current library, the unit record, and Stacks 01PV, and repaired the delivery
preflight failure caused by its additional `open CategoryTheory` command. Removed that
command and qualified `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`, preserving the
original module-visible commands.

No false statement or interface defect was found. The DAG's fpqc route was unnecessary below
the unit level. The theorem docstring and the updated node now record the implemented argument.
The local Stacks TeX file was absent on this machine, so the source was read at
https://stacks.math.columbia.edu/tag/01PV (the algebra argument in its proof).
LeanSearch returned an Internal Server Error, recorded as unavailable in `searches.jsonl`;
LeanFinder, Loogle, and local searches ran successfully. No matching ready-made theorem was
found. No forced adaptations and no new nodes.


## Second reading by A2

1. **Interfaces — pass.** Compared the delivered module with the repository using `diff`.
   The sole original theorem's complete signature, universes, binders, and visibility are
   byte for byte unchanged. All four public imports and the module-visible commands remain
   unchanged. The five added helper theorems are private. No definition or other module
   is changed; no change record is needed.
2. **Proof — pass.** Read the entire proof, including both explicitly constructed inverse
   maps and the residue-field evaluation. The original module compiled cleanly in 30.8 s.
   After pruning redundant imports, a scratch copy compiled in 25.4 s and
   `#print axioms AlgebraicGeometry.affine_cap_section_open_algebra` returned exactly
   `[propext, Classical.choice, Quot.sound]`. Scanned the delivered sources: no `sorry`,
   forbidden declaration, or kernel-checking bypass. No data is chosen from an unproved
   theorem; chart bases and the projective splitting come from proved Mathlib results.
3. **Split statements — pass, none.** Zero statements and zero holes were split off.
   The private coordinate-functional lemma holds for any ideal and projective module:
   the finite-support splitting formula proves its contrapositive. The chart calculation
   also handles coefficient zero or one and zero localizations. For the zero base ring
   the covering assertion is vacuous. Repeated Loogle search `SymmetricAlgebra,
   IsLocalization` (zero matches), LeanFinder search for the rank-one symmetric-algebra
   quotient spectrum (only localization/Proj results), and local Mathlib/upstream searches
   for `SymmetricAlgebra` in algebraic geometry and prime spectra: no ready-made theorem
   replaces this argument.
4. **Route and pruning — pass after repair.** The proof starts from the target and uses
   proved Mathlib declarations throughout. Read Stacks 01PV and the unit record
   `dag/units/sk-thm-curveestimate.json`: its realized statement is
   `thm-sc-proper-cohomology`, and its steps are empty. This auxiliary algebra calculation
   changes no unit step. The seven former proof dependencies listed in `No longer needed`
   are exactly the old `proof_deps` absent from the new proof. The two removed Sheaf
   imports are the pruned modules for this delivery; global reachability is for the ledger.
   Removed four redundant draft proof imports: `Mathlib.LinearAlgebra.Dimension.Free`,
   `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`,
   `Mathlib.AlgebraicGeometry.AffineScheme`, and `Mathlib.RingTheory.Localization.Module`.
   Their declarations remain available through the retained imports. All proof imports
   are plain `import`; public imports are used by the original statement.
5. **DAG — pass after repair.** Compared the node with the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. Its six steps match the actual chart,
   localization, inverse-map, restriction, and image arguments. Checked the Mathlib
   declarations of the listed dependency nodes. Removed the unused draft dependency
   `lem-weil-pbc-finite-projective-rank-locally-constant` from step 1 and `proof_deps`:
   the code uses spreading freeness directly, not local constancy of rank. No new node.

Second-reading changes: pruned four redundant proof imports, corrected the theorem's
outdated fpqc docstring to describe the implemented proof, removed one unused DAG
dependency, and updated this report. No mathematical proof repair was necessary.
