## What changed

Repaired the returned delivery in the assigned module. Removed the three duplicate
private declarations and used the existing declarations directly:

- `Scheme.finite_sections_of_finiteType` is replaced by
  `Scheme.Modules.finite_sections_of_finiteType` from AffineSectionCoverTwistGeneration.
- `Scheme.mem_radical_annihilator_of_pow_torsion` is replaced by
  `AlgebraicGeometry.mem_radical_annihilator_of_pow_torsion` from CoherentAffineMapSupportRadical.
- `Scheme.power_multiplication_range` is replaced by
  `Scheme.Modules.multiplication_range` from Modules.IdealTimesQuasiCoherentAffineSections.

These existing helpers are private. Three proof-only `import all` lines make them
available without changing any library interface. Also removed the local `powers_qc`
copy and reused `Scheme.Modules.powers_qc` from the same ideal-product module.
The remaining `powers_range` proves the needed formula for arbitrary structure-module
maps and all natural-number degrees; the existing ideal-sheaf-data formula alone does
not have this signature. The theorem signature and visibility are unchanged.

Updated only `proof`, `proof_deps`, and `proof_origin` of the item's node to record
these reused results. No other module, definition, statement, or unit record changed.
Removed the obsolete second reading of the returned version; the repaired version
requires a fresh independent reading.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ideal_power_evaluation_affine_eventually_zero`
(node `lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero`).
No `sorry` remains in the delivered module. No new hole, node, or axiom was added.
The remaining private helpers are fully proved. This is not a decomposition.
The repaired module compiled cleanly through `lcompile.py`. The dry run checks
its declaration axioms and the maintainer preflight. Degree zero, zero ideals,
zero rings, and empty affine opens use the same unchanged argument.

## No longer needed

Removed direct imports relative to the original assigned module:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`;
- `Mathlib.Algebra.Module.LocalizedModule.Basic`;
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.

Additionally removed the returned version's direct imports of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and
`Mathlib.RingTheory.Support`. Their relevant declarations are available through
retained imports; the duplicated arguments that required them locally are gone.
The earlier redundant source Tilde and Mathlib Finiteness.Ideal imports also stay absent.

Direct proof-dependency nodes no longer used are
`lem-weil-pbc-quasi-coherent-finite-type-affine`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`def-weil-pbc-module-localization-away`.
The last four remain ingredients of the imported proved helpers, rather than
local proof steps. IdealTimesQuasiCoherentAffineSections and its node are now
retained, correcting the returned report's pruning claim.

These are direct dependency removals only; no whole-library pruning is claimed.
FormalPolynomialPowerLifts stays for its section-injectivity result. Its polynomial
lifting theorem is not used. The unit `sk-thm-p1` and every realized step stay unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned proof unnecessarily reproduced three existing private theorems.
The earlier second reading incorrectly treated their private visibility as preventing
reuse. Lean's `import all` gives access to those declarations; a scratch compilation
checked all three exact signatures before the repair. All three return findings are
repaired by direct calls, without renamed copies or changes to their statements.
Reusing the existing `powers_qc` removes a fourth unnecessary local argument.

The mathematical route remains the radical/annihilator variant of Stacks 01PM and
01PQ. Only the ownership of the supporting proofs changes. No statement correction,
forced adaptation, or new proof obligation is needed.

## Second reading by H2

1. Interface: PASS. Compared the entire module with the repository version using
   a file diff and checked the existing theorem signature byte for byte, including
   universes, monicity, quasi-coherence, finite type, the prescribed `one` and `r`,
   and both compatibility equations. They are unchanged. Both public imports and
   public visibility stay unchanged. The only delivered module is the assigned one;
   there are no definitions, change records, or forced adaptations.
2. Proof and trust: PASS. Independently compiled the delivered module through
   `lcompile.py` without errors or warnings. A scratch copy with `#print axioms`
   for the main theorem and all six remaining private helpers reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   No `sorry`, axiom, unsafe/opaque declaration, external implementation, or hollow
   definition occurs in the delivery. One original hole is closed; none is added.
3. Split statements and reuse: PASS; no split-off statement or new node exists.
   Read the exact signatures and proofs of the reused finite-section, multiplication,
   power quasi-coherence, and radical-annihilator helpers. Their hypotheses match:
   the finite-section helper needs no Noetherian hypothesis, and multiplication
   accepts arbitrary quasi-coherent structure-module maps. The local `powers_range`
   includes degree zero and arbitrary maps, whereas the existing ideal-data theorem
   assumes `IdealSheafData` and positive degree. The three duplicate declarations
   named in the return are absent and are replaced by direct calls.
4. Route and pruning: PASS. Read Stacks 01PM's injectivity argument and 01PQ's
   first proof paragraph at https://stacks.math.columbia.edu/tag/01PM and
   https://stacks.math.columbia.edu/tag/01PQ. The radical/annihilator route proves
   the same affine calculation: `J^k` annihilates the finite image of `phi`, and
   `hr` plus injectivity puts the prescribed transition image in `J^k P_n`.
   The final helper clears denominators on basic opens and uses separation on
   every subopen of V; it assumes quasi-coherence only for its source.
   Degree zero uses the unit and `J^0`; for `J=0` a positive power has zero
   section image, while the zero ring and empty affine open cause no excluded
   case. No nonempty generating set or positive degree is assumed.
   Searched independently with LeanFinder for affine detection and annihilator
   power containment, and with `rg` in both Lean roots for zero-on-sections,
   powers-range, and radical-annihilator lemmas. No shorter exact theorem was
   found: the affine detection results found elsewhere require an affine ambient
   scheme, while the imported module's analogous argument is a proof-local `have`.
   Every retained proof import supplies a directly used declaration; none is public.
   Compared the old `proof_deps` with the report: all four removed old dependencies
   are listed, and the two retained old ones remain. No whole-library pruning is
   claimed. Read `dag/units/sk-thm-p1.json`, including `realized`; the item is below
   its realized steps, which remain unchanged.
5. DAG: PASS. Compared the node JSONs: only `proof`, `proof_deps`, and
   `proof_origin` change. The five proof steps record the range induction, finite
   image, stalk/basic-open vanishing, radical power bound, and restricted morphism
   vanishing actually written in Lean. Their cited dependencies have matching
   modules and declarations; the text explicitly identifies the private helper
   used when the node's principal theorem is not called. `proof_deps` is exactly
   the union of those uses. No statement, source, unit, or Lean signature record
   is altered.

Second-reading changes: appended this independent review only. The repaired Lean
proof and node needed no further edits.
