## What changed

Proved AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion by applying the existing kernel estimate and the restored cokernel estimate at every e, with exactly the original inputs and exponent 4*t.

Restored the commented public theorems AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel and AlgebraicGeometry.completion_thickening_cokernel_reflection in their existing modules. The cokernel comparison uses ObjectProperty.homMk and cokernel.mapIso with its implicit first map. Reflection now proves coherence of the ideal product through its identification with the kernel of a coherent quotient projection, uses the public idealModuleProduct_exact_calculus for support, and reuses the existing proved private epimorphism helper in CoherentMapReductionTorsionCoker. It does not access private helpers of the retired CoherentFormalModule file. The supported completion faithfulness argument and all recorded signatures are preserved.

Updated the three existing DAG nodes to match the proof. Change record: coord/changes/K2-second-adic-torsion-cokernel-restoration.md. Neither dependency module has a current holder, so these are repairs of unclaimed modules, not forced adaptations of another group's work.

## Proved and sorry left

Closed the single original hole: AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion (lem-weil-pbc-devissage-second-adic-system-torsion). Original holes: 1; remaining holes in the assigned module: 0; new holes: 0; split-offs: 0. This is a proof from existing declarations, not a new decomposition.

Also restored complete proofs, without introducing holes, of AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel (lem-weil-pbc-devissage-second-adic-system-torsion-cokernel) and AlgebraicGeometry.completion_thickening_cokernel_reflection (lem-weil-pbc-completion-thickening-cokernel-reflection). The two private helpers in the reflection module are proved. There is no sorry in any delivered Lean file. Existing transitive dependencies may still have their own holes; this delivery does not claim to close them.

All three delivered modules compile individually in dependency order with lcompile.py --all.

## No longer needed

Removed direct proof imports from GrothendieckDevissageSecondAdicSystemTorsion:

- Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence (lem-weil-pbc-closed-immersion-coherent-equivalence).
- Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated (lem-weil-pbc-formal-systems-annihilated-by-power).
- Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal (lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal).

These are no longer direct proof dependencies of the conjunction theorem; the existing half-estimates retain the lower theory they require, so no claim is made that all three modules leave the global import closure. The main node now cites only its kernel and cokernel half-estimates. Its statement/definition imports are unchanged.

Removed import all Sheaf.AlgebraicGeometry.CoherentFormalModule from the restored reflection proof. Its old private quasi-coherence helpers are unnecessary: coherence of the quotient and its kernel suffice. Added private proof imports of IdealModuleProductExactCalculus and all CoherentMapReductionTorsionCoker instead. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing kernel/cokernel decomposition was sufficient for the main theorem, but the cokernel declaration and its reflection dependency had been commented out during the upstream sync. Simply applying the recorded declaration would therefore fail against current sources. They are restored and included in the same delivery. Access through import all to private declarations in CoherentFormalModule was invalidated when that module became a re-export wrapper. A small three-module compilation experiment confirmed that import all does not reveal private declarations through a public re-export; the temporary experiment sources have been removed.

A direct import of the new upstream CoherentFormalModule was unavailable in the published compiled snapshot during this session. The delivered proof avoids that direct import and its private API entirely. It uses public re-exported formal-module declarations and an existing stable reduction helper. No statement, definition, source conclusion, or target signature is weakened or changed. Empty schemes, zero modules, and zero or unit ideals remain covered; s-1 is used only with the supplied hypothesis 1 <= s. Faithfulness is taken on the supported coherent category globally, never assumed for an individual affine completion.

## Second reading by K2

1. **Signatures and accidental changes.** Compared all three delivered modules with the repository versions. The main target declaration is byte-for-byte unchanged. The two dependency theorems were commented out in the repository sync and are restored with the exact signatures recorded in their DAG nodes; no definition or target statement was altered. Verdict: pass.

2. **Proof and axioms.** Compiled the three modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all` in dependency order; all compiled cleanly. The delivered files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The proofs use existing declarations and the permitted categorical/classical machinery. Verdict: pass.

3. **Split-off statements.** No new statements were split off. The restored cokernel theorem and completion-reflection theorem are existing DAG nodes, are strictly needed by the target route, and their statements agree with the nodes and source argument. Local searches found no duplicate upstream or Mathlib declaration. Verdict: pass.

4. **Shortest route and pruning.** The target proof pairs the existing kernel and restored cokernel estimates directly. The reflection proof avoids retired private formal-module helpers, using public coherence, exact annihilator calculus, and the existing reduction epimorphism helper. Three unused direct imports of the target were removed and recorded under `## No longer needed`; the unit route through both quantitative halves is retained. Verdict: pass.

5. **DAG agreement.** Updated `proof`, `proof_deps`, and `proof_origin` for the three nodes to match the Lean proofs and imports. The realized unit remains `sk-thm-p1`; no new node or change record is missing. Verdict: pass.

Changed during second reading: no Lean proof changes; this section records the checks above. The required restoration change is recorded in `coord/changes/K2-second-adic-torsion-cokernel-restoration.md`.
