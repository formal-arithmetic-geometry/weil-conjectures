## What changed

Repaired the landing refusal by importing and using the existing
`AlgebraicGeometry.Proj.localization_kernel_isHomogeneous` from
`Sheaf.AlgebraicGeometry.ProjBasicOpenLocalizationDetection`. Because that theorem
is private, the proof-only import now uses `import all`. This compiles without
changing the dependency module or either public interface.

Removed `twistGradingPolynomial`, `twistGradingPolynomial_coeff`, and
`twistLocalizationKernel_isHomogeneous`. The remaining private helper
`twist_local_component_zero` applies the existing kernel theorem directly.
The main proof still detects unwanted components using
`basicOpen_localization_detection`, then reconstructs the required homogeneous
fraction from the finite decomposition. The theorem signature, visibility,
public imports, and original docstring remain unchanged.

Updated the node's proof and proof origin to match this repair. Its proof
dependencies remain the two definitions and the existing detection node.
The unit's realized statement and proof steps are empty for this item, so the
unit route is unchanged. No other module is adapted.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Proj.twist_degree_detection`
(node `lem-sc-proj-twist-degree-detection`).

The retained private helper `twist_local_component_zero` is proved.
No sorry remains in the module, and no holes, modules, nodes, or axioms are added.
This is a proof, not a decomposition. The repaired module compiled cleanly with
`lcompile.py`. The delivery dry run printed OK, passed its axiom probe and
preflight except for the pending second reading, and pushed nothing. A separate
`tools/import_prune_check.py` run exited 0 with no findings, directly checking
the landing refusal that prompted this repair.

The proof still covers negative shifted degree, absent support components,
zero numerator, nilpotent f, and an empty basic open without new hypotheses.

## No longer needed

Removed the three duplicate polynomial/kernel helpers named above. Their
private constructions and McCoy argument are supplied by the existing imported
kernel theorem. No modules or DAG nodes are pruned; all original public imports
and the proof-only detection import remain needed. The redundant proof-only
`Mathlib.Algebra.Polynomial.AlgebraMap` import removed in the earlier delivery
remains absent.

The original plan's auxiliary graded localization, Laurent-polynomial
construction, and denominator enlargement remain unnecessary; the original
denominator suffices. These were unstated planned constructions with no modules
or nodes to prune.

## Where the brief, the DAG or earlier work was wrong

The returned delivery and its earlier second reading incorrectly treated private
visibility as requiring a duplicate proof. Lean's `import all` exposes the
existing private theorem to this proof without re-exporting it or modifying its
module. The returned duplicate theorem and both supporting polynomial helpers
have now been deleted, and the existing theorem is used directly.

The old second reading is removed because it validated the superseded proof;
the independent second reader must review the repaired delivery. There is no
statement correction or forced adaptation.

## Second reading by K3

1. **Reading and interface check.** Compared the delivered module and node with the repository. The public theorem signature and visibility are unchanged; the only module interface addition is a proof-only `import all`, and the existing localization-detection dependency is used as written. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the delivered module. The target's transitive axiom probe reports only the permitted logical axioms plus `sorryAx` inherited from an open imported declaration. Verdict: pass.

3. **Statements and duplication.** The private helper is a direct reduction to the existing homogeneous-kernel theorem, and the target statement is unchanged. Searches and repository grep found no duplicate public theorem or stronger/weaker replacement. Verdict: pass.

4. **Pruning and route.** The duplicate polynomial/kernel helpers are removed. The proof uses the existing basic-open detection theorem, finite homogeneous decomposition, and degree-zero fraction constructor; no unit route is bypassed and no additional holes or nodes are introduced. Verdict: pass.

5. **DAG consistency.** The node proof steps, `proof_deps`, and `proof_origin` describe the delivered proof and its imported detection node. The unit's realized route is unchanged. Verdict: pass.

Changed after this reading: no Lean declarations or statements; recorded this independent review and retained the repaired proof-only import and DAG metadata.
