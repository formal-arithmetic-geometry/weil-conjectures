## What changed

Replaced the hole in AlgebraicGeometry.affine_chart_ordinary_map_descent with the
upper-tail partial-order quotient argument, finite presentation of the explicitly
constructed section modules, and the map clause of
ModuleCat.finitePresentation_descent_directedColimit. The final algebraic square
is transported by a new affine Hom comparison theorem. All original signatures
and visibility are unchanged. Added proof imports of AffineChartOrdinaryHomComparison,
Modules.FiniteDescent, and Mathlib.AlgebraicGeometry.Morphisms.Affine.

The new module constructs its ring diagram from upperTailChartDiagram and global
sections. Its base modules are sections of actual ordinary pullbacks. Every data
definition is complete. The remaining theorem supplies only Hom comparisons and
transport of a supplied commuting square, without finite-presentation assumptions
or existence of a stage map. This is the geometric part of the existing plan,
strictly separate from the algebraic descent now used in the main proof.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.affine_chart_ordinary_map_descent
(lem-pc-affine-chart-ordinary-map-descent), conditional on the new comparison theorem.
The private ordinaryChartBaseModule_finitePresentation helper is fully proved.
Added one hole: AlgebraicGeometry.affine_chart_ordinary_hom_comparison
(lem-pc-affine-chart-ordinary-hom-comparison), the sole sorry in the delivery.
This is a decomposition: one upper hole closed and one geometric hole added, net zero.

The actual four-module sandbox set compiled with lcompile.py in import order,
without errors or warnings: AffineChartUpperTailLimitData (4.9 seconds),
ChartOrdinaryMapRecovery (2.1 seconds), AffineChartOrdinaryHomComparison
(11.8 seconds), and AffineChartOrdinaryMapDescent (14.3 seconds).
The first two modules are byte-for-byte unchanged dependency copies; they are
not changes or forced adaptations and are not staged by the delivery tool.
The earlier missing-dependency blockage is superseded by this module-set check.

## No longer needed

No original imports removed. No original module can be claimed pruned. The old direct proof dependencies no longer used are pqf-def-coherent and
def-pc-chart-ordinary-map-recovery: their geometric roles now occur inside the
comparison node. The recovery definition remains in the unchanged signature,
and quasi-coherence remains a hypothesis and a dependency of the comparison;
neither module is pruned. The old def-pc-fibre-product and
lem-pc-fp-module-map-descent-affine proof dependencies are retained. The new
finite-presentation sections dependency names the proved upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The original dependencies name definitions of quasi-coherence and pullbacks, but
provide no geometric Hom comparison to scalar extension. Algebraic finite-presentation
descent alone does not supply this interface. The new node isolates precisely that
gap. Its proof uses no ambient tensor-pullback comparison and no sheaf gluing.

Read Stacks Tags 01ZR, 05N7 and 01I6 online. Checked the starting representative,
mutually comparable distinct indices, the empty affine chart, zero ring and zero
modules: all comparisons are universal-property comparisons and need no nonzero
or nonempty hypothesis. The tail itself contains j, so the algebraic descent
lemma's Nonempty assumption is available even if I was not separately declared
nonempty. The unit realization table is empty for this node; its unit route stays.

## New nodes

lem-pc-affine-chart-ordinary-hom-comparison: canonical affine Hom comparisons for
an explicit upper-tail chart ring diagram, and transport of a supplied normalized
algebraic square to ordinary recovery. Module:
lean/Sheaf/AlgebraicGeometry/AffineChartOrdinaryHomComparison.lean. No change records
or forced adaptations.

## Earlier second reading (a previous round; superseded)

The saved reduction was independently checked by compiling all sandbox modules after
including the two source dependencies that were absent from the published compiled
library. The main theorem's signature is unchanged and its proof uses the comparison
node exactly as stated. The new comparison theorem is strictly weaker than the main
descent theorem: it supplies only affine Hom transport and leaves its geometric
comparison as the named documented `sorry`. The upper-tail unit route is retained.

## Second reading by R1

1. Compared every sandbox module with the repository. The two dependency copies
are byte-for-byte identical. In AffineChartOrdinaryMapDescent the existing theorem
signature and docstring are byte-for-byte identical; only its proof, a private
proved helper, and three plain proof imports were added. The comparison module is
new. No definition, existing signature, visibility, or target changed. Verdict: pass.

2. Compiled all four actual modules in import order through lcompile.py, without
errors or warnings. Scanned the delivered Lean text: exactly one sorry, the whole
proof of affine_chart_ordinary_hom_comparison; no prohibited declarations or
hollow definitions. Explicit axiom checks on scratch copies cover the main theorem,
the private finite-presentation helper, and every new comparison-module declaration.
The allowed standard axioms and the reported comparison's sorryAx are the only
axioms. The concrete diagram and section-module definitions do not use sorryAx.
Verdict: pass, conditional proof/decomposition as reported.

3. Read the new comparison statement, complete docstring argument, and node.
Independently checked the singleton index, distinct mutually comparable indices,
starting representative, zero ring, empty chart and zero modules. The representative
of the class of j is equivalent to j; its scheme transition is an isomorphism.
Scalar-extension linear maps are determined by 1-tensors, so the normalization
forces the composition comparisons. This statement does not assert existence of
any stage map and does not assume finite presentation; algebraic map descent is
a separate, already proved input. No arbitrary object is chosen from an unproved
existence theorem. Repeated leanfinder and loogle with comparison/pullback queries
and msearch grep, and searched both Lean roots. PullbackTilde supplies
pullbackSpecΓEquiv and its one-tensor equation; FaithfullyFlatDescent supplies
hom_ext_of_isQuasicoherent_Spec and exists_hom_app_top_eq. These are supporting
pieces, not this combined chart/cone/pasting comparison. The full remaining
geometric theorem cannot be closed in a few minutes by any result located.
Read Stacks 01ZR, 01I6, 0095 and 0096 independently. Verdict: true, needed and
strictly a geometric part of the argument; one documented split retained.

4. Traced the proof from the descent goal: directed quotient, concrete chart rings,
finite presentation of actual pullback sections, inverse Hom comparison, the map
clause of finitePresentation_descent_directedColimit, and transport of its normalized
square. This is a genuine reduction, with no restatement hole. Imports are needed
for statements/data or proof APIs; all three added imports in the main module are
plain imports. No old import is removed. The No longer needed section now names
both removed direct proof edges while correctly claiming no pruned module.
The unit sk-thm-picard-semicon has empty realization lists; the upper-tail route is
retained and no realized step is bypassed. Verdict: pass.

5. Compared node statements, Lean records, proof steps and their dependency unions.
The original node records the actual reduction and the new node records the exact
comparison statement and all concrete definitions, with source, searches, creation,
blueprint, chapter and unit fields. No statement change record is needed.
Verdict: pass.

Second reading changed only this report: replaced the obsolete compile-blockage
paragraph with actual module-set verification, completed the removed direct
proof-edge inventory, and recorded this independent review. The Lean proof and
node records required no repair. Net holes closed minus added: zero (decomposition).
