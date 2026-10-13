## What changed
The unchanged target `AlgebraicGeometry.coherentMap_reduction_torsion` pairs separate kernel and cokernel bounds. An earlier reading proved the cokernel component by the canonical epimorphism from the original cokernel to the reduced cokernel, tensor multiplication naturality, and `formalModuleQuotient_factor`. Only the kernel component remains an affine reduction obligation. Every statement and definition of the original module is unchanged; no change record is required.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.coherentMap_reduction_torsion` by decomposition. Added and proved `AlgebraicGeometry.coherentMap_reduction_torsion_coker` (node `lem-weil-pbc-coherent-map-reduction-torsion-coker`); its axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Added one hole, `AlgebraicGeometry.coherentMap_reduction_torsion_kernel` (node `lem-weil-pbc-coherent-map-reduction-torsion-kernel`), with the complete affine scalar quasi-inverse proof in its docstring. One original hole closed, one new hole left: net zero for these declarations; this is a decomposition, not a complete proof of the target. No ledger-wide progress figure is claimed.

## No longer needed
Also removed the unused proof-only import `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` from the cokernel module in the current reading; compilation and its axiom check still pass.

Removed the proof-only import `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated` from the target and both new components, and the target baseline imports `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, and `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: its formal-system equivalence is not used. The target's old direct proof dependencies `lem-weil-pbc-formal-systems-annihilated-by-power`, `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, `lem-weil-pbc-quasi-coherent-module-cokernel-image`, and `pqf-lem-coherent-ft-locnoeth` are replaced by the two component nodes. The last three remain part of the kernel obligation's affine route. The formal-system annihilation node is replaced there by the underlying ring-level reduction node `lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal`. `def-weil-pbc-coherent-formal-module` remains a statement dependency and its public import stays. No other module's reachability was measured; no claim that all these modules are globally pruned.

## Where the brief, the DAG or earlier work was wrong
The first worker merely split the conjunction into two holes and described it as proved. That is a decomposition with negative net holes before this reading. Its new nodes copied unrelated searches and historical review approval from the old node; those records were removed and fresh searches recorded. The cokernel half has a shorter categorical proof requiring neither the kernel hypothesis nor coherence, although its new signature is preserved. The open kernel argument was checked against [Stacks Tag 0888](https://stacks.math.columbia.edu/tag/0888), the commutative algebra paragraph; its source file is not present on this machine.

## New nodes
`lem-weil-pbc-coherent-map-reduction-torsion-kernel` records only the kernel conclusion and its complete affine proof plan. `lem-weil-pbc-coherent-map-reduction-torsion-coker` records only the cokernel conclusion, now proved with standard axioms. Both are strictly smaller than the simultaneous bound and live in their own modules. There are no statement or definition change records.

## Earlier second reading (a previous round; superseded)
1. Compared the target module by diff against the repository: its existing signature is byte-for-byte unchanged. Only proof imports, the proof docstring, and the proof body changed. No existing data definition changes and no forced adaptations.
2. Compiled every delivered module locally in import order. The cokernel proof uses only the three permitted axioms; the remaining kernel hole is a named public theorem with a complete proof docstring and node. The target depends on this hole. No axiom, unsafe, opaque, implemented_by, extern, or hollow data definitions occur in the delivery.
3. Checked the two component statements against the affine argument and the quotient argument. Edge cases: K=0 makes the positive-power product zero; K=O_X forces the original map to be an isomorphism; I=0 recovers the original map; I=O_X makes both quotients zero; the empty scheme and zero modules cause no exception. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. Fresh LeanFinder, Loogle and grep searches found categorical primitives, used in the cokernel proof, but no exact existing sheaf bound. The kernel half still genuinely needs the kernel and cokernel hypotheses. The cokernel half keeps unused hypotheses to avoid unnecessary signature churn.
4. Closed the cokernel hole by the shorter quotient proof, removed unused annihilation imports, and recorded every old direct proof dependency above. Read `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized statement or step node, and the unit's realized route stays unchanged. This is below the unit level.
5. Updated proof steps, their dependency unions, and proof origins to agree with the final code and the open kernel plan. New nodes have their own statements, modules, provenance and actual searches; removed copied review approvals. No unrelated node or unit is changed.

Second reading changed: proved the cokernel component; expanded the kernel docstring; pruned unused imports; repaired DAG metadata and the report's accounting. The kernel remains a genuine smaller obligation.

## Second reading by M1

1. Compared the delivered target with the repository by `diff -u`: the complete existing
   theorem signature is byte-for-byte identical. Only its proof, proof docstring and
   private imports differ. The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. Both other modules and nodes are new. No definition, public import,
   target statement or forced adaptation changed. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`. Printed axioms
   from fresh scratch copies of the actual final files: the cokernel theorem uses
   exactly `propext`, `Classical.choice`, `Quot.sound`; the target and kernel add only
   `sorryAx`. The only delivered sorry is the public named kernel theorem, with source,
   full proof docstring and matching node. There are no forbidden declarations or data
   constructions and no line exceeds 100 characters. Verdict: pass as decomposition.
3. Read Stacks Tag 0888, `remark-inverse-systems-kernel-cokernel-annihilated-by`, the
   paragraph constructing the scalar quasi-inverse. The kernel uses cokernel annihilation
   to lift fy and kernel annihilation to make gx independent of the lift; its linearity
   preserves the reduction ideal. Products fg generate the double power. The cokernel
   projection factors through the original cokernel and is epic; tensoring preserves
   epimorphisms by the closed monoidal structure. These statements match the Lean
   hypotheses and ambient kernel/cokernel conventions. Checked K=0 (positive powers),
   K=O_X (the original map is an isomorphism), I=0 (the original map), I=O_X (zero
   quotients), zero modules and empty X. All satisfy the bounds. Fresh searches with
   different wording: LeanFinder found tensor kernel/Kaehler primitives, grep no exact
   bound, Loogle unavailable (not a no-match verdict). Local searches in both library
   roots and upstream found the existing ring theorem in
   `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal`, already cited by the kernel
   plan; no exact sheaf kernel bound. The kernel is a strict single-conclusion part,
   while the other conclusion is proved without sorry. Verdict: pass.
4. Read the actual `formalModuleQuotient_factor` proof and the cokernel's tensor/image
   proof. Removed the unused TensorProduct import and compiled the result. The remaining
   MonoidalClosed import supplies the closed structure used to infer tensor map epi;
   CoherentFormalModule is required publicly by signatures. The report lists all four
   old direct dependencies and explains which remain in the kernel plan. Read
   `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized unit statement or
   step, and all realized nodes remain unchanged. The ring argument is already proved,
   but transporting affine kernels, powers and quotients to the actual sheaf map is
   substantial work, so the remaining hole was not closed in a short review pass.
   Verdict: pass; no global pruning or positive net-hole progress claimed.
5. Read all three delivered JSON nodes and the four kernel-plan dependencies, including
   the coherent/quasi-coherent equivalence, affine ideal products, affine cokernel/image
   comparison and ring scalar quasi-inverse theorem. The target's dependency union is
   precisely its two applications. The cokernel node names the proved factorization
   used by its Lean proof. The kernel node describes the remaining affine argument;
   its `proof_deps` are a plan, not a claim that these lemmas are used by a completed
   Lean proof. New nodes have independent signatures, provenance, source, blueprint
   ancestor, chapter, unit and logged searches. Corrected their prose statements to
   TeX with explicit ambient conventions and appended this reader's actual searches.
   Verdict: pass.

Current second reading changed: pruned one unused proof import, clarified new-node
statements and added independent search evidence and this review. Kept the valid
cokernel proof and open kernel statement. Accounting remains one original hole closed
by decomposition and one kernel hole added (net zero); one additional cokernel theorem
is proved with standard axioms.
