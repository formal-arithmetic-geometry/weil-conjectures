## What changed

The item is reduced to natural unit-module section coordinates and naturality of the
coefficient-universe comparison. Its statement and public imports are unchanged.
The proof constructs the sheaf isomorphism from the supplied section coordinates,
checks its scalar square sectionwise, and composes natural cohomology comparisons.
The new ModuleCohomologySourceComparison module states the natural bridge to the
source library's ordinary H: free abelian Yoneda at the terminal open is the constant
integer presheaf, and Ext precomposition transports the module/abelian comparison.
The natural comparisons are composed in EtaleQcoherentSourceComparisonNatural.
All new data used in the proof are concrete isomorphisms or locally eliminated
existential witnesses; no definition chooses an arbitrary witness from a sorry.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.exists_addEquiv_etaleCohomology_one_structureSheaf
(lem-sc-additive-cohomology-scalar-comparison) by decomposition.
Proved AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsSheaf_source_comparison_natural
(lem-sc-etale-qcoherent-source-comparison-natural).
Three holes added, all in new modules:
- AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_source_comparison
  (lem-sc-module-cohomology-source-comparison).
- AlgebraicGeometry.Scheme.Modules.exists_etaleTensorUnit_sections_natural
  (lem-sc-etale-tensor-unit-sections-natural).
- AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsSheaf_cohomology_ulift_natural
  (lem-sc-etale-qcoherent-ulift-cohomology-natural).
There are no remaining sorries in the item's module. This is a decomposition,
not a sorry-free proof of the geometric comparison. It closes one upper hole and
adds three strictly lower holes; the net hole count of this delivery is minus two.
Existing sorry-bearing dependencies, including etale_zariski_qcoh_comparison,
remain dependencies and are not newly added holes of this delivery.

## No longer needed

Removed these direct proof imports from the item:
- Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
- Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
- Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
- Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
- WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
- Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
- Sheaf.AlgebraicGeometry.TensorPullback
- Sheaf.Paper.PQFCohomology

The etale/Zariski, module/abelian, tensor-section, affine acyclicity and Cech
modules remain below the intermediate statements or their imports. This delivery
does not claim that those modules are globally pruned. PQFCohomology's
sheafCohomologyAndHigherDirectImages is not used: the argument only needs the
already defined moduleCohomology functor and the source definitions of H and smul.
The former direct proof-dependency nodes are replaced in the item's node by the
new section-coordinate, coefficient-naturality and composite-comparison nodes;
the natural Ext/derived comparison stays a direct dependency. No unit statement
or unit step is bypassed (sk-prop-cd.realized is empty).

## Where the brief, the DAG or earlier work was wrong

The existing coefficient-lift result asserts only Nonempty of an additive
equivalence. It cannot be used to deduce naturality in scalar endomorphisms;
the new coefficient-naturality statement specifies one equivalence working for
all endomorphisms on a fixed finite cover. The ordinary-H bridge was also implicit
in the plan: zariskiModuleAbelianCohomologyAgree ends in H-prime at the terminal
open, whereas source Scheme.Modules.H uses Ext from the constant integer sheaf.
The bridge is stated separately with its explicit free-Yoneda proof plan. The earlier
attempt at its explicit proof exceeded the 60-second compile limit in the dry run;
its lower statement is now a named sorry rather than an unverified proof.
The raw tensor-pullback construction is expensive to unfold; the section lemma
therefore accepts the associated morphism and its component formula, so the
consumer uses the established component equality without reducing tensor sheafification.
No existing signature, definition or visibility is changed.
The earlier main proof also timed out while matching the tensor sheaf behind a
local module abbreviation. Supplying the syntactically identical unit tensor
sheaf to the section-coordinate helper avoids unfolding tensor sheafification;
the full target proof then compiles in about fourteen seconds. A chained
`.hom.app` syntax error in that helper was corrected.
Edge cases of the new statements were checked mathematically: empty schemes and
zero modules give zero groups/complexes; r=0 and r=1 give zero and identity maps;
q=0 is ordinary sections. No smoothness, properness or field characteristic is used
in the new statements. The coefficient comparison requires compactness and
separatedness exactly where the finite affine cover argument uses them.
LeanFinder returned cotangent-cohomology results, not a sheaf comparison;
Loogle found Ext and FreeAbelianGroup.uniqueEquiv; Mathlib grep found no
coefficient-lift cohomology naturality. LeanSearch was unavailable (HTTP internal
server error), as recorded by the search tool.

## New nodes

lem-sc-etale-tensor-unit-sections-natural: section coordinates and global-function
multiplication for the tensor pullback of the unit; no cohomology conclusion.

lem-sc-etale-qcoherent-ulift-cohomology-natural: natural coefficient comparison
for a quasi-coherent associated sheaf, with no field, curve, scalar action or
ordinary-H comparison in its conclusion.

lem-sc-module-cohomology-source-comparison: natural identification of
module right-derived sections with source ordinary H, for all modules and degrees.

lem-sc-etale-qcoherent-source-comparison-natural: proved composition of the three
natural cohomology comparisons for one quasi-coherent module and every module
endomorphism. It does not identify arbitrary sectionwise presentations of the
additive sheaf or express scalar compatibility.

No change records or forced adaptations are needed.

## Second reading by S3

1. Compared the delivered item module with the repository version. The target
   declaration and all existing declaration signatures are unchanged byte for
   byte; only proofs, proof-only imports, and the documented new modules differ.
   Verdict: pass.
2. Compiled all five delivered modules with the launcher. The item has no
   remaining `sorry`; the three explicitly split lower theorems are the only
   sorries, and no forbidden declarations occur. Verdict: pass.
3. Checked each split statement and its edge cases, source/docstring, and DAG
   node. They are strictly lower than the item and carry the required naturality
   hypotheses and proof plans. Verdict: pass.
4. Checked the proof route and imports. The proof uses the stated comparison
   modules, removes unused direct imports, and keeps the unit route; no shorter
   available declaration was found. Verdict: pass.
5. Checked the DAG proof steps, dependencies, origins, and realized-unit data
   against the Lean proof. They agree, and the report records the replaced
   dependencies and the three split nodes. Verdict: pass.

Changed only this report by adding this second-reading record; no Lean or DAG
repair was required.
