## What changed

Proved `tensorBoundaryKernelMap_local_multiplication` in the delivered module. The proof expands the transported kernel map through its explicit pushforward isomorphisms, uses the ideal-kernel inclusion equations, and reduces the section calculation to two named intermediate tensor lemmas. Added `BoundaryPullbackTensorUnit` and `BoundaryCoefficientTensorProduct`; both are explicit public statements with `sorry` proofs for the remaining tensor-coherence calculations. The proof also contains a proved categorical ideal-pairing inclusion helper and a proved source-unit whiskering helper.

## Proved and sorry left

Closed the one original hole `tensorBoundaryKernelMap_local_multiplication` by decomposition. Added two lower holes, so this is a reduction, not a net sorry reduction. The private helpers `ideal_product_inclusion` and `whiskerLeft_section` are proved without holes. Remaining named holes are `boundaryPullbackTensorIso_unit_tmul` in `BoundaryPullbackTensorUnit.lean` and `boundaryCoefficientDegreeIso_tensor_product` in `BoundaryCoefficientTensorProduct.lean`; these are strictly lower tensor-coherence statements and have corresponding DAG nodes.

## No longer needed

Second reading removed the redundant direct public import of
`WeilConjectures.AlgebraicGeometry.Modules.TensorSection` from both new modules;
`SquareZeroTensorBoundaryComparisons` already exports it through `ProjectionFormula`.
No planned nodes or modules were pruned. Both original proof dependencies remain used. The proof uses `TensorBoundaryKernelMapNaturality`, `SquareZeroTensorBoundaryComparisons`, tensor-section lemmas, and the two new lower statements. No module or node outside this closure is required by the delivered proof.

## Where the brief, the DAG or earlier work was wrong

The imported plan omitted the concrete tensor-section coherence needed to compute the transported map. The target is still unchanged; the missing work is split into the two lower tensor statements above. Both new statements were checked at n=0 and e=0 where applicable, on empty opens, and for zero sections: the tensor unitors give precisely the degree-zero formulas, while linearity gives the zero formulas. No arbitrary witness is chosen: `boundaryIdealTensorProduct` is an explicit composite. Existing signatures and the existing module's public imports are unchanged. Profiling identified an expensive `erw` on a nested inclusion expression; a typed categorical equality removes the unfolding, and the final file compiles without increased heartbeat limits. The source reference for Tag 09MS is the coherent-equation-ses paragraph, while Tag 01CD supplies the pullback tensor comparison (the online Stacks page labels 01CD as Lemma 17.16.4 and 09MS as Lemma 30.17.5).

## New nodes

`lem-sc-boundary-pullback-tensor-unit` records normalization of the pullback tensor comparison on pure sections. `lem-sc-boundary-coefficient-tensor-product` records compatibility of the coefficient-degree comparison with the explicit ideal tensor pairing.


## Second reading by D4

1. PASS: compared the existing module with its repository version. The complete
   `tensorBoundaryKernelMap_local_multiplication` signature, including its lift
   hypothesis and conclusion, is byte for byte identical. Only its proof, two
   private proved helpers, and two plain proof imports were added. There are no
   changed existing definitions or statements and no forced adaptations.
2. PASS: compiled all three modules with `lcompile.py --all`. The only two
   sorries are the public named theorems reported above, each exactly `by sorry`.
   No prohibited declaration or option occurs. A scratch copy prints axioms for
   the main theorem, both helpers, the explicit pairing definition, and both
   split theorems. Helpers and pairing use only `propext`, `Classical.choice`,
   `Quot.sound`; the three remaining declarations also use `sorryAx`. The pairing
   is an explicit composite; no data is chosen from an arbitrary existence claim.
3. PASS: read both split statements against `boundaryPullbackComparison`,
   `boundaryPullbackTensorIso`, `boundaryPullbackPowIso`,
   `boundaryCoefficientDegreeIso`, `boundarySectionDegreeIso`, `tensorPowAddIso`,
   and `tensorPowMulIso`. Pullback normalization is the pure-tensor formula for
   scalar extension transported through uniqueness of left adjoints. Coefficient
   coherence is checked on a trivializing cover of L: q is h times the pulled-back
   generator, and s is r times its n-fold tensor with r in the pulled-back ideal.
   Both sides give hr in the coefficient block and the same remaining generator
   blocks. For n=0 this is scalar multiplication with unitors; e=0 joins two
   n-blocks. Empty opens, zero ideal, and zero sections give zero on both sides.
   These statements have complete proof docstrings and matching nodes. They omit
   the kernel transport and lift of the original theorem and are strictly smaller
   parts of its argument, not restatements. Repeated leanfinder, loogle and grep
   searches with different wording found pullback/unit and oplax naturality
   lemmas, but no exact statement closing either hole. Read the upstream
   `PullbackMonoidal` localization construction and `ProjectionFormula` section
   lemmas; a short application does not discharge these coherence statements.
4. PASS after import cleanup: the main proof constructs the ideal product, uses
   unit naturality and the two smaller formulas, cancels the explicit transported
   isomorphisms, and applies the ideal inclusion equations. Both old proof_deps
   are used; none is missing from No longer needed. The two new modules needed
   only their comparison-module public import, so the redundant direct public
   TensorSection imports were removed. The unit record `sk-thm-curveestimate`
   realizes `thm-sc-proper-cohomology` and has no realized steps; this lower
   reduction preserves that route.
5. PASS: the existing node changes only `proof`, `proof_deps`, `proof_origin`.
   Its steps follow the Lean proof and its dependencies include both old nodes
   and the two new nodes. The new node statements agree with the Lean signatures;
   their source, proof steps, dependency unions, provenance, searches, creation,
   blueprint, chapter, unit and Lean records are present. Added the second-reader
   search evidence to both new nodes.

Changed in second reading: removed two redundant direct imports, clarified the
import-pruning report, added independent search evidence and this review. No Lean
proof or statement needed repair. This remains a decomposition: one original hole
closed, two lower holes added, net minus one hole closed; no module pruned.
