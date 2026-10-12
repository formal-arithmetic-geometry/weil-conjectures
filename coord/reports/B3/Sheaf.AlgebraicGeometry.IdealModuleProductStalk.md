## What changed

Filled `AlgebraicGeometry.Scheme.ideal_module_product_stalk` without changing any existing
signature or definition. Added proved private helpers `unit_stalk_iso`, `stalk_mono`, and
`stalk_quotient`. The main proof identifies product ranges, constructs quotient equivalences
with their specified representative formula, and proves all positive-power claims by induction.
Added a proof import of `Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange`, whose
single theorem isolates the tensor-multiplication range calculation (parent steps 2 and 3).
The unit identification uses the colimit comparison of forgetful functors, not an arbitrary
witness from an unproved existence theorem. Updated the parent DAG proof to the Lean reduction.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.ideal_module_product_stalk`
(node `lem-weil-pbc-ideal-module-product-stalk`). Added exactly one hole:
`AlgebraicGeometry.Scheme.ideal_multiplication_stalk_range`
(node `lem-weil-pbc-ideal-multiplication-stalk-range`). This is a decomposition, net zero
holes, rather than a complete axiom-free proof: the new result covers only the multiplication
range, while the unit identification, injectivity, quotient construction and power induction
are complete Lean proofs. There is no `sorry` in the assigned module or a definition.
The existing dependency `RingedSpace.module_stalk_exact` is used as stated, independently
of whether its published version still rests on further holes.

## No longer needed

Removed the assigned module's direct imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor` and
`Sheaf.Topology.PresheafModuleStalkFunctor`. StalkTensor is retained in the new multiplication
module and its node's proof plan; its existing unit/tool route is preserved, not pruned.
The presheaf stalk functor is not used by this proof: it uses the existing ringed-space module
stalk functor and Mathlib's underlying abelian stalk instead. No assertion is made that its
module disappears from the entire targets' import closure.
Removed the direct parent proof dependency on `def-weil-presheaf-modules-sheafification`;
it remains needed below the new multiplication lemma. The tensor and module-sheaf definitions
remain statement dependencies, and `lem-weil-pbc-module-stalk-tensor` remains needed below
that new lemma. The ringed-space functor is recorded by `def-pc-module-stalk-functor`, now included
in the proof dependencies. No further node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox's assigned file was empty, and its multiplication lemma had no node or
report. Its scratchpad helpers compiled; they have been incorporated and checked. The DAG's
mathematical route is sound. The multiplication step still requires relating the localized
monoidal left unitor to the sectionwise tensor multiplication. This has been explicitly
included in the new node's proof, rather than hidden as an elementary identification.
The positive-power induction does not need a mono hypothesis for each power, because the
range lemma holds for any map to the unit. Checked the zero map, zero ideal, unit ideal,
zero module, and exponent one: the split lemma and recurrence have the expected values.
Read the source's 01AG and 01CB text from the available local Stacks copy; 01CB's proof is
omitted there. The assigned node is not itself a unit realization in `sk-thm-p1`; no unit
step is bypassed. LeanFinder, Loogle and Mathlib/source searches found no shorter whole
statement; LeanSearch returned a service error, recorded as unavailable.

## New nodes

`lem-weil-pbc-ideal-multiplication-stalk-range` is the strictly smaller range calculation
used uniformly for F, J^n, and the products J^n F. Its new module is
`Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange`. It imposes no injectivity,
flatness, coherence or finiteness assumption, and its germ-compatible unit identification
is the same one used by the unchanged parent theorem. No interface change or forced
adaptation, and no change record, is required.

## Second reading by B3

1. Compared both delivered modules with the repository versions. Existing definitions and
theorem signatures in `IdealModuleProductStalk` are unchanged byte for byte; the only new
interface is the separately recorded split theorem and its node.
2. Compiled both modules with `lcompile.py --all`. The parent theorem has no `sorry`; the
single remaining `sorry` is the named `ideal_multiplication_stalk_range` split, with its
docstring and matching DAG node. No forbidden declarations or hollow definitions occur.
3. Checked the split statement on the zero map, unit map, zero module, and arbitrary maps:
it asserts exactly the multiplication image range and adds no injectivity or finiteness
hypothesis. Searches and repository grep found no existing theorem with this statement.
4. Read the proof reduction and imports. The parent proof uses the unit comparison, stalk
exactness, quotient equivalence, range lemma, and positive-power induction; the removed
presheaf-stalk-functor and direct stalk-tensor imports are unused. The unit route and the
unit's realized steps remain represented through the range node and its dependencies.
5. DAG `proof`, `proof_deps`, and `proof_origin` match the Lean proof, and the new node
contains the required statement, source, proof steps, searches, and Lean record.

Changed only the proof-bearing parent module, added the range split module and node, and
recorded the pruned imports and remaining hole above. No statement or definition change was
needed.
