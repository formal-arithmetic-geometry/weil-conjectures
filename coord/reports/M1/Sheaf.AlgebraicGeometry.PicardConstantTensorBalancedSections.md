## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections`
without changing its statement, universe, or visibility. Added the proof-only import
`Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections`.

The new module fully proves
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_scalar_extension_sections`:
it constructs pointwise extension of the constant module, its restriction maps, and
inverse natural Hom equivalences, then compares its representing object with the chosen
presheaf pullback. All construction data and private helpers are proved, with no holes.
The original module combines this comparison with Mathlib tensor cancellation, proves
the pure-tensor forward and inverse formulas, and proves the two required identities.
The DAG records this route. No existing signature or definition changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections`
(node `lem-sc-picard-constant-tensor-balanced-sections`).

Also completely proved the new helper:
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_scalar_extension_sections`
(node `lem-sc-picard-constant-scalar-extension-sections`).

No `sorry` remains in either delivered module; no holes were added or split off.
This is a proof, not a decomposition. Both modules compile without warnings.
`#print axioms` for each of these two public theorems reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; neither uses `sorryAx`.
The final single-file compiles and the separate axiom probe succeeded.

## No longer needed

No existing import or module was pruned. The public import
`Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor` is needed for its definitions.
Its theorem `exists_picard_constant_sections_tensor_basis` is not used in this proof:
no basis or coproduct argument is required. The original proof dependency on
`lem-sc-picard-constant-sections-tensor-basis` is replaced by the new proved comparison;
the definitions associated with the former node remain statement dependencies.
Neither `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction` nor
`Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule` is imported: direct Mathlib
adjunction and cancellation suffice. These were searched alternatives, not pruned imports.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan works unchanged. The chosen presheaf pullback is abstract,
so its sections cannot be reduced definitionally to tensor products. The representing-object
comparison specified in the original docstring is essential and is now fully proved.

The scalar-action and restriction calculations work for zero coefficients and the empty
open because no nonzero structure ring, affine, quasi-coherent, or finite-dimensional
hypothesis enters the construction. Restrictions are semilinear; the final pure-tensor
calculation explicitly uses `G.val.map_smul` rather than incorrectly treating them as
linear over a fixed structure-section ring.

The local literature checkout lacks `literature/stacks-project/sheaves.tex` and
`varieties.tex`; the cited [Tag 006R](https://stacks.math.columbia.edu/tag/006R) and
[Tag 0BED](https://stacks.math.columbia.edu/tag/0BED) were read online. The new argument
is the formal algebraic expansion of the original node's representing-object step.
`blueprint_refs.py ancestor` stops at the inherited null ancestor of the item;
the new node records its direct parent and exact proof step. Searches of the entire
blueprint for constant scalar extension and extension of scalars found no duplicate
constant-presheaf comparison. The unit's realized list is empty; no unit route was bypassed.

## New nodes

`lem-sc-picard-constant-scalar-extension-sections`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-constant-scalar-extension-sections.json`,
states the pre-tensor comparison independent of G. Its module and all helper proofs
are fully proved. It leaves no deferred item or new hole. No change record is needed:
all existing signatures, definitions, and public imports are unchanged.

## Second reading by M1

1. Compared both delivered modules with the repository versions. The existing theorem
   statement is byte-for-byte unchanged; the helper is a new declaration and its DAG
   node matches its Lean statement. The only interface change is the proof-only import.
2. Compiled both modules with `lcompile.py --all`; there are no errors or warnings and
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proofs
   use only the permitted classical axioms (the helper construction is noncomputable
   only through the representing-object choice).
3. Checked the helper statement on zero modules and empty opens: it is an ordinary
   pointwise scalar-extension comparison and introduces no extra hypotheses. It is
   strictly simpler than the target and is not a restatement of it. Searches found no
   existing declaration with the same statement.
4. The target proof follows the DAG route: first the scalar-extension comparison,
   then Mathlib tensor cancellation and tensor induction. The old basis dependency is
   removed from `proof_deps`; no unused delivered import remains.
5. The unit record's realized list is empty, so no realized unit step is bypassed.
   The DAG proof, dependencies, origin, and new helper node agree with the Lean code.

Changed during second reading: no mathematical or interface changes; this report
section records the checks above.
