## What changed

Replaced the invalid full-conclusion core restatement with the scalar-compatibility theorem
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counit_smul`, in the new module
`Sheaf.AlgebraicGeometry.AffineModuleTensorCounitSmul`. It asserts only the sectionwise
scalar identity for the already specified counit composite. Its docstring gives the
balanced evaluation and local-generation proof.

The existing module `Sheaf.AlgebraicGeometry.AffineModuleTensorCounitLinear` now composes
κ and the canonical counit as actual O_U-linear maps, forgets scalars to obtain an additive
natural transformation, and constructs its B-linear lift with Mathlib's
`PresheafOfModules.homMk`. The new scalar identity supplies the sole linearity condition;
the requested section formula is reflexive. The new import is proof-only (`import`).
Both existing public imports are required by the existing signature and are retained.
No existing signature, definition, notation, visibility, or docstring changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counitLinear`
(node `lem-weil-pbc-affine-module-tensor-counit-linear`).

Hole added: `AlgebraicGeometry.Scheme.Modules.affine_module_tensor_counit_smul`
(node `lem-weil-pbc-affine-module-tensor-counit-smul`). This named theorem has exactly
`:= by sorry`; there are no other new holes and none in the original item module.

This is a decomposition: one upper hole closed and one narrower scalar-compatibility
hole added, net zero holes closed. The full counit-linearity assertion is not yet
proved without sorryAx. Additivity, naturality, and construction of the actual module
morphism are checked Lean terms, rather than further postponed claims.

Both modules compiled locally through lcompile.py in import order. A scratch copy with
`#print axioms` for both declarations showed only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The scratch copy was removed before delivery.

## No longer needed

No imports removed and no modules pruned from the targets' import closure.
The original node's direct proof dependencies
`def-pur-sheaf-tensor-product`, `def-weil-presheaf-modules-sheafification`, and
`lem-pc-module-inverse-image-adjunction` are no longer direct dependencies of its
Lean proof. They remain dependencies of the new scalar-compatibility node's proof
plan, so this moves work below the constructor and does not claim closure pruning.
`lem-pc-module-pullback-adjunction` remains a direct dependency.
The unlanded `lem-weil-pbc-affine-module-tensor-counit-linear-core` node and its theorem
were deleted; they were a duplicate of the entire item with a vacuous premise.

## Where the brief, the DAG or earlier work was wrong

The first worker's extra premise `(0 : sections) = 0` does not make an exact restatement
of the original conclusion a strict subproblem. Its report's claim that this was a
strict decomposition was incorrect. The second reader removed both that theorem
and its new node. No artifact of that interface is delivered.

The existing theorem is still true in the edge cases examined: zero section and
zero scalar give zero on both sides; on an empty open or with zero rings the same
balanced evaluation is defined. For the identity scheme map and identity algebra
maps the scalar identity reduces to ordinary linearity. The construction of a module
morphism from an additive natural transformation and this identity is Mathlib's
existing homMk, now used directly rather than split off.

The source's construction was checked against [Stacks Tag 01SB](https://stacks.math.columbia.edu/tag/01SB).
The expanded proof of the new scalar identity uses the sheafified balanced evaluation
and equality on locally generating unit sections; it requires no new affineness or
quasi-coherence assumption. `b ≫ ε = 1` makes the evaluation O_U-linear, and
`t ≫ ε = e₀` makes it balanced over IA.

## New nodes

`lem-weil-pbc-affine-module-tensor-counit-smul` records the scalar-compatibility part
in its own module. Its statement and Lean record match the new theorem verbatim,
with the original chapter and unit, source, proof steps, dependencies, provenance,
four fresh search records, and creation record. No change records are needed:
no existing statement or definition changed. The original node's proof, proof_deps,
and proof_origin now describe the explicit constructor reduction.

## Second reading by F3

1. Interface comparison: passed after repair. `diff` and the declaration parser show
   the existing signature is byte-for-byte unchanged, with no altered definitions or
   visibility. The only edits to the existing module are its proof and a plain import.
2. Proof and axioms: both modules compile in import order; the target constructs a
   real morphism using an additive natural transformation and homMk. The only explicit
   sorry is the named scalar theorem in the new module. No axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition was introduced. Explicit axiom prints
   show only the permitted axioms and sorryAx; this is a decomposition, not completion.
3. Split statement: rejected the original core and its vacuous hzero premise. The new
   theorem contains only the scalar condition, not a module-morphism existence claim.
   Its source and full natural-language proof are in its docstring and matching node.
   Checked zero section, zero scalar, empty open, zero ring, and the identity-map case.
   Fresh leanfinder, loogle, and grep searches (LeanSearch returned Internal Server Error),
   plus direct searches of lean/ and the
   upstream source, found homMk (used) but no duplicate scalar-compatibility theorem.
   restrictHomEquivOfIsLocallySurjective cannot be applied: b is not assumed locally
   surjective. The remaining balanced-evaluation/local-generation argument could not
   be closed by a short existing theorem application.
4. Downward route and pruning: the outer proof uses the shortest found constructor
   route. All imports serve signatures or the proof. The list above accounts for
   every old direct proof dependency no longer directly used. None is claimed pruned
   from the closure. The item is below the unit level; dag/units/sk-thm-p1.json realized
   does not name this node, and no recorded unit statement or step is bypassed.
5. DAG consistency: the original node now follows the actual Lean reduction; its
   proof dependencies are the canonical adjunction and the new scalar theorem. The
   new node includes all required fields and has a verbatim Lean statement. Its proof
   plan includes the inverse-image and change-of-rings adjunctions and sheafification.

Second reading changed: deleted the invalid restatement and vacuous premise; added
one scalar-only theorem with its source, docstring, searches and node; constructed the
module morphism in the existing target; corrected the original DAG proof and report.
