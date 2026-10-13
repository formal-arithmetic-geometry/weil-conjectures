## What changed

Replaced `exists_square_zero_tensor_boundary_leibniz` by a construction of its witnesses
and a specialization of a two-section product identity. The target signature is unchanged.

Second reading removed the redundant direct quasi-coherent-kernel import.
Imports supplying constants in exposed definition bodies remain public.

Added `SquareZeroTensorBoundaryComparisons`: explicit tensor-pullback comparisons,
recursive tensor-power comparisons (including zero), the ideal-tensor kernel isomorphism,
and the coefficient-cohomology isomorphism. Proved
`square_zero_ideal_tensor_unit_isIso` using the affine ideal-product range theorem,
monicity of twisting the ideal inclusion, sheaf separation, and the existing
annihilated-module unit theorem. The comparison package is explicitly constructed;
the product theorem pins it by equality to that construction.

Added `SquareZeroTensorBoundaryProduct`, isolating the homogeneous two-section Leibniz
identity. It applies to an arbitrary degree-n section and an arbitrary degree-n(e+1)
section, with their three boundary classes specified by the comparison equations.
The main proof takes the second section to be a tensor power and uses the recursive
formula for `tensorPowSection`. Boundary classes are explicitly defined inverse images under additive equivalences,
so they are uniquely determined.

Checked the source online at https://stacks.math.columbia.edu/tag/09MS (the graded
sequence following coherent-equation-ses) and https://stacks.math.columbia.edu/tag/0B8S
(the two-section cocycle product calculation). The local literature tex files are absent.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_square_zero_tensor_boundary_leibniz`.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.transportedTensorBoundary_product`
(node `lem-sc-square-zero-tensor-boundary-product`). This is a decomposition, not an
independent sorry-free proof: one upper hole is closed and one strictly smaller product
identity is added. No sorry remains in the original module or in the comparison module.

The comparison module's `square_zero_ideal_tensor_unit_isIso` and
`boundaryIdealKernelIso_exists` are proved. All its data definitions are real constructions;
no arbitrary object is selected from an unproved existence theorem.

## No longer needed

No original public import was removed: all four serve the unchanged statement.

The new proof does not use the planned
`lem-weil-pbc-invertible-pullback-tensor` or
`lem-weil-pbc-module-pullback-tensor`, or their modules
`Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and
`Sheaf.AlgebraicGeometry.ModulePullbackTensor`. Instead it constructs the generic tensor
comparison from the proven monoidal Mathlib pullback and uniqueness of left adjoints.
The generic comparison also handles the ideal factor, which need not be invertible.
These two nodes are removed from the item's proof dependencies; they were not original
imports of the supplied module. Other nodes retaining them may still need them.

The original direct proof dependencies also cease to be direct dependencies of the item:
`lem-weil-pbc-closed-immersion-pushforward-annihilated`,
`def-sbc-closed-immersion-ideal-sheaf`, `def-sbc-ideal-sheaf-powers`,
`lem-sc-boundary-derivation-square-zero`, and `def-sc-module-cohomology-boundary`.
They remain dependencies of the comparison or product nodes, so they are not claimed
as globally pruned. No original module is pruned. In the new comparison module,
the direct `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` import
is redundant via `ClosedImmersion` and removed. ProjectionFormula remains necessary:
it declares tensor quasi-coherence and invertibility of tensor powers used in the public
cohomology comparison construction.

The square-zero boundary derivation node is still needed below the new product node.
The unit-quotient, annihilated-module, affine cohomology edge, ideal definitions, and
canonical section-boundary nodes remain needed. No claim is made that these become
unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had a stale Lean signature in the product node; this now matches
the actual statement. Destructuring its existential comparison wrapper triggered expensive
unfolding. The main proof now names the explicit package directly, and the unused wrapper
is removed. Explicit types for the product statement’s boundary and equivalence functions
prevent expensive inference.

The supplied dependency statements do not directly expose the graded summand/action
comparison with the canonical triangle boundary. This is the remaining product lemma,
with the exact section, kernel, and cohomology comparisons specified in Lean.
No existing statement or definition was changed and no forced adaptation is required.
The unit's realized statement and route are preserved.

Edge cases checked for the new product statement: e=0 is the ordinary two-section
identity with the right unitor; n=0 is the square-zero scalar boundary derivation;
I=0 gives zero coefficient cohomology; and empty schemes give zero groups. No positive
exponent, Noetherian, or nonempty hypothesis is introduced. No arbitrary choice of
comparison automorphisms is allowed: the package equals the explicit construction.

LeanSearch returned an Internal Server Error for both new searches. LeanFinder returned
ring cotangent/derivation and invertible-module results rather than the needed sheaf
statements. The logged Mathlib grep search returned only manifold boundary-product hits.
Repository searches found the existing derivation and affine ideal-product interfaces,
which are retained in the proof plans. Blueprint searches for square-zero ideal and
tensor boundary found no matching blueprint statement.

## New nodes

`lem-sc-square-zero-ideal-tensor-unit`, in
`dag/nodes/sec-curve-estimates/lem-sc-square-zero-ideal-tensor-unit.json`, records the
proved annihilated ideal-tensor unit statement and the explicitly constructed comparison
maps in `SquareZeroTensorBoundaryComparisons`. It adds no hole.

`lem-sc-square-zero-tensor-boundary-product`, in
`dag/nodes/sec-curve-estimates/lem-sc-square-zero-tensor-boundary-product.json`, records
the remaining arbitrary two-section product identity in `SquareZeroTensorBoundaryProduct`.
It is the derivation/transport portion of step 3 of the original plan and introduces one
hole. The main theorem's proof combines this identity with the independently constructed
comparison data and the actual boundary inverse images.

Change record: `coord/changes/square-zero-tensor-boundary-elaboration.md` records the
file-local elaboration settings conservatively classified as an interface change.
All declaration signatures and public imports are preserved; no users need adaptation.


## Second reading by P1

1. Compared the delivered item against the repository with `diff -u`; independently
   compared the full theorem signature as a byte string. Verdict: identical, including
   universe parameters, hypotheses, lets, conclusions and public imports. The other two
   modules are new. Only the reported file-local elaboration settings change outside the
   original proof; their change record describes them. No definition used by a target
   changes, and no forced adaptation is present.
2. Read all three modules. Verdict: the comparison objects are constructed, not hollow.
   The sole selected ideal-kernel isomorphism is uniquely determined by its inclusion
   equation, since the kernel inclusion is mono; its existence theorem is proved.
   The classes c_e are inverse images under additive equivalences, hence uniquely fixed.
   There is one literal sorry, exactly the named product theorem listed above; no forbidden
   axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass occurs. All files
   compile locally; explicit scratch #print axioms and the delivery probe check the axiom
   closure, allowing sorryAx from the reported open theorem and upstream holes.
3. Read the product theorem, docstring, node and its comparison definitions. Checked Stacks
   Tags 09MS and 0B8S directly: the graded exact sequence and local cocycle product rule
   support the statement without Noetherian or positive-degree hypotheses. In local frames
   the two terms are f times the boundary of x and x times the boundary of f; associativity
   and the right unitor match the displayed maps. At e=0 these are the ordinary two-section
   terms; n=0 is the scalar rule with unit comparisons; zero ideal and empty schemes give
   zero classes. The comparison equality hD prevents arbitrary automorphisms. Verdict:
   a true derivation/transport subproblem, not a renamed existential recurrence. The item
   separately constructs all comparisons and c_e and specializes x to a power. Repeated
   repository searches with connecting/product/annihilation terminology, LeanFinder for
   infinitesimal lifting of two sections, Loogle leftAdjointUniq, and Mathlib grep found
   no shortcut to this transport identity. Its remaining formalization is substantial,
   not a hole that can be closed in a few minutes.
4. Read the original proof plan and sk-thm-curveestimate realized record. Verdict: the
   item is below the unit level; the realized statement and every unit step stay intact.
   The proved affine image/annihilation and left-adjoint uniqueness interfaces give a real
   shorter route for comparisons. The old dependency pruning inventory is now complete,
   distinguishing removed direct edges from dependencies retained below the new nodes.
   Removed a redundant direct kernel import. Compilation established that ProjectionFormula
   is necessary for its tensor quasi-coherence theorem and tensor-power invertibility instance.
   Public imports used in exposed construction bodies are necessary under Lean's module
   visibility rules and remain public; proof-only imports remain plain imports.
5. Compared new node Lean signatures verbatim with the files and checked the original
   node diff. Verdict: the only original fields changed are proof, proof_deps and
   proof_origin; the statements are unchanged. Both new nodes have source, full proof
   steps, search records, matching declarations, creation data and inherited chapter/unit
   provenance. Proof dependencies are the union of steps' uses. The product node holds
   the one remaining hole; the comparison node records the proved unit theorem.

Second reading changed only one import and this report: removed the redundant direct
QuasicoherentKernel import and completed the direct-dependency pruning inventory. No statement, definition,
proof body, node signature or hole count changed. One original hole is closed and one
product hole is added: net zero, a decomposition, not a sorry-free proof of the item.
