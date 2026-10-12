## What changed

Replaced the sorry in `AlgebraicGeometry.finite_free_kernel_h1_zero` with a compiling
cohomological induction. Its signature and public imports are unchanged. The proof takes
a finite chain with quasi-coherent ideal quotients, proves that H¹ sends its zero initial
object to zero, applies the full long exact sequence at every step, and transports the
result across the endpoint isomorphism to `kernel p`.

Added `Sheaf.Paper.FiniteFreeKernelIdealFiltration`, with the geometric conclusion of
steps 1–2 as one public named theorem. It has no H¹ hypothesis or cohomological conclusion.
Its docstring and new node give the coordinate-kernel construction and explain the
identification of the image with `IdealSheafData.toModules`. Updated the parent node's
proof dependencies to match the actual induction.

Both modules compile together through `lcompile.py --all`. The structural statement was
checked on an empty index type (zero chain), a one-coordinate map (its kernel is an ideal),
the zero map (the chain has structure-sheaf quotients), and an empty scheme (all objects
zero). No epimorphism, affineness, quasi-compactness, or nonempty-index hypothesis is used.
The unit record has no realized nodes for this argument, and its route is unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.finite_free_kernel_h1_zero`
(node `lem-pqf-finite-free-kernel-h1-vanishing`). No sorry remains in the assigned module.

Added one hole, the entire proof of
`AlgebraicGeometry.finite_free_kernel_ideal_filtration`
(node `lem-pqf-finite-free-kernel-ideal-filtration`), in the new module.

This is a decomposition: one original hole closed, one geometric hole added, net zero.
The cohomological induction is proved, but the filtration's geometric construction is
still to be formalized. No data definition or private declaration contains sorry.

## No longer needed

Removed the direct proof imports
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` and
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` from the assigned module.
They are retained as planned proof imports of the geometric filtration module: their
nodes remain needed there. This is relocation, not pruning of their modules or nodes.

The old direct proof-dependency nodes
`lem-weil-pbc-quasi-coherent-module-kernel` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image` are no longer used directly by
`finite_free_kernel_h1_zero`; both remain dependencies of the geometric filtration.

No modules or nodes are claimed globally unnecessary. The full long exact sequence is
still used in the assigned module. The statement imports all remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing kernel and image closure declarations alone do not construct a finite
coordinate chain or an ideal-data comparison for an arbitrary quasi-coherent subsheaf
of the structure sheaf. The new lemma records precisely this remaining geometric work.
The available source-library ideal-module comparison in `Modules.ZeroLocus` requires
invertibility/Cartier hypotheses and cannot be applied here.

The local literature checkout does not contain `coherent.tex`; the recorded source was
read at https://stacks.math.columbia.edu/tag/01XF. LeanSearch returned an internal server
error; its search record says unavailable, not absence. No mathematical statement was
found false and no existing signature or definition was changed.

## New nodes

`lem-pqf-finite-free-kernel-ideal-filtration`, at
`dag/nodes/sec-abelian-varieties/lem-pqf-finite-free-kernel-ideal-filtration.json`, states
only the geometric chain with ideal quotients. It isolates the coordinate-filtration
paragraph of Stacks Tag 01XF from the subsequent H¹ induction. The new module is
`lean/Sheaf/Paper/FiniteFreeKernelIdealFiltration.lean`. Its statement introduces all
objects independently and contains no cohomology hypothesis. No change record is needed:
all existing signatures, definitions, and public imports stay identical.


## Second reading by M2

1. Compared the assigned module and existing node against the repository using diff.
   The existing declaration signature is byte for byte unchanged, as are its docstring,
   visibility, universe and three public imports. Only its proof and proof-only imports
   changed. The existing node changes only proof, proof_deps and proof_origin. The new
   module and node add one geometric statement; no definition or existing statement is
   changed and no change record is required. Verdict: pass.
2. Compiled both modules in import order with lcompile.py --all, without errors or
   warnings. Separate scratch copies with #print axioms show exactly propext,
   Classical.choice, Quot.sound and sorryAx for both declarations. The only literal
   sorry delivered is the named public filtration theorem, exactly := by sorry.
   No axiom, unsafe, opaque, extern, implemented_by, hidden hole or data definition is
   added. The existential chain is eliminated only inside a proof of a proposition;
   no data object is defined by choosing an arbitrary witness. Verdict: pass as a
   decomposition, not an axiom-free proof of the original result.
3. Read the geometric docstring, the IdealSheafData module bridge, quasi-coherent
   kernel/image declarations, and the coordinate paragraph of
   https://stacks.math.columbia.edu/tag/01XF. The chain consists of kernels of the
   coordinate restrictions; the next-coordinate projection has the preceding kernel
   and a quasi-coherent ideal image. On affine opens localization gives the required
   ideal-data compatibility; equal ranges of the monic inclusions give the module
   comparison and transport the short exact sequence. This does not use Epi p or
   quasi-compactness. Checked zero coordinates (zero kernel, n=0), one coordinate
   (kernel is itself an ideal), zero p (structure-sheaf quotients), and empty X.
   Fresh searches used leanfinder for a quasi-coherent subsheaf/ideal-data comparison,
   loogle for free sheaves and short complexes (identifier unavailable), msearch grep
   for ideal-data/quasi-coherence and free-filtration closure, plus rg on local modules
   and Mathlib. No existing geometric filtration/comparison theorem was found;
   unrelated coherent integral-support filtrations require different hypotheses.
   The new lemma has no H¹ hypothesis or conclusion and is strictly the geometric
   part of the original argument, not a renamed restatement. Its complete proof in
   words and matching node are present. Closing it would require substantial new
   categorical and affine-basis construction, beyond a few-minute repair. Verdict: pass.
4. Read the induction downward: additive H¹ maps the initial zero object to zero;
   the exact middle segment of the existing full long exact sequence and the ideal
   hypothesis give each successor; the mapped endpoint isomorphism gives the stated
   kernel. No simpler library result was found. Statement imports are public and
   proof imports are plain. The new module retains kernel/image imports as the
   declared plan for its open proof. The two old dependency nodes are explicitly
   listed above as relocated, not globally pruned. Read
   dag/units/sk-prop-av-pqf-finite.json: realized.statement and its only step are empty,
   and no realized route is removed or changed. Verdict: pass.
5. Checked the existing proof steps, proof_deps and proof_origin against the Lean
   induction. Checked the new node's source, searches, creation/blueprint records,
   chapter/unit, geometric proof steps and dependency union. Both lean.statement
   records match their actual Lean signatures verbatim. Verdict: pass.

Second reading changed only this report: explicitly named the old direct dependency
nodes that were relocated and recorded the independent checks. Lean proofs and node
files needed no repair. One original hole is closed and one geometric hole is added;
net zero, with no globally pruned module or node.
