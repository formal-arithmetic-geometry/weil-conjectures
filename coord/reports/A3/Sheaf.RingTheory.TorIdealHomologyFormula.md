## What changed

Replaced the proof of `ModuleCat.exists_tor_ideal_homology_formula` in
`Sheaf.RingTheory.TorIdealHomologyFormula` without changing its signature or docstring.
Added the proved private helper `cycleMap_of_exact`: in a diagram of exact module pairs,
lift a cycle, lift its differential through an injective map, and apply a map killing the
ideal differential. Comparing two lifts proves independence, additivity, and linearity.
Specialized this to tensoring the ideal inclusion and quotient in degrees zero and one.
Computed the finite-sum formula directly. Tensor induction, a representative of each
quotient scalar, and the empty sum show that the resulting map kills all boundaries.
Finally used `HomologicalComplex.homologyIsCokernel` to descend to first homology.
The added proof import is `Mathlib.RingTheory.Flat.Basic`; the public imports are unchanged.

## Proved and sorry left

Closed the one original hole: `ModuleCat.exists_tor_ideal_homology_formula`
(node `lem-weil-pbc-tor-ideal-homology-formula`). No holes added; no sorry remains in the
module. The private helper is proved, rather than a new assumed dependency.
All choices are made from proved surjectivity/exactness; the comparison argument proves
that the final value is independent of them. No data is chosen from an unproved theorem.

## No longer needed

No original imports, nodes, or modules are pruned. The original four Mathlib dependency
nodes still account for free-to-projective-to-flat inference, tensor injectivity, and
right exactness. No Sheaf proof dependency is required. The redundant explicit import of
`Mathlib.LinearAlgebra.TensorProduct.RightExactness` was removed from the working proof;
`Mathlib.RingTheory.Flat.Basic` publicly imports it.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The local source file `literature/stacks-project/algebra.tex`
is absent on this machine; read the Stacks web pages for Tags 00M5 and 00M6 instead.
Their exact sequence and ideal-kernel interpretation agree with the node's construction.
The original proof route is retained. The second reader updated the node proof text and
proof_origin to record the actual degree-zero flatness, boundary calculation, and completed proof. The proof only
uses freeness of the degree-zero resolution term; all original hypotheses are preserved.
The construction uses no properness/nonzero assumption on the ideal or module, so the
zero ideal, unit ideal, zero module, and empty finite expression are included.


## Second reading by A3

1. **Interface: pass.** Read the full diff against the repository. The existing theorem
   signature is byte-identical, as checked by direct string comparison; its docstring and
   all public imports are unchanged. Only a proved private helper, a proof-only import,
   and the theorem proof were added. No definition or target statement changed.
2. **Proof: pass.** Read the helper and the complete construction. Exactness supplies
   the chosen lifts; injectivity and the augmentation identity establish independence.
   Comparing lifts establishes linearity. Tensor induction and the empty-sum formula
   kill boundaries, so the homology cokernel descends the map with the required formula.
   Compiled the delivered module and a scratch copy printing axioms for both declarations.
   No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition appears.
3. **Split statements: pass (none).** No new hole or public statement is split off.
   The proved private helper is strictly a lift-independence construction. Checked zero
   modules, zero and unit ideals, and k = 0: there is no missing properness or nonzero
   assumption; the boundary proof itself uses the k = 0 case.
4. **Route and pruning: pass.** An independent leanfinder search for exact-row cycle
   lifts returned general exactness and cycle-lifting lemmas, not this formula.
   Repository searches found the downstream TorIdealConnectingFormula and other-factor
   TorKernelBoundary constructions, neither a shorter available proof of this item.
   The proof uses Mathlib tensor exactness directly and homologyIsCokernel for descent;
   a full snake diagram would add machinery. All four original dependency nodes are
   retained (including free-to-projective-to-flat instance inference). The only added
   import, Flat.Basic, is private and needed. No original module or node is pruned.
   Read sk-thm-p1.realized; this construction is below its unit steps and bypasses none.
5. **DAG: repaired, pass.** The four dependencies match the inference and tensor lemmas.
   Updated the existing node's proof and proof_origin: only P₀ needs flatness, quotient
   boundary coefficients are lifted and reduced using the empty sum, and the construction
   is now formalized. No new node or unit-record change is required. The cited Stacks
   Tags [00M5](https://stacks.math.columbia.edu/tag/00M5) and
   [00M6](https://stacks.math.columbia.edu/tag/00M6) give the ideal Tor exact sequence
   and kernel interpretation; the explicit cycle construction implements that map.

Second reading changed the DAG proof description and completion attribution, and added
this review section. No Lean proof repair was needed. Closed one original hole and added
zero holes; this is a proof, not a decomposition.
