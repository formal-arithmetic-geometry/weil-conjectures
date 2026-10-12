## What changed

Proved AlgebraicGeometry.Etale.finiteCoproductConstantBaseChangeSquare in
Sheaf.AlgebraicGeometry.FiniteCoproductConstantBaseChangeSquare without changing its
signature. Constructed the base-changed coprojections by pullback.lift and their
colimit using Mathlib scheme extensivity. Applied the existing finite coproduct
cohomology assembly, transported coordinates by explicit coefficient isomorphisms,
and verified the square using cohomologyPullbackFunctorial and cohomologyMap_map.
Two proved private helpers construct H of a sheaf isomorphism as an equivalence
and transport cohomologyMap through equality of scheme morphisms. Updated the
existing node's proof and proof_deps to this route.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.finiteCoproductConstantBaseChangeSquare
(node lem-sc-finite-coproduct-constant-base-change-square).
No sorry remains in the delivered module; no holes or new modules are added.
The proof uses AlgebraicGeometry.Etale.finiteCoproductCohomologyAssembly,
whose existing sorry remains in its own module and is not changed here.
This is a proof from existing stated dependencies, not a new decomposition.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs (already publicly available
  through the statement imports).

The node no longer directly needs lem-weil-pbc-scheme-coproduct-family:
Mathlib FinitaryPreExtensive.isUniversal_finiteCoproducts proves the required
base-changed colimit. No scheme-coproduct-family module was directly imported.
The node no longer directly needs
lem-weil-pbc-constant-pullback-composition-coherence or its module:
cohomologyPullbackFunctorial supplies the composition identity. That coherence
module remains a dependency of the functoriality theorem, so this does not claim
it is globally unreachable. Retained all statement imports and the assembly and
functoriality proof imports. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned clopen-cover proof was unnecessary: Mathlib already makes schemes
finitarily extensive. The explicit comparison of two constant-sheaf composition
isomorphisms was also unnecessary once the existing functoriality declaration
was used. No statement or definition was found wrong or changed.
The construction works for an empty finite family and all n,q, including n=0,
n=1 and q=0; neither field-extension comparison is assumed invertible.

## Second reading by G2

1. Compared the delivered module with the repository version. The theorem signature and all existing declaration interfaces are unchanged; only proof imports, private proof helpers, and the theorem proof differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`, plus the pre-existing `sorryAx` inherited through `finiteCoproductCohomologyAssembly`; the delivered theorem itself has no `sorry`.
3. Checked the proof construction and edge cases. The base-changed coproduct is obtained by `FinitaryPreExtensive.isUniversal_finiteCoproducts`; the coefficient comparison is an explicit sheaf isomorphism, and no arbitrary witness or hollow definition is introduced. The argument applies uniformly to empty finite families, n = 0, n = 1, and q = 0.
4. Checked pruning and imports. The removed `ConstantPullbackCompositionCoherence` and `UpperLowerStar.Defs` imports are unnecessary for this proof; the former remains transitively available to the functoriality theorem. The node proof and `proof_deps` match the Lean route, and the unit route remains realized through the finite coproduct assembly step.
5. Searched the repository for duplicate declarations and checked the node metadata. No duplicate theorem or new split-off statement was added; the node retains the original statement and records the shorter universal-finite-coproduct route.

Changed during second reading: restored the repository theorem docstring and existing interface text, leaving only the proof, private helpers, and proof-only import pruning from the delivery.
