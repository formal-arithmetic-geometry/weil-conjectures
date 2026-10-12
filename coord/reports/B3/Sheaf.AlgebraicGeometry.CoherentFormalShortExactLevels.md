## What changed

Proved `AlgebraicGeometry.coherentFormalModule_shortExact_levels` in
`Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels` without changing its signature.
Evaluation preserves the cokernel using the existing termwise cokernel interface.
The constructed kernel is compared with the first term using their universal properties.
The required later-level quotient map is explicitly a composite of image corestriction,
image comparison, quotient projection, quotient comparison, and kernel comparison.
Updated the theorem docstring and its DAG proof to follow this Lean argument.
Added the proof-only Mathlib import `Mathlib.CategoryTheory.Limits.Shapes.RegularMono`
for the regular-epi/strong-epi/balanced instance chain. All public imports stay unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherentFormalModule_shortExact_levels`
(node `lem-weil-pbc-coherent-formal-short-exact-levels`).
No holes added; no `sorry` remains in the delivered module.
This is a complete proof from existing named declarations, including the still-unproved
`AlgebraicGeometry.coherentFormalModule_abelian` and
`AlgebraicGeometry.coherentFormalModule_kernel`. Their holes are unchanged and are not
claimed as closed. No new module, axiom, definition, or statement was added.
The prescribed single-file compiler passed without warnings.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`

Removed direct proof dependencies `pqf-def-coherent` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`: categorical cokernel and image
instances suffice. The formal-module definitions are still needed and publicly available
through `CoherentFormalModulesAbelian`; that definition node remains a proof dependency.
Coherence and quasi-coherent cokernel/image modules remain reachable through the retained
construction modules, so this delivery does not claim they leave the target closure.
The abelian and kernel construction modules remain needed. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned separate quasi-coherent image calculation is unnecessary once the abelian
interface gives a cokernel cofork preserved by evaluation. The kernel interface already
supplies the image comparison needed at n+c, so its stabilization equality need not be
used again. The Lean index n represents positive level n+1; choosing index n+c+c matches
the existing kernel statement exactly, including c=0 and n=0.

Lean's native full-subcategory zero morphisms and the zero morphisms induced by the chosen
abelian preadditive structure are not definitionally equal. The proof installs the chosen
preadditive and zero-morphism structures only inside the proof of Balanced, whose statement
is independent of those structures. This resolves instance inference without changing any
public definition or statement.


## Second reading by B3

1. Interface: PASS. Compared the sole delivered Lean module with the repository using
   diff and a byte-for-byte extraction of the existing theorem signature. The signature
   and both public imports are unchanged. There are no new declarations, definitions,
   instances, file-level options, or change records. Changes are confined to the proof,
   its explanatory docstring, and private proof imports.
2. Proof: PASS. Independently compiled the delivered module with lcompile.py: no errors
   or warnings (4.6 seconds). A scratch copy with `#print axioms
   AlgebraicGeometry.coherentFormalModule_shortExact_levels` compiled and reported exactly
   propext, Classical.choice, Quot.sound, and sorryAx. The last is expected from the
   existing open abelian/kernel interfaces and their dependencies; no local sorry remains.
   Checked absence of forbidden declarations and foreign implementations. The proof
   constructs the requested epimorphism explicitly. Choices of limiting cokernel and
   kernel data are governed by their universal properties; no arbitrary witness is used
   to define public data.
3. Split statements: PASS, not applicable. No statements or holes were split off or added.
   Checked both imported theorem statements. At n = 0 the quotient exponent is 1; at
   c = 0 the selected later index equals n and the image and quotient comparisons still
   typecheck mathematically. No termwise monomorphism is inferred.
4. Route and pruning: PASS. Read Mathlib's ShortExact.fIsKernel/gIsCokernel and
   Exact.map_of_epi_of_preservesCokernel and searched the local Sheaf, upstream algebraic
   geometry, and Mathlib short-complex sources for a shorter existing result. The proof
   already uses the direct generic cokernel route; no existing formal-level replacement
   was found. The kernel comparison is exactly its universal-property comparison, and
   the five factors of q are epimorphisms. Retained proof imports supply the kernel
   interface and regular-epi instance chain. No longer needed lists all three removed
   direct imports and both old proof dependencies omitted by the new proof. Checked
   dag/units/sk-thm-p1.json: no removed dependency realizes a unit statement or step;
   its realized route is unchanged. The removed modules remain transitively reachable,
   as the report explicitly states.
5. DAG: PASS. The sole delivered node changes only proof, proof_deps and proof_origin.
   Its proof_deps are exactly the union of the proof steps' uses. The steps match the
   cokernel preservation, universal kernel comparison and explicit quotient construction
   in Lean. Statement, statement dependencies, source, Lean record, chapter and unit
   remain unchanged. The two categorical kernel/cokernel dependencies are realized by
   the Mathlib short-exact methods used in the proof.

Second reading changed only this report: added independent review evidence and the
axiom-check result. No proof or node repair was needed. Holes closed: one; holes added:
zero; whole modules removed from the target closure: none.
