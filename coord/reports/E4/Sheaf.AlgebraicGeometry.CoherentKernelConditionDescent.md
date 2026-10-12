## What changed
Added `Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing`, whose named theorem constructs finite local-generators data for the global kernel from the local cover kernel conditions. The target theorem now applies this gluing statement and unpacks the defining `IsFiniteType` structure. The existing target module's proof dependency and node copy were updated accordingly.

## Proved and sorry left
Proved `AlgebraicGeometry.coherent_kernel_condition_descent` from the lower-level gluing theorem. One sorry remains in `AlgebraicGeometry.coherent_kernel_condition_local_generators`, recorded by node `lem-weil-pbc-coherent-kernel-condition-descent-local-generators`.

## No longer needed
The original target proof dependencies `def-pc-scheme`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and `pqf-def-coherent` are no
longer used directly by the target proof; they remain transitively available through the
gluing theorem's statement. No existing import was removed; the target adds the proof-only
import `Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing`.

## Where the brief, the DAG or earlier work was wrong
The stated DAG proof requires substantial restriction and local-generator gluing machinery absent from Mathlib. That argument was isolated as one strict lower-level theorem so the target proof is a real structural reduction rather than an in-proof sorry.

## New nodes
`lem-weil-pbc-coherent-kernel-condition-descent-local-generators` records the local-generator construction and its Stacks source.

## Earlier second reading (a previous round; superseded)
A second reader should compile the two delivered modules and check that the target signature is unchanged, that the new local-generators statement is a strict lower-level construction, and that the unit route through restriction and local finite generation is preserved.

## Second reading by E4
1. I compared both delivered modules with the repository versions. The target theorem's
   signature is byte-for-byte unchanged; the only target change is its proof and the proof-only
   import. The added theorem is a separate existential local-generators statement.
2. I compiled `CoherentKernelConditionGluing.lean` and then the target with
   `python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`; both compile cleanly. The only
   remaining `sorry` is the named theorem
   `AlgebraicGeometry.coherent_kernel_condition_local_generators`, and it has its node and
   source proof docstring. No definitions contain `sorry`, and no forbidden declarations were
   added. The target proof introduces no extra axioms beyond those permitted by the project.
3. The split-off statement is true and strictly simpler than the target: it constructs the
   `LocalGeneratorsData` witness whose finite-type predicate is exactly the defining data used
   by `IsFiniteType`. It does not restate the target theorem, and it has no existing Mathlib or
   library duplicate found by the recorded searches.
4. The proof follows the unit route: the gluing node explicitly performs restriction to cover
   intersections, sectionwise kernel computation, and local-generator assembly. The target
   merely applies that lower-level construction and unpacks `IsFiniteType`.
5. The DAG target proof, proof dependencies, and new node agree with the Lean declarations.
   The old direct dependencies are recorded above as no longer needed by the target proof.

I changed only the report during this second reading; no Lean proof or statement required repair.
