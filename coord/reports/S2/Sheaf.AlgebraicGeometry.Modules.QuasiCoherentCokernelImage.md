## What changed

Proved `AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image` with its complete
original signature. The item now imports the proved source-library
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and Mathlib's
linear first isomorphism theorem. Public imports are unchanged.

The private, fully proved helper `surjective_affine_of_epi` applies affine Cech acyclicity
to the exact kernel sequence. Its use for the image factor and cokernel projection gives
all affine formulas. Local surjectivity of the image factor and sheaf uniqueness give the
local-image equivalence. The quotient equivalence is constructed from the surjective
linear projection, rather than selected from an unproved existence theorem.
The node's proof, proof dependencies and origin now describe this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image`
(node `lem-weil-pbc-quasi-coherent-module-cokernel-image`): 1 of 1 original holes.
Added holes: none. Sorries left in delivered modules: none.
The private helper is also proved. This is a proof, not a decomposition.
Local compilation succeeds without warnings. The delivery dry run checks the axioms.

The proof handles empty opens through sheaf uniqueness on an empty covering. No
Noetherian, finiteness, separatedness, or nonemptiness assumption was added.
The unit `sk-thm-p1`'s realized statements and steps are untouched.

## No longer needed

Removed proof import `Sheaf.Topology.SheafCokernelLocalImage`, and direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` (the latter is supplied
transitively by QuasicoherentCokernel and its kernel theorem is still used).

Removed direct proof dependencies:
`lem-weil-pbc-sheaf-cokernel-local-image`, `def-weil-pbc-sheafification`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-spec-module-tilde-sections`,
`def-pc-scheme`, `def-weil-sheaf-of-modules-category`, and `pqf-def-coherent`.
The affine tilde/restriction lemmas remain used internally by the existing proved cokernel
closure theorem; the scheme and module definitions remain in the statement's imports.
They are not claimed globally unused. The sheafified-cokernel local-image theorem is
entirely bypassed by the proved categorical local-surjectivity criterion.
Added direct dependencies are existing nodes for cokernel closure, the exact forgetful
functor, and affine Cech exactness. No unit statement or unit proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. Its planned proof overlooked the already proved
source-library cokernel closure and affine Cech lifting lemmas. The general
sheafified-cokernel criterion is unnecessary for this categorical formulation. The
original docstring records the original plan; the updated node and the proof body record
the actual shorter route. No new nodes or interface changes were needed.

## Second reading by S2

1. **Interfaces: PASS.** Read the entire module and compared it with the repository
   by `diff`. Independently checked that the existing theorem's signature is byte-for-byte
   identical, including its universes, both quasi-coherence instances, every open and
   affine-open quantifier, and the formula for the quotient equivalence on representatives.
   Public imports and existing docstrings are unchanged. No definition or statement changed;
   no change record is required.
2. **Proof and axioms: PASS.** The single delivered file compiles without warnings in
   8 seconds through `lcompile.py`. No `sorry`, prohibited declaration or hollow definition
   occurs. A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`
   and `Quot.sound` for `AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image`.
   Read `isQuasicoherent_cokernel`, `range_map_kernelι`, the exact forgetful-functor
   instances, and both affine Cech lemmas: their hypotheses match the applications.
   The helper maps the short exact kernel sequence to abelian sheaves, with quasi-coherent
   kernel. Forward local-image membership uses the epi image factor and naturality;
   reverse membership uses the cokernel condition and sheaf uniqueness. Empty opens
   permit an empty covering, so no point or nonemptiness assumption is hidden.
   Affine surjectivity supplies the range equality and the constructed first-isomorphism
   equivalence; no arbitrary witness is taken from an unproved existence theorem.
3. **Split statements: PASS (none).** No added holes or new public statements. The private
   helper is proved and strictly supplies the affine surjectivity step. Searched the library
   for sectionwise surjectivity and checked the existing `epi_of_surjective_app` (the opposite
   implication), the affine Cech lifting theorem, and `range_map_kernelι`. No duplicate
   unresolved statement is introduced.
4. **Shortest route and pruning: PASS.** Existing proved source declarations close the
   entire item; no unresolved Sheaf lemma is used. Each new proof import has an explicit role:
   cokernel/kernel closure, affine Cech lifting, the linear quotient equivalence, and exactness
   of forgetting modules. The report lists every old proof dependency absent from the new
   dependency set. The kernel import is replaced by the cokernel module's public import,
   while its theorem remains used. Read `dag/units/sk-thm-p1.json`'s `realized` statement
   and four step lists: neither the item nor any removed dependency realizes these steps.
   The affine Cech node of `sk-lem-picard-affine` and the exact forgetful node of
   `sk-thm-reduction` are used as general tools, not replacements for a unit's route.
5. **DAG: PASS.** Only `proof`, `proof_deps`, and `proof_origin` differ. The dependency set
   equals the union of the four steps' `uses`. Cokernel and kernel closure give the first
   step; the forgetful-functor node gives the local-surjectivity and exactness instances;
   the affine Cech node supplies quasi-coherent acyclicity used by the proved lifting
   criterion. The final step is the elementary linear first isomorphism theorem, with
   its compatibility on quotient representatives. No new node is needed.

Second reading changed the report only: added this independent review and explicit notice
of general tools filed in other units. The Lean proof and node need no repair. Closed one
original hole, added zero holes; no decomposition.
