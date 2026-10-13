## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_coherent_open_section_carrier` in
`Sheaf.AlgebraicGeometry.CoherentOpenSectionCarrier`, with its signature unchanged.
Added proof-only imports of `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`.

Constructed the rank-one free map corresponding to the open section and its abelian
image. Private proved helpers transport quasi-coherent image closure through the
slice/open-subscheme equivalence and exhibit finite local generators of that image.
These follow the existing private helpers in ModuleFiniteTypeAffineCapture.
The existing submodule extension theorem produces the global finite-type carrier;
the existing coherence criterion makes it coherent. Evaluating the inverse extension
isomorphism produces the required section, and the commuting inclusion equation
proves its image equals the original section. Updated the node proof and dependencies
to describe these actual steps. No arbitrary existential witness defines a library
object: the cyclic image is the categorical image of an explicit free map.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_coherent_open_section_carrier`
(node `lem-pc-coherent-open-section-carrier`). No holes added or split off, and no
`sorry` remains in the delivered module. Both finite-type extension and the coherence
criterion are existing declarations with completed local proofs; the target still
depends on sorryAx through existing imported dependencies, as the second reading
verified. It is not yet a fully axiom-clean target. Private helpers are fully proved.
The construction includes the empty open and zero section without extra hypotheses.

## No longer needed

None. Both original proof dependencies are used, and both original public imports
are needed by the statement. No imports were removed. The proof does not introduce
any auxiliary modules or nodes. The unit realization is empty, and its route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan was correct but omitted the explicit kernel/cokernel closure
dependencies needed for the quasi-coherence of the cyclic image on the slice site.
Those existing nodes are now recorded. An epimorphism of sheaves need not be
surjective on sections of U; the proof lifts the particular original section using
its known free basis preimage, then the extension isomorphism, rather than assuming
sectionwise surjectivity. No statement or definition was changed.

## Second reading by N3

1. PASS: Compared the sole delivered module with the repository using diff and
   separately compared the existing theorem signature byte for byte. Its signature,
   visibility, and docstring are unchanged. Only proof-only imports, private proved
   helpers, an explicit private section construction, and the theorem proof were
   added. No existing definition or statement changed; no change record is needed.
2. PASS: The module compiles locally through lcompile.py without errors or warnings.
   There is no sorry or forbidden declaration in the module. The section construction
   consists of actual restrictions with a proved compatibility equation; the cyclic
   image is the categorical image of the explicit rank-one free map. The existential
   extension witness is used only within the theorem proof, never to define arbitrary
   library data. A scratch copy checks the axioms of all four delivered declarations.
3. PASS: No statements were split off, no holes added, and no new nodes require
   checking. Reviewed the private helpers: quasi-coherence follows from kernel and
   cokernel closure under the slice equivalence; the finite free generators descend
   through the image epimorphism. These remain valid for empty U, zero morphisms,
   and rank zero. The section restriction construction also handles the empty open.
4. PASS: Read both original dependencies and searched the library and Mathlib for
   image finite-type and section-carrier results. Additional searches used Loogle
   `SheafOfModules.GeneratingSections.ofEpi` and Lean Finder's quasicoherent-section
   containment query. Mathlib supplies the generating-section image construction
   already used here; no shorter direct carrier theorem was found. The matching
   slice helpers in ModuleFiniteTypeAffineCapture are private and cannot be reused
   as public declarations. Both original dependency nodes are used; none is pruned.
   Both public imports support the signature; all added imports are proof-only and
   used. The unit sk-thm-picard-coherence has empty realization entries, unchanged.
5. PASS: Compared the old and delivered node: only proof, proof_deps, and proof_origin
   changed. Their steps match the explicit cyclic image, kernel/cokernel closure,
   finite-type submodule extension, coherence criterion, and evaluation of the
   extension isomorphism. Checked the four dependency nodes' Lean declarations.

Changes by the second reader: appended this independent review and axiom-check
results. No repair to the Lean proof or DAG was needed. The sole original hole is
closed, with zero holes added; this is a proof, not a decomposition.

Axiom-check result: quasiCoherent_slice_image, finiteType_image_free_slice, and
section_on_open use only propext, Classical.choice, and Quot.sound. The carrier
theorem additionally uses sorryAx from existing imported results. Thus this delivery
closes one local hole without adding any, but does not certify the transitive target
closure as complete. No new axiom or hidden local sorry was introduced.

The dependency probe identifies the existing finite-type submodule extension theorem
as depending on sorryAx. The coherence criterion uses only the three standard
axioms. These imported results were not changed in this delivery.
