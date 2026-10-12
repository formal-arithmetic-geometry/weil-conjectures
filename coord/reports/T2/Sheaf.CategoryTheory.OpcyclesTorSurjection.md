## What changed
Proved the original theorem from the tensor image-inclusion kernel. Added two modules:
`Sheaf.CategoryTheory.OpcyclesTorKernelIso` proves the natural identification with Tor;
`Sheaf.CategoryTheory.TensorHomologyImageKernelEpi` proves the quotient-map step.
The original theorem signature is unchanged. Its proof composes the epimorphic natural
map with the inverse natural isomorphism and proves that every component is epimorphic.
The kernel is constructed by Mathlib, not chosen from an unproved existence statement.
No definitions or interfaces of existing modules changed; no forced adaptations.

The Tor-kernel proof applies the existing first-variable Tor sequence and Tor symmetry.
Its private proved helper establishes Tor vanishing for a flat first argument by
resolving the second argument and tensoring its exact degree-1 short complex.
The boundary is lifted to the functor-category kernel; exactness proves componentwise
injectivity and surjectivity. The second module constructs the quotient map and verifies
its naturality using the single-complex tensor comparison, and lifts kernel elements into cycles to prove
surjectivity. A private proved helper verifies that the single-complex tensor comparison
commutes with maps of the module placed in degree zero.
All three modules compile through lcompile.py. The quotient-map theorem uses a scoped
heartbeat allowance for comparing the total-complex and termwise-tensor types; each
module still compiles within the project's 60-second single-file limit.

## Proved and sorry left
Closed the original hole `CategoryTheory.exists_epi_homology_tensor_to_tor_opcycles`
(node `lem-pc-module-opcycles-tor-surjection`).
Also proved `CategoryTheory.nonempty_tor_opcycles_tensor_image_kernel_iso`
(new node `lem-pc-module-opcycles-tor-kernel-iso`).
Also proved `CategoryTheory.exists_epi_tensor_homology_to_image_kernel`
(new node `lem-pc-module-tensor-homology-image-kernel-epi`).
No sorry remains in any delivered module. One original hole closed, zero holes added:
net one hole closed. Both intermediate theorems are proved, rather than split off.
The proof still uses the existing Tor-symmetry theorem and first-variable Tor sequence.
Second-reader axiom probes confirm that the original theorem and both new public
theorems have no reachable sorryAx; all use only propext, Classical.choice, Quot.sound.

## No longer needed
Removed direct proof imports `Sheaf.Algebra.Category.ModuleCat.TorSymmetry` and
`Sheaf.Paper.TorLongExactFirstVariable` from the original module; both remain needed
and are imported by the proved Tor-kernel module. No original planned dependency is
pruned from the overall proof: the Tor facts feed the isomorphism, while tensor right
exactness feeds the proved quotient-map theorem. No unit step is bypassed.
Removed unused `Mathlib.Algebra.Homology.Bifunctor` and
`Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors` imports from the new
Tor-kernel module. The quotient-map proof uses
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` for the tensor comparison;
import_direction.py confirms that this import creates no cycle.
The earlier attempt's invalid uncommitted nodes
`lem-pc-module-opcycles-tor-surjection-partial-map` and
`lem-pc-module-opcycles-tor-surjection-epi` remain removed.

## Where the brief, the DAG or earlier work was wrong
The previous epimorphism lemma quantified over arbitrary natural transformations.
It was false: for A = Z, differential multiplication by 2, and N = Z/2, the zero
natural transformation has nonzero Tor target and cannot be epimorphic. This delivery
uses existence of an epimorphic map onto a concrete kernel and a separately proved
Tor-kernel isomorphism, so it does not reproduce that error.

Edge cases checked mathematically: with a zero outgoing differential the image kernel
is zero and the claim reduces to a map onto zero; with multiplication by 2 over Z and
N = Z/2 the kernel is nonzero and the lift from tensor cycles is surjective. No
boundedness assumption is used in either new theorem. The Tor-kernel theorem needs
flatness only in degree a; the tensor-homology theorem needs none.

The old tool import failure is repaired in the current tools: refuse_missing is now
present. No repository or launcher tool was edited or bypassed. The cited source file
is absent locally; the source was read at https://stacks.math.columbia.edu/tag/0653.
LeanFinder found Tor computation and tensor right-exactness APIs, not either new
statement. Loogle returned the Tor definition and projective vanishing. LeanSearch
returned HTTP 500 and is recorded as unavailable, not as a mathematical no-match.
Blueprint searches for opcycles tensor kernel, Tor kernel, and homology image found
no existing blueprint statement of either new lemma.

## New nodes
`lem-pc-module-opcycles-tor-kernel-iso`: the proved natural identification of first Tor
of opcycles with the tensor image-inclusion kernel; module
`Sheaf.CategoryTheory.OpcyclesTorKernelIso`. It implements Step 1 of the original plan.

`lem-pc-module-tensor-homology-image-kernel-epi`: the quotient-map and lifting argument
of original Steps 2 and 3, including naturality; module
`Sheaf.CategoryTheory.TensorHomologyImageKernelEpi`. It is proved without any flatness
hypothesis and adds no hole.
Both nodes inherit the original chapter/unit, record actual searches, and refer to the
same truncation argument of the blueprint ancestor. No change record is needed.

## Second reading by T2

1. **Interfaces: pass.** Compared the original module with the repository using
   `diff -u`. Only its two private proof imports and the theorem body differ.
   The existing theorem signature, universes, section, visibility, and docstring
   are byte for byte unchanged. Both other modules are new; no definition or
   existing statement changes, forced adaptations, or change records are needed.
2. **Proofs: pass.** Compiled all three delivered files together in import order
   through lcompile.py: 3.0 s, 9.4 s, and 1.8 s, with no errors or warnings.
   In temporary scratch copies, ran `#print axioms` on each of the three public
   theorems: precisely propext, Classical.choice, Quot.sound, with no sorryAx.
   Scanned all delivered Lean for sorry and forbidden declarations/attributes:
   none. Read both private proved helpers and the naturality, kernel lift, and
   element-lifting proofs. Objects are categorical images, kernels, resolutions,
   and explicit maps; no arbitrary data is chosen from an unproved existence.
3. **New statements: pass.** There are zero split-off holes. Both new public
   statements are proved and express strictly separate parts of the original
   argument. Checked zero complex/module, zero differential, and the complex
   Z --2--> Z with N = Z/2: the latter has tensor-image kernel Z/2, detected by
   degree-(a-1) tensor homology, and Tor_1(Z/2,Z/2) = Z/2. The kernel isomorphism
   uses flatness only at a; the quotient-map construction needs no flatness.
   Independently searched LeanFinder with derived-tensor/cokernel/flat-middle
   and termwise-tensor/differential-image queries, and searched Mathlib and both
   library roots with Tor-flat and tensor-descHomology patterns. Candidates were
   tensor exactness and kernel equivalences requiring different flatness, or
   group (co)homology sequences; none replaces either new theorem. The existing
   first-variable Tor sequence and symmetry are used rather than restated.
4. **Route and pruning: pass.** Read from the original theorem down through the
   two helpers and their imported APIs. The natural map is explicitly composed
   with the inverse kernel isomorphism. Its epimorphism follows componentwise.
   The public imports supply statement notation or instances (in particular,
   ModuleCat.Projective supplies the projective-resolution instance required
   by Tor'); the single-complex comparison and other proof APIs are private
   imports. All seven old proof dependencies remain used through the helpers:
   flat-ring-map, tor-modules, tor-long-exact-first-variable, tor-symmetry,
   tensor-right-exact, tensor-complex-sheaves, and acyclic-complex-modules.
   None is pruned from the overall argument. Read the unit record
   dag/units/sk-thm-picard-duality.json: this item is not a realization entry,
   and the internal Tor argument changes no chapter or unit route.
5. **DAG agreement: pass.** Checked the three node records against the Lean.
   The original node composes exactly the two new theorems; each helper's proof
   steps describe the constructions actually used, and proof_deps equals the
   union of those steps' uses. Each new record has its source, statement
   dependencies, searches, origin, blueprint ancestry, chapter/unit, creation
   record, and verbatim Lean signature. No new hole is hidden behind a node.

Second reading changed only this report: recorded the independent checks and
replaced the provisional dependency-axiom caveat with the successful axiom audit.
No Lean or DAG repair was necessary. Original holes closed: one of one; holes
added: zero; new proved helper theorems: two; pruned modules: none.
