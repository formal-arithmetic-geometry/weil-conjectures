## What changed

`lean/Sheaf/AlgebraicGeometry/FormalCompletionExact.lean` now proves
`AlgebraicGeometry.formalCompletion_exact` with its original signature and visibility.
It constructs the coherent abelian structure from the existing general ringed-space
closure theorem and Mathlib's full-subcategory criterion. It proves completion additive
by cancelling the quotient projection, and proves preservation of epimorphisms at every
quotient level and then in the full formal subcategory.

The global argument uses the existing local exactness theorem on the cover of all affine
opens. An affine kernel fork supplies middle exactness and the first-arrow monomorphism.
For the second-arrow epimorphism, the proof restricts the canonical kernel short exact
sequence of the globally completed epimorphism. It then assembles short exactness with
`ShortExact.mk'` and the covering criterion. The two private witness helpers keep the
original zero-morphism structure when extracting homology and kernels from abelianness;
this avoids changing the public preadditive structures.

Added the proof imports `Mathlib.CategoryTheory.Abelian.Subcategory`,
`Mathlib.Algebra.Homology.ShortComplex.Abelian`, and
`Sheaf.AlgebraicGeometry.FormalCompletionAffineKernel`. The original public imports,
existing theorem signature, definitions, and declaration docstring are unchanged.
The new module records only the missing affine kernel argument. Updated the original
node's `proof`, `proof_deps`, and `proof_origin` to the actual Lean reduction.

Both delivered modules compile through `lcompile.py --all` with no compiler errors or
warnings. No other existing module is adapted. No definition, target, or existing
interface is changed. The item's unit `sk-thm-p1` and all its realized statements and
steps are untouched.

## Proved and sorry left

Closed the original direct hole in `AlgebraicGeometry.formalCompletion_exact`
(node `lem-weil-pbc-formal-completion-exact`). Its body is a complete proof from named
statements, not a partially holed proof. Private helpers proved in the item's module:
`hasHomology_of_abelian_witness`, `hasKernels_of_abelian_witness`,
`completion_additive`, `coherent_closedUnderKernels`, `coherent_closedUnderCokernels`,
`coherent_abelian`, and `completion_epi` (all under namespace `AlgebraicGeometry`).
None contains a `sorry`.

Added exactly one direct hole:
`AlgebraicGeometry.formalCompletion_affine_kernel`
(node `lem-weil-pbc-formal-completion-affine-kernel`), in its own new module. It is a
public theorem with proof exactly `:= by sorry`, a source, and a complete mathematical
proof in its docstring and DAG node. It asserts only a limiting kernel fork after affine
restriction. It does not assert global exactness, additivity, abelianness, or preservation
of epimorphisms. The original result genuinely combines this smaller assertion with
separately proved epimorphism preservation and the existing local criterion.

This is a decomposition: one upper hole closed, one strictly smaller lower hole added,
net zero direct holes. It is not a sorry-free proof of completion exactness. Existing
holes in imported library modules are unchanged.

Edge cases checked mathematically before stating the new lemma: for the empty affine
open every module is zero; for I = 0 the quotient system is constant and the fork is the
original kernel; for I = O_X every completed object is zero. For the sequence
Z --p--> Z --> Z/p, quotient-level multiplication by p need not be injective, so the
new statement deliberately concerns the kernel in the formal category rather than
termwise kernels. None of these cases requires excluding an ideal or a zero object.

## No longer needed

Removed these eight direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.RingTheory.AdicCompletionNoetherian`

The node `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` and its module are unnecessary
for this argument, including the new affine kernel plan: the general ringed-space
coherent closure theorem already gives the required kernels, cokernels, and sums.
The explicit `CoherentFormalModule` import is redundant because the preserved public
abelian import already exposes its definitions; the definition node remains necessary.

The affine equivalence, finite affine sections, ideal-product sections, quasi-coherent
cokernel sections, and completion-Noetherian-ring arguments have been localized to the
new affine kernel node. Their direct imports are absent from the original module, but
these facts remain necessary to the new node's planned proof; this report does not claim
that they have been eliminated from the mathematical argument or the targets' closure.
The finite-module completion, finite-module abelianness, affine adjunction, and equivalence
nodes similarly move out of the original proof_deps into the new node's proof_deps.
No whole-library pruning claim is made before the maintainer measures the closure.

For completeness, the old proof dependencies removed from the original node are:

- `def-weil-affine-spectrum`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-abelian-exact-epi-cokernel`
- `lem-weil-pbc-abelian-short-exact-kernel`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
- `lem-weil-pbc-completion-exact-finite-modules`
- `lem-weil-pbc-equivalence-injective-resolutions`
- `lem-weil-pbc-finite-modules-noetherian-abelian`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `pqf-lem-coherent-ft-locnoeth`

All except the locally Noetherian coherent-closure node and the two abelian
kernel/cokernel nodes remain in the affine kernel node's planned dependencies.
The original proof does not use `ShortExact.fIsKernel` or `Exact.gIsCokernel`,
the results of those latter two nodes: it uses the converse kernel-to-exactness
lemma `exact_of_f_is_kernel`, the canonical `kernelIsKernel`, and elementary
assembly with `ShortExact.mk'`. This is pruning of direct planned dependencies,
not a claim that these Mathlib modules leave the targets' import closure.

An attempted use of `CoherentFormalModuleEpi` was also removed before delivery:
the stronger statement that every quotient component of a completed epi is epi follows
directly by cancelling a cokernel projection, so the first-component Nakayama criterion
is not needed here.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The original plan's
locally Noetherian coherent-closure dependency is redundant: the existing general
ringed-space theorem already supplies that part. The source plan remains applicable to
the affine kernel gap; the global Lean proof no longer needs to repeat the affine
argument for preservation of epimorphisms.

The local checkout does not contain `literature/stacks-project/coherent.tex`.
Read the primary source pages directly: Stacks [0881](https://stacks.math.columbia.edu/tag/0881),
[087W](https://stacks.math.columbia.edu/tag/087W), and
[00MB](https://stacks.math.columbia.edu/tag/00MB). Their affine-equivalence and finite-module
completion route agrees with the new node. The bibliography path is kept as the project's
canonical source identifier.

LeanSearch returned Internal Server Error for the affine kernel query; its search record
says unavailable, not no match. LeanFinder and Mathlib/source grep were run. The whole
blueprint search for completion kernel found no matching statement.

## New nodes

`lem-weil-pbc-formal-completion-affine-kernel`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-completion-affine-kernel.json`,
states `AlgebraicGeometry.formalCompletion_affine_kernel` in
`lean/Sheaf/AlgebraicGeometry/FormalCompletionAffineKernel.lean`. It isolates the affine
kernel universal property from steps 2--6 of the original node. Its five proof steps
record restriction and finite affine sections, quotient identifications, the affine
completion equivalence, algebraic injectivity/middle exactness, and transport of the
kernel fork. Its statement is strictly weaker than the original global exactness result.
No change record is required: no existing signature, definition, public import, or
visibility is changed.

## Second reading by R4

1. **Interfaces: pass.** Read both delivered modules and compared the existing module
   with the repository using `diff -u`. The sole existing public theorem's signature
   is byte-for-byte unchanged (also checked by extracting its text before `:=`).
   Its visibility, docstring, public imports and definitions are unchanged. Only
   proofs, private proved helpers and private proof imports are added or changed;
   the affine kernel theorem is a new statement in its own module. No change record
   or forced adaptation is necessary.
2. **Kernel-checked proof: pass as a decomposition.** Independently ran
   `lcompile.py --all` on the two modules: both compile without warnings or errors.
   Searched delivered Lean for sorry and forbidden declarations/attributes: exactly
   one sorry remains, the named public affine kernel theorem, with its docstring and
   node. There are no new definitions or arbitrary data witnesses. Appended
   `#print axioms` for the seven private helpers and both public theorems to a scratch
   copy and compiled it through `lcompile.py`. The two structure-compatibility helpers
   and additivity use only `propext`, `Classical.choice`, `Quot.sound`; the other
   helpers and public theorems additionally use `sorryAx` from the named remaining
   statements in their import closure. No other axiom occurs. Removed the scratch copy.
   The use of kernel objects is governed by their universal property, and the
   zero-morphism compatibility helpers preserve the original short complexes.
3. **Split statement: pass.** Read the full signature, mathematical proof and node.
   The equality after the full inclusion specifies genuine termwise restriction;
   it does not permit a different functor that could trivialize the claim. The fork
   asserts precisely injectivity and middle exactness on an affine open, omitting
   epimorphism preservation, global descent, additivity and abelianness. It is a
   strict part of the original argument. Checked empty opens, zero modules, zero
   and unit ideals, and the sequence Z --p--> Z --> Z/p: individual quotient maps
   can fail to be injective, but the completed fork has the asserted universal
   property. Re-read [0881](https://stacks.math.columbia.edu/tag/0881),
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [00MB](https://stacks.math.columbia.edu/tag/00MB); their affine reduction,
   equivalence and algebraic exactness justify the docstring argument.
   Independent LeanFinder search: "inverse systems of finite modules completion
   preserves kernel universal property" returned lifting/universal-property results
   (`IsAdicComplete.of_comp_lift`, `AdicCompletion.lift`, etc.), not this sheaf theorem.
   Loogle query `AdicCompletion.map` returned completion maps and functoriality,
   not the sheaf comparison. Ran launcher grep and separately searched both Lean
   roots for completion/exactness/kernel combinations. Inspected Mathlib's
   `AdicCompletion.map_injective` and `map_exact`: these supply the algebraic step
   already in the node, but do not identify restricted coherent sheaf systems with
   those algebraic completions. Closing that comparison is substantial work, not
   a direct application that can be completed in a few minutes.
4. **Top-down reduction and pruning: pass.** Read the closure, affine equivalence,
   local exactness and full-subcategory declarations used by the argument. The
   proof gives coherent abelianness and quotient-map additivity, proves quotient
   epis directly, then reduces only the remaining kernel property to the affine
   theorem. Applying restriction exactness to the canonical global kernel sequence
   establishes the local epi without assuming completion exactness. Every added
   proof import is private; the new module's public imports supply its signature.
   The report now enumerates all 15 original proof dependencies removed from the
   original node and distinguishes relocated dependencies from unused ones. Read
   `dag/units/sk-thm-p1.json`, including `realized`: neither the item nor its new
   kernel node replaces a realized unit statement/step; no unit or chapter route
   changes. No whole-library pruning or net-positive hole claim is made.
5. **DAG consistency: pass after the record correction.** The existing node changes
   only `proof`, `proof_deps` and `proof_origin`; each proof-dependency list equals
   the union of its steps' `uses`. Checked the named declarations or Mathlib matches
   of the cited dependencies. The original node describes the actual Lean proof,
   while the new node records the sourced affine kernel argument, statement
   dependencies, search evidence, creation information, chapter, unit and Lean record.
   Its Lean statement is now recorded verbatim, including line breaks.

Second-reading changes: completed the `## No longer needed` dependency list and
clarified which nodes move to the affine argument; replaced the normalized single-line
new-node Lean signature with the verbatim signature; added this independent review.
No Lean proof, public interface, definition or hole count was changed by the second reader.
