## What changed

Closed `AlgebraicGeometry.artinSchreier_data_exact_components` by a complete Lean reduction
with its original statement unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.ArtinSchreierKernelSections`, plus the upstream affine-space
Artin–Schreier module, local-surjectivity API, and lifted-field instances.

Two private helpers are proved: sectionwise injectivity and lifting imply the kernel
universal property, and a section acquires an Artin–Schreier preimage on a surjective
etale cover. The latter uses the already proved upstream affine-space map, base change,
and its pulled-back coordinate. The main proof constructs the image-sieve covering,
proves epimorphicity, constructs the kernel limit, and derives exactness and monicity.
The original `hG` hypothesis is retained without changing the statement; the section
formulas suffice for the argument.

## Proved and sorry left

The original one sorry in `AlgebraicGeometry.artinSchreier_data_exact_components` is
closed. Both private helpers have complete proofs. The delivery leaves exactly one
new sorry: `AlgebraicGeometry.artinSchreier_kernel_sections`, node
`lem-sc-as-kernel-sections`, in its own module. This is strictly the sectionwise
prime-field kernel argument; it asserts neither epimorphicity nor short exactness.
The docstring and node give the local-ring calculation and sheaf descent proof.
Local compilation succeeds for both modules; the delivery dry run checks the server.

Edge cases checked: p is prime by positive field characteristic; a root on a
disconnected object may vary between components and is represented by a section of
the constant sheaf, rather than one ZMod element. Empty objects have unique sections
and the kernel statement uses the empty cover. The pulled-back cover construction
also applies to the empty object. No algebraic closedness, curve hypothesis, or hG
is needed for the kernel lemma or the cover construction.

## No longer needed

No original import was removed: the existing public imports preserve the module's
exported interface. The cyclic proof dependency `lem-sc-as-sequence` (module
`Sheaf.AlgebraicGeometry.ArtinSchreierSequence`) is no longer needed by this node and
was replaced with `lem-sc-as-kernel-sections`. This is a dependency of the assigned
node being pruned, not a claim that the parent sequence module is globally unreached.

The epimorphism step needs no new covering lemma with sorry, nor imports of the
planned standard-etale derivative, nonempty geometric fibers, or geometric-stalk
exactness/conservativity modules. The proved upstream affine-space lemmas provide
this step directly. The new kernel obligation retains the local-ring calculation.

## Where the brief, the DAG or earlier work was wrong

The assigned node's sole proof dependency was its parent `lem-sc-as-sequence`, whose
Lean module reaches this node through `ArtinSchreierExact`; importing it would make
an import cycle. The dependency therefore did not provide a usable proof plan.
The parent node's detailed local-root and local-cover argument was used instead.
Also, kernel sections are locally varying constants on disconnected etale objects;
they need not be single constants. The new statement makes this distinction explicit.
LeanSearch returned an Internal Server Error; its recorded search is unavailable,
not evidence of absence. LeanFinder, Loogle, source grep and upstream searches ran.

## New nodes

`lem-sc-as-kernel-sections` in
`dag/nodes/sec-curve-estimates/lem-sc-as-kernel-sections.json`, module
`Sheaf.AlgebraicGeometry.ArtinSchreierKernelSections`: sectionwise injectivity and
lifting for the prime-field inclusion. It isolates only the kernel portion of the
source argument, for any scheme over a field of prime characteristic. Its hypotheses
fix the natural section equivalences and the inclusion's values on sheafification-unit
constants. Its proof plan uses the existing local-ring root lemma and sheaf descent.
The unit record `sk-prop-h2` has no realized nodes here; its route is unchanged.
No statement or definition change record is needed.

## Second reading by C1

1. Compared the delivered existing module and node with the repository using diff.
   The full signature of `artinSchreier_data_exact_components` is byte for byte
   unchanged. There is no changed definition or target statement, no adapted module,
   and no added public import in that module. Verdict: pass.
2. Compiled both delivered modules in import order through `lcompile.py`: clean,
   without warnings (2.9 and 3.8 seconds). Explicit `#print axioms` probes in temporary
   copies show only propext, Classical.choice and Quot.sound for both private helpers.
   The main theorem and the new kernel theorem additionally use sorryAx, as expected
   from the single open kernel obligation. No prohibited declaration, hollow
   definition, or other sorry occurs in the delivery. Verdict: pass as a reduction;
   the original theorem is not yet independent of sorryAx.
3. Read the new kernel statement, its docstring and its complete node. Checked prime
   characteristic (so p is at least 2), disconnected objects (constants may vary),
   empty objects (empty-cover sheaf condition), and local rings with nilpotents
   (the local-ring lemma does not assume reducedness). Restriction naturality and
   the prescribed values on the sheafification unit fix the inclusion. The local
   root calculation, refinement of covers, separatedness, and gluing prove precisely
   the two asserted clauses. This is strictly the kernel portion, with no claim
   about wp, local surjectivity, or short exactness. Independent LeanFinder search
   for the constant finite-field sheaf kernel found no matching theorem; Loogle
   search for kernel-fork limits returned the universal-property constructors
   already used. Grep searches using `isLimitOfInjective`, locally constant roots,
   and kernel-section terminology found no existing kernel-section result. Read
   `ArtinSchreierSchemeSectionExact`: its still-open theorem asserts full short
   exactness and is not a shorter proved kernel tool. Closing the new obligation
   requires the scheme-germ/sheaf-descent formalization, not a few-minute repair.
   Verdict: true, properly sourced and documented, with no duplicate found.
4. Read the proof downward: kernel-section identification supplies unique lifts;
   injectivity proves additivity and naturality of those lifts; the kernel universal
   property gives exactness and monicity. Independently checked the upstream
   affine-space surjectivity and etaleness lemmas, the prime-field base change,
   pullback coordinate equation, and singleton image-sieve covering. The covering
   argument is fully proved and needs no additional split-off obligation. All new
   imports in the existing module are proof-only. The new kernel module's private
   imports retain its documented proof plan. The complete old proof_deps list was
   just `lem-sc-as-sequence`; it is listed under No longer needed. The unit
   `sk-prop-h2` has empty realized fields here and its route is preserved.
   Verdict: pass; no shorter proved route found.
5. Checked the modified proof, proof_deps and proof_origin against the Lean, and
   checked every required new-node field, the union of step dependencies, and the
   byte-identical new-node Lean signature. The new node records its search-service
   failure honestly. No unowned existing-node field is changed. Verdict: pass.

Second-reading changes: appended this review and performed independent searches,
local compilation, and explicit axiom probes. No Lean or node repair was needed.
Temporary probe copies were removed before delivery.
