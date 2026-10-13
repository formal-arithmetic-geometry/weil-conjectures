## What changed

Repair of the landing-tool return: removed the duplicate private theorem
AlgebraicGeometry.formalMono_of_kernel_transition_zero and added proof-only
`import all Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel`. Both existing
uses now resolve to that module's already proved private theorem. Lean compilation
confirms it is available through this import without any library interface change.
Added its existing kernel node to the upper node's proof dependencies. The second
reading below describes the previous delivery and must be refreshed by the next
reader for this repair.

Completed the proof of
AlgebraicGeometry.coherentFormalModules_restriction_limits without changing its
signature or any definition. This is a decomposition with genuine categorical and
kernel-uniqueness proofs, not a complete elimination of its geometric dependency.

Cokernel preservation is proved from ambient cokernel closure, ordinary module
restriction's left adjoint, right whiskering, and reflection by the fully faithful
inclusion. Mathlib's Preadditive.LeftExact criteria assemble preservation of kernels
and cokernels into finite limits and finite colimits. The unique zero-morphism
structures are explicitly identified when supplying the biproduct instances.

Kernel uniqueness is proved in this module: the stabilized construction supplies a
zero transition on each later levelwise kernel; epi transitions force annihilated
formal morphisms to vanish. Ordinary restriction preserves kernels, so its kernel
comparison isomorphism transports these equations. Comparing global limiting forks
then proves monicity of every restricted kernel arrow. Cancellation supplies
uniqueness for the factorization-existence lemma, and Fork.IsLimit.mk' supplies the
limiting fork. The two local private helpers are fully proved; the monicity criterion is reused from
CoherentFormalModuleKernel rather than declared a second time.

One new module states only existence of factorization through a restricted kernel,
with source, a complete proof in words, and a new node. The remaining geometric work
is comparison of restricted stabilized images and ideal-power quotients. No finite
product or cokernel assertion is delegated to it. A second new node records the
existing fully proved source-library instance for ordinary module restriction
preserving limits; no Lean declaration is duplicated for that node.

Resumed the earlier sandbox attempt, read both modules and checked the private
proofs against the construction and factorization signatures. Updated the item's
proof docstring to describe the actual Lean argument, and corrected the ordinary
restriction node's proof-step citation to match its source. Verified the source
argument at https://stacks.math.columbia.edu/tag/087X. The unit's realized steps
are preserved and no existing signature or visibility is changed.

Compiled both sandbox modules together through lcompile.py, with no errors or
warnings. deliver3.py --no-push printed OK; nothing was pushed. Checked the empty open, zero arrow, zero ideal, and unit ideal when stating
the new lemma: empty restriction and the unit-ideal category give zero objects;
for the zero arrow the kernel is the source; for the zero ideal the systems are
constant and the assertion is ordinary module-kernel factorization.

## Proved and sorry left

Upper hole closed:
AlgebraicGeometry.coherentFormalModules_restriction_limits
(lem-weil-pbc-coherent-formal-modules-restriction-limits).

One hole added:
AlgebraicGeometry.coherentFormalModules_restriction_kernel_factorization
(lem-weil-pbc-formal-restriction-kernel-factorization), in the new module
Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernelFactorization.
Its body is exactly `:= by sorry`. It asserts existence only. No sorry remains
in the item's module; no other hole is added. This is one upper hole reduced to
one strictly smaller existence lemma, net zero holes, not a complete proof.

The ordinary-restriction node attaches the already proved
AlgebraicGeometry.Scheme.Modules.preservesLimitsOfSize_restrictFunctor in
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel, lines 95-106.

## No longer needed

Retained Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel as a proof-only
`import all` to reuse its private formalMono_of_kernel_transition_zero theorem.
The duplicate local declaration and its proof have been removed. The finer
construction and factorization declarations remain necessary. No dependency
module is pruned from the closure.
No original dependency node or module is pruned from the overall route.

During development removed redundant explicit imports of
Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory and
Mathlib.CategoryTheory.Adjunction.Limits: their instances are already available
through the retained imports. All final imports serve statements or proof steps.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated a private helper already present in
CoherentFormalModuleKernel. The landing-tool rejection was correct: Lean's
proof-only `import all` supports reusing that private theorem directly. This
repair follows the requested reuse route; it adds no theorem or hole.

The original kernel node's public theorem does not expose the zero-transition
property of the kernel arrow. The finer construction theorem does, so the proof
uses that theorem and the existing factorization theorem directly. No interface
changes or adaptations are required. The old plan did not state the restriction
comparison needed for factorization existence; this is now a separate item.

The initial compile lacked the cached RestrictionObjects module and synchronization
reported an interrupted rsync. The next refresh supplied it; compilation now works.
The repository does not contain literature/stacks-project/coherent.tex, so Tag 087X
was read at https://stacks.math.columbia.edu/tag/087X. Its kernel construction and
last sentence are the source of the new factorization lemma.

The blueprint ancestor tool returned None for this item because an older node's
created.item is a module name. Following the recorded parent LocalExactness gives
thm-weil-pbc-finite-etale-lifting; new nodes record that existing ancestor and via
chain. The unit's realized nodes and route are unchanged.

Searches actually run: LeanFinder found the generic kernel/cokernel finite
preservation criteria; Loogle for the unqualified criterion returned unknown
identifier; source grep found the criteria in Mathlib.Preadditive.LeftExact.
For both new nodes, LeanSearch returned HTTP 500, recorded as unavailable;
LeanFinder and Mathlib grep were completed, then repository rg and source reads
identified the existing ordinary-restriction instance and found no formal
restriction factorization theorem. Blueprint searches for formal/kernel/restriction,
087X, and restriction/modules found no duplicate of either new statement.

## New nodes

lem-weil-pbc-formal-restriction-kernel-factorization: existence of factorization
through a restricted limiting kernel fork. This is the one remaining geometric
lemma, strictly smaller than preservation of all finite limits and finite colimits,
and smaller than the full kernel universal property because uniqueness is proved
in the item's module.

lem-weil-pbc-module-restriction-open-immersion-limits: attaches the existing proved
source-library instance for ordinary module restriction preserving limits. It
records the exact declaration needed to transport the zero-transition equations,
which the previous colimit-only node did not state. No new hole or module.

Updated the item's proof, proof_deps, and proof_origin to match the compiled proof.
No change record is necessary: all existing signatures and definitions are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered RestrictionLimits module with the repository using diff.
   The existing coherentFormalModules_restriction_limits signature, universes,
   Noetherian hypotheses, ideal, open, and both preservation conclusions are byte
   for byte unchanged. There are no changed definitions or existing visibility
   changes. The only other delivered module is the new factorization statement.
   The existing node differs only in proof, proof_deps, and proof_origin. Verdict:
   unchanged interface; no change record needed.

2. Independently compiled both modules in import order through lcompile.py (2.5 s
   and 5.0 s), with no errors or warnings. Inspected all three private helpers:
   formalMono_of_kernel_transition_zero factors the later component through its
   kernel and cancels an epi transition; restricted_construction_mono transports
   its zero equation using PreservesKernel.iso_inv_ι; restricted_kernel_mono
   constructs and compares limiting forks and transports monicity. Cokernel
   preservation uses ambient closure, whiskering, and fully faithful reflection;
   the additive finite-preservation criteria then apply. Scratch-copy #print axioms
   reports only propext, Classical.choice, Quot.sound for the first helper, and
   those plus sorryAx for the other helpers and the upper theorem. The new lemma
   also has only these four axioms. Thus the upper proof still depends on open
   imported statements, including the restriction-object property theorem, not
   just its new factorization hole. There is exactly one delivered sorry, in the
   named public factorization theorem; no forbidden declarations or hollow data.
   Verdict: valid reduction, not a sorry-free result in the import closure.

3. Read the new lemma, its full docstring and node, and Stacks Tag 087X (a)--(d)
   and its final sentence at https://stacks.math.columbia.edu/tag/087X. The lemma
   asks only for existence of a lift for an arbitrary formal source on U, through
   an arbitrary globally limiting kernel fork; it asserts neither uniqueness nor
   preservation of cokernels or finite products. Restriction of stabilized images
   and ideal-power quotients, followed by the existing factorization argument on U,
   proves this statement without extending that source to X. Checked empty U,
   zero alpha (the kernel is the source), I=0 (constant systems up to the transition
   isomorphisms), and I=O_X (zero systems). Independently searched LeanFinder for
   an open-immersion weak-kernel lift of adic coherent sheaves, Loogle for
   restrictFunctor and PreservesLimitsOfSize, and rg over Lean and the DAG. No
   existing formal-restriction factorization lemma was found. Read the existing
   ordinary-restriction limit instance at QuasicoherentKernel.lean:95 and checked
   no DAG lean.declaration already records it. This new node reuses that instance
   and adds no Lean declaration. The ideal-product restriction equality already
   in ideal_times_quasiCoherent_affine_sections supports the geometric comparison,
   but does not alone identify the quotient systems and their transitions; closing
   the new hole requires that remaining argument. Verdict: true, strictly smaller
   split; no readily available lemma closes it in a few minutes.

4. Checked the proof from the upper theorem downward, including the Mathlib
   Preadditive.LeftExact criteria found independently by LeanFinder. Public imports
   expose the restriction functor and preservation predicates used in signatures;
   new proof imports are plain imports. The new module publicly imports kernels
   because KernelFork and IsLimit occur in its signature. The old direct kernel
   dependency lem-weil-pbc-coherent-formal-module-kernel is absent from the upper
   proof_deps, but remains a dependency of the new existence lemma: its module
   is not pruned from the closure. All other old dependency nodes remain used.
   Opened dag/units/sk-thm-p1.json and checked its realized statement and steps;
   none is altered or bypassed. Verdict: the unit route is kept; no closure pruning.

5. Matched every upper-node proof step and its uses with the Lean construction,
   factorization, cokernel, restriction, and abelianness declarations. proof_deps
   is the union of the recorded uses. Checked both new nodes' source, statement
   dependencies, proof plan, search records, created, blueprint ancestry, chapter,
   unit, and lean records. The factorization signature matches its node verbatim;
   the ordinary-restriction node records the existing universe-u instance, rather
   than duplicating it. Verdict: nodes agree with the delivered argument.

Changes by the second reader: appended this independent review, including explicit
axiom-dependency and net-zero decomposition qualifications. No Lean or node repair
was needed. One original upper hole is closed syntactically and one smaller hole
is added; zero net holes are eliminated. No module is pruned from the closure.

## Second reading by S1

This reading checks the repaired delivery independently; the earlier reading above
is historical and is not the review of the current import-all repair.

1. Compared the current RestrictionLimits file against the repository with diff.
   The existing theorem signature is byte for byte identical, including universes,
   both Noetherian instances, I, U, and both preservation conclusions. No definition
   or existing visibility changes. The existing node changes only proof,
   proof_deps, and proof_origin (checked by JSON comparison). The factorization
   module is new. No change record is required. Verdict: interface unchanged.

2. Compiled both delivered modules in import order with lcompile.py: 1.8 and
   3.4 seconds, no errors or warnings. Read the reused private theorem in
   CoherentFormalModuleKernel: kernel.lift factors the later component, the assumed
   zero transition kills it, and cancellation of the source's epi transition
   proves monicity. The repaired import all resolves this very declaration; there
   is no duplicate. Read both remaining private helpers: PreservesKernel.iso_inv_ι
   transports the zero equation; image factorization proves the constructed arrow
   kills alpha; existing factorization plus monicity builds its limiting fork;
   the inverse comparison isomorphism transports restricted monicity to any fork.
   Cokernel preservation follows by whiskering and reflection by the inclusion.
   Scratch-copy #print axioms for both private helpers, the upper theorem, and
   the new factorization theorem gives only propext, Classical.choice, Quot.sound,
   and sorryAx. There is exactly one delivered sorry, the named public
   factorization theorem; no forbidden declarations or hollow definitions.
   A first scratch compile lacked sandbox import overrides; rerunning a scratch
   copy with the sandbox .lbuild available compiled cleanly. Verdict: valid
   reduction depending on open imported results, not a completed axiom-free proof.

3. Read the factorization signature, node, and full docstring, and independently
   opened Stacks Tag 087X, claims (a)--(d), the factorization paragraph and final
   sentence. It asks for existence for arbitrary T on U, without extending T to X.
   Restriction identifies the stabilized images and ideal-power quotient levels;
   the same bound c works. The existing factorization construction on U then
   descends the maps using epi transitions. Uniqueness is proved in the upper file.
   Empty U and I=O_X give zero categories; alpha=0 gives the source as kernel;
   I=0 gives systems with invertible transitions and ordinary module factorization.
   These tests reveal no missing hypothesis. Independent LeanFinder search for
   weak kernel factorization of adic coherent sheaves and repository rg found no
   proved formal restriction factorization. Found and read the existing
   CoherentFormalModulesRestrictionKernels theorem: it is still sorry, and merely
   applying it would discard the genuine uniqueness reduction here. Read the
   ordinary restriction limit instance in QuasicoherentKernel.lean:95-106; the new
   ordinary-restriction node correctly attaches this instance, with no new hole.
   Also read the ideal-product restriction equality in
   IdealTimesQuasiCoherentAffineSections: it supports, but does not alone furnish,
   all quotient/transition comparisons. Verdict: true, strictly smaller split;
   no immediately available proved lemma closes the remaining geometric hole.

4. Checked downward from finite preservation to kernels and cokernels. An
   independent Loogle search found Functor.preservesFiniteLimits_of_preservesKernels;
   read Mathlib.Preadditive.LeftExact to check its zero-morphism and biproduct
   hypotheses, supplied by the proof. Public imports serve the unchanged signature
   and the new KernelFork/IsLimit signature; added proof imports are non-public.
   The import-all repair retains the original kernel dependency. JSON comparison
   confirms no old proof_deps is removed, so No longer needed correctly reports
   no original dependency pruning. Read sk-thm-p1.json including its realized
   statement and all four realized steps: no unit node is altered or bypassed.
   Verdict: shortest concrete reduction found; unit route retained.

5. Matched the upper node's four steps against the abelian instances, ambient
   cokernel closure, ordinary restriction, stabilized construction, reused private
   monicity criterion, global factorization, and restricted factorization in Lean.
   Its proof_deps is the union of uses. Checked both new nodes' statements,
   sources, search records, created fields, blueprint ancestry, chapter, unit,
   and Lean records. The factorization signature matches its record verbatim;
   the second new node attaches the existing universe-u ordinary restriction
   instance. Verdict: nodes agree with the repaired argument.

Changes by this second reader: refreshed scratch axiom checks and appended this
review. No Lean or node change was necessary. One of one original holes is closed
syntactically and one strictly smaller hole is added: a decomposition with net
zero holes, and no module pruned.
