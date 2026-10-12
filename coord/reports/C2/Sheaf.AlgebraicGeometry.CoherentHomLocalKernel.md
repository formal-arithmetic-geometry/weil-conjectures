## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_coherent`
by an explicit two-step reduction: obtain a local finite free cokernel presentation from
coherence, then obtain the Hom kernel on that same open using that specified presentation.
The existing target signature and its public imports are byte-for-byte unchanged.
The two intermediate statements are in new modules
`Sheaf.AlgebraicGeometry.CoherentLocalFinitePresentation` and
`Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation`, imported only for the target proof.
No definitions, existing statements, or data constructions are changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_coherent` (1 of 1 original holes).
Added two named theorem holes, and only these:

- `AlgebraicGeometry.Scheme.Modules.coherent_local_finite_presentation`, node
  `lem-weil-pbc-coherent-local-finite-presentation`, in
  `Sheaf.AlgebraicGeometry.CoherentLocalFinitePresentation`.
- `AlgebraicGeometry.Scheme.Modules.homObj_locally_kernel_of_local_presentation`, node
  `lem-weil-pbc-coherent-hom-local-kernel-from-presentation`, in
  `Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation`.

This is a decomposition, not an axiom-free proof or net sorry reduction: one original
hole closes and two strictly smaller holes are added (delivery-local net -1).
The first intermediate statement constructs the presentation without mentioning F or Hom.
The second uses a specified presentation without coherence and proves a kernel description
on the fixed open with the same ranks. It does not assert existence of a presentation.
No split-off hole was closed during the second reading. All remaining holes are exactly
`:= by sorry` in named public theorems, with source and complete proof docstrings and nodes.

## No longer needed

Removed the target module's proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel`; its planned
left-exactness theorem is now imported by `HomLocalKernelOfPresentation` instead.
There are no modules pruned from the delivery's import closure.

The original target proof dependencies no longer used directly by its new proof are:
`def-pur-sheaf-hom`, `def-weil-pbc-module-finite-type-presentation`,
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-sheaf-hom-finite-presentation-kernel`, and `pqf-def-coherent`.
These remain dependencies of the intermediate statements or their planned proofs;
they are not claimed as globally pruned. The target's direct proof dependencies are now
exactly the two new nodes. No unit-level realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The first submission compiled, but its two new node statements had been copied from the
original target and did not describe their Lean declarations. Their proofs and sources
were generic copies, and the second node incorrectly depended on the first even though
it assumed its presentation. Copied review fields falsely suggested these new nodes
had previously been reviewed. The original target node was not updated to its new proof.
The helper comments were not proper theorem docstrings with complete proofs, and the
original target's docstring had become attached to the first helper. Those faults are
repaired. The second helper now has a fixed-open, fixed-presentation statement, and each
helper is placed in its own new module as the brief requires.

The sources are not present under this clone's literature directory. I checked the
published Stacks statements and proofs directly:
[01BW](https://stacks.math.columbia.edu/tag/01BW),
[01CQ](https://stacks.math.columbia.edu/tag/01CQ),
[01CO](https://stacks.math.columbia.edu/tag/01CO), and
[0E8H](https://stacks.math.columbia.edu/tag/0E8H).
These justify the coherence-to-presentation argument and the Hom kernel argument without
Noetherian or target-coherence assumptions.

## New nodes

`lem-weil-pbc-coherent-local-finite-presentation` records only the local finite free
cokernel presentation supplied by coherence (01BW). It has no target F or Hom conclusion.
Its Lean statement is recorded verbatim, with the scheme, coherence, module category and
finite presentation definition dependencies, a three-step proof, and three search kinds.

`lem-weil-pbc-coherent-hom-local-kernel-from-presentation` records the Hom kernel for an
arbitrary G and F given a specified presentation on V. It retains V and the ranks rather
than assuming the existence of a local presentation. Its dependencies include the existing
left-exact Hom theorem; proved upstream `homObjFreeIso` and `overHomObjIso`, and Mathlib's
`overEquiv` / `overFunctorEquiv`, supply the coordinate and restriction identifications.
No change record is needed: all statement changes concern new, undelivered declarations.

## Second reading by C2

1. Compared every delivered existing module to the repository with `diff`, and checked the
   original target signature byte-for-byte. Verdict: unchanged; only its proof and proof-only
   imports change. No definitions or existing signatures are altered. The original theorem's
   docstring is restored to it. The two new statements have their own modules.
2. Compiled the three modules in import order through `lcompile.py`; all compile without
   errors or warnings. Audited the source: exactly the two listed named theorem sorries;
   no axioms, unsafe declarations, opaque declarations, extern or implemented_by attributes,
   or data definitions. The explicit `#print axioms` scratch check is recorded below.
3. Read both split statements against Stacks 01BW, 01CO/01CQ and 0E8H and supplied complete
   docstring proofs. Checked ranks zero, G = 0 and F = 0: the zero-object and cokernel/kernel
   universal properties give the expected statements. An empty scheme makes the pointwise
   first claim vacuous; an empty V gives the trivial module category in the second claim.
   No extra assumption on X or F is used. Repeated leanfinder, loogle and grep searches with
   different queries, and searched both library roots. Presentation constructors and proved
   Hom/free and slice-restriction isomorphisms exist, but neither full intermediate claim does.
   The private coherent-to-finite-presentation proof in TwistedSectionsFiniteDimensional
   assumes IsLocallyNoetherian and cannot apply here. Verdict: true, needed, strictly smaller
   statements; no directly applicable existing replacement found.
4. Read the target from the top down and its original dependencies, including
   `homObj_precomposition_exact`. The two steps follow the original source route. The import
   moved to the second helper is reported above, along with all old direct proof dependencies.
   Read `dag/units/sk-thm-p1.json` and its `realized` statement and steps: this node is below
   those unit realizations, and none is changed or bypassed. Verdict: decomposition preserves
   the route; no global module pruning or net proof progress is claimed.
5. Matched the nodes to Lean: corrected both new prose statements, verbatim Lean signatures,
   module paths, source places, dependencies and proof steps; removed copied review history.
   Updated the original node's proof, proof_deps and proof_origin to its actual reduction.
   No cycle between the two intermediate nodes remains. Verdict: records agree with Lean.

Changed during second reading: separate helper modules; fixed-open second helper; proper
proof docstrings; restored target docstring; explicit witness composition; corrected new
and existing DAG records; additional searches; accurate decomposition and pruning report.

Axiom audit: `#print axioms` for all three delivered theorem declarations printed
exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the last from the
two documented open intermediate theorems. The scratch copy compiled and was removed.

Preflight repair: its three search categories require LeanSearch separately from
Loogle/LeanFinder. Ran LeanSearch for each new claim; both attempts returned Internal
Server Error and are recorded as unavailable, without a mathematical verdict. The
completed Loogle/LeanFinder and local grep checks above still supply the search evidence.
