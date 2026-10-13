## What changed

Proved `HomologicalComplex₂.verticalCutoff_endpoint_forks` in
`Sheaf.Algebra.Homology.VerticalCutoffEndpointForks`, without changing its signature,
visibility, or existing docstring. Added six proved private helpers for the integer
kernel fork, the opcycles cokernel, the cycles-to-homology cokernel, and their transports.
The helper returning an `IsColimit` structure is a noncomputable definition with a
complete proof, not a theorem or a hole.

Added proof-only `import all` of `VerticalCutoffComparisonEpi` to reuse its proved
private inclusion lemma and the proved coordinate lemmas of its two imports,
`UpperTruncationStepSES` and `LowerTruncationTransitionKernel`. No imported holed
theorem is used. The final compile checked that no direct imports of those two
modules are needed.
Updated the item's node proof, proof dependencies, and proof origin to record these
helpers and the actual formal argument. No public import or interface changed.

The argument follows Stacks Tag 0118, cochain truncations (3) and (4), read from
https://stacks.math.columbia.edu/tag/0118. The adjacent endpoints use homology naturality
and the invertible homology projection of the lower truncation, avoiding an additional
window-to-homology coordinate theorem. The unit record's `realized` entries are empty;
no unit statement or step is bypassed.

Searches: LeanFinder for smart-truncation boundary kernel/cokernel properties returned
truncation differential and complementary-truncation APIs, not the exact paired theorem.
Loogle for `cyclesIsKernel` returned the ShortComplex and HomologicalComplex kernel
universal properties. The recorded grep for
`cyclesIsKernel|opcyclesIsCokernel|homologyIsCokernel` found their Mathlib implementations.
Local searches located the three proved coordinate-helper modules reused here.

## Proved and sorry left

Closed: `HomologicalComplex₂.verticalCutoff_endpoint_forks`
(node `lem-sp-vertical-cutoff-endpoint-forks`), the only original hole.
Added: none. Remaining in the delivered module: none. This is a proof, not a
decomposition. All six private helpers are complete.

The single-file compile passes without warnings. A separate scratch probe reports
exactly `propext`, `Classical.choice`, and `Quot.sound` for the public theorem.
All lines are at most 100 characters. The proof includes `a=1`, `b=a+1`, zero objects,
and zero differentials: arithmetic uses only `0<a<b`; the boundary case is handled
explicitly, with no additional exactness or nonvanishing hypothesis.

## No longer needed

Removed the two redundant exploratory direct imports of `UpperTruncationStepSES`
and `LowerTruncationTransitionKernel`: their proved helpers remain available through
the proof-only `import all VerticalCutoffComparisonEpi`. These two modules remain
needed transitively; no original dependency node or module is pruned. The original
public tower-map import supplies the statement's definitions. No new unfinished
theory is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG plan was sufficient, and its transports
are now actual Lean constructions. The local repository has no Stacks source text at
`literature/stacks-project/homology.tex`; the cited official Tag 0118 page was read instead.

## Second reading by G2

1. Interface: PASS. Compared the entire delivered module with the repository using
   `diff -u`, then compared the exact text from `theorem verticalCutoff_endpoint_forks`
   through its `:= by`. Its signature, universes, category assumptions, visibility,
   docstring and original public import are unchanged. Only six private proved helpers,
   one proof-only import and the replacement proof were added. No change record is needed.
   The two conclusions still concern the prescribed `g` and restricted lower-projection
   component, including their actual zero-composite witnesses and universal properties.

2. Proof: PASS. Independently compiled the delivered file with `lcompile.py` (3.3 seconds,
   no warnings or errors). Compiled a fresh scratch copy of exactly this file with
   `#print axioms HomologicalComplex₂.verticalCutoff_endpoint_forks` (3.1 seconds):
   only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Searched the delivered
   Lean for sorry, axiom, unsafe, opaque, implemented_by, extern and skipKernelTC:
   none occur. `cokernel_post_iso` constructs colimit data by `IsColimit.ofIsoColimit`
   from its supplied colimit and explicit cofork isomorphism; it selects no arbitrary
   witness from an unproved existence theorem. The other helpers return proof-valued
   existential/nonempty propositions and are fully proved.

3. Split statements: PASS, none. Checked the six private helpers directly against their
   bodies. `upper_boundary_kernel` transports `cyclesIsKernel`; `nested_upper_kernel`
   cancels the mono inclusion in degree a and transports along the isomorphism in degree
   a-1, using exactly its factorization hypothesis. `lower_boundary_cokernel` transports
   `opcyclesIsCokernel`. `cycles_lower_boundary_cokernel` transports `homologyIsCokernel`
   through the lower projection's homology isomorphism and the target's invertible
   homology projection, justified by its zero incoming differential. The last helper
   treats both a<t and a=t, with no unmentioned strictness assumption. At a=1 restriction
   uses degrees 0 and 1. At b=a+1 the upper-boundary cycles branch is used, rather than
   incorrectly asserting that the upper inclusion at a is invertible. Zero complexes
   and zero differentials satisfy the same transports and universal properties.

4. Route and pruning: PASS. Read the official Stacks Tag 0118 cochain truncations (3)
   and (4): boundary objects are respectively kernel and cokernel of the specified
   differential. Checked the cited private helpers in UpperTruncationStepSES,
   LowerTruncationTransitionKernel and VerticalCutoffComparisonEpi: their proofs are
   complete, and their coordinate equalities are precisely those used here.
   Independent Loogle search `"truncLE", "IsLimit"` returned no match. Independent
   LeanFinder search for inclusion into smart truncation as boundary kernel and
   truncation of quotient as incoming cokernel returned the general truncation short
   complex, complementary-truncation API and `truncLE'_d_eq_toCycles`, not this nested,
   restricted pair of forks. Grep of Mathlib's Embedding modules and the local Homology
   modules found coordinate APIs and downstream users, no shorter matching endpoint
   theorem. The proof already uses Mathlib's universal properties directly.
   The single added `import all VerticalCutoffComparisonEpi` supplies the used private
   inclusion lemma and the two transitive coordinate-helper modules; it is proof-only.
   No original import or proof-dependency node is removed: the original dependencies
   are the window and tower-map definitions. Thus the pruning list is none; the earlier
   report's removed direct imports refer only to exploratory imports, not baseline ones.
   Read dag/units/sk-prop-av-pqf-finite.json, including its recorded statement and step
   text. The referenced blueprint section is absent from this checkout. The unit is
   the proper/quasi-finite geometric proposition, and its `realized` statement
   and step lists are empty. This boundary argument bypasses no recorded unit step.

5. DAG: PASS. Compared the complete node JSON with the repository. Only `proof`,
   `proof_deps` and `proof_origin` changed. The statement and Lean signature record
   remain unchanged. The four steps accurately describe the kernel transport, lower
   and cycles cokernel constructions, the upper-boundary case split and restriction
   transports. Their `uses` union is exactly `proof_deps`. The added three dependencies
   record the modules of the proved helpers actually used, rather than claiming use
   of their public theorem statements. Both original definition dependencies remain.
   No new node or unsupported proof step is present.

Second-reading changes: added this independent review and clarified that no baseline
module or node was pruned. No Lean or node repair was necessary. Closed one original
hole (`HomologicalComplex₂.verticalCutoff_endpoint_forks`), added zero holes, split off
zero statements; the public theorem has no dependency on an unfinished theorem.
