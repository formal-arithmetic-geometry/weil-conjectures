## What changed

Closed the proof of
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyTheta_isIso_of_acyclic`
without changing its statement, universe, visibility, or public imports.
Added two non-public proof imports: `SectionAcyclicIncomingKernelImage` and
`ShortComplexSectionComparison`, both under `Sheaf.AlgebraicGeometry`.
The target proof obtains the incoming kernel/image acyclicity, specializes it to
cohomological degree one, and applies the arbitrary-short-complex comparison to `K.sc p`.
Its normalized sheafification/adjunction expression agrees definitionally with theta.

The new dimension-shifting module is proved, including its private helper lemmas.
It constructs the two short exact sequences using kernel/cokernel universal properties,
uses the existing full long exact sequence of right-derived functors, and inducts from
the zero incoming boundary. The incoming kernel in degree zero is `K.X 0`, rather than
an incorrectly presumed negative-degree term. Dependent kernel/image transports use
explicit isomorphisms. Restriction exactness comes from the proved source instance
`preservesLimitsOfSize_restrictFunctor` and the restriction adjunction.

All three delivered modules compile together without errors or warnings, under the
normal heartbeat limits. No library build, statement adaptation, or arbitrary-witness
construction was made. New-node searches used LeanFinder, Loogle, and grep; LeanSearch
returned an Internal Server Error and is recorded as unavailable. Blueprint searches
for `section-acyclic` and `short complex section` found no matching blueprint nodes.
The unit record `sk-thm-p1` was checked: this change stays below its realized steps.

## Proved and sorry left

Closed one of the item's one original holes:
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyTheta_isIso_of_acyclic`
(node `lem-pc-section-cohomology-theta-acyclic`). No sorry remains in the item.

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.section_acyclic_incoming_kernel_image`
(node `lem-pc-section-acyclic-incoming-kernel-image`); its module has no sorry.
Its private boundary-sequence, outgoing-sequence and cohomology closure helpers are proved.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.shortComplex_sectionComparison_isIso`
(node `lem-pc-short-complex-section-comparison`), in
`lean/Sheaf/AlgebraicGeometry/ShortComplexSectionComparison.lean`.
Its proof is exactly `by sorry`, with the full proof in the docstring and node.
It concerns an arbitrary short complex and assumes only first-cohomology vanishing of
two incoming objects. It does not repeat the original nonnegative-complex assertion or
its term/homology acyclicity assumptions. Its remaining work is the initial long exact
sequence, the resulting two surjections on sections, and identification of that
cokernel comparison with the explicitly normalized sheafification adjoint.

This is a decomposition of the original hole, with one hole closed and one added;
no net reduction in hole count is claimed. The dimension-shifting part is complete.
Existing dependencies can themselves reach existing sorries; none of those declarations
is changed or copied into this delivery.

## No longer needed

The second reader removed the redundant new-helper imports
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` from
`SectionAcyclicIncomingKernelImage` and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` from
`ShortComplexSectionComparison`; their interfaces already come through the remaining
public imports. The reduced modules compile cleanly.

No existing import was removed: the item's original public import
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices` is required by its statement.
The new helper modules use smaller direct statement imports, rather than importing
FlatBaseChangeOpenChoices.

The following planned dependencies and their modules are not needed by this proof and
are removed from this item's DAG proof dependencies:

- `thm-sp-if-e1`: `Sheaf.CategoryTheory.HypercohomologyFirstPage`.
- `thm-sp-truncation-e2`: `Sheaf.CategoryTheory.TruncationHypercohomology`.
- `lem-sp-cartan-eilenberg-total-resolution`:
  `Sheaf.CategoryTheory.CartanEilenbergTotalResolution`.
- `lem-weil-pbc-ce-resolution-all-lower-bounds`:
  `Sheaf.CategoryTheory.CartanEilenbergAllLowerBounds`.

Their imports were absent in the original item, and are not added. This is pruning of
this proof's planned route; no claim is made that these modules are globally unreached.
No realized unit statement or unit proof step is bypassed or modified.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement was found. The DAG's spectral-sequence route is
valid but unnecessarily broad here. Its generic interfaces use integer-indexed derived
category models, whereas the required local calculation can be obtained by dimension
shifting and two short exact sequences. The original item did not actually import its
listed proof-dependency modules; its header had only the public statement import.
The replacement DAG route records the dependencies actually used.

A Lean interface detail matters for the new local comparison: its arbitrary short complex
is typed directly over `SheafOfModules Y.ringCatSheaf`. Typing it over the definition
`Y.Modules` led to a category-instance mismatch in `ShortComplex.map` instance synthesis.
The direct type converts to `K.sc p` without any change to the item's signature.

## New nodes

`lem-pc-section-acyclic-incoming-kernel-image`:
`lean/Sheaf/AlgebraicGeometry/SectionAcyclicIncomingKernelImage.lean`.
This is the proved dimension-shifting part, sourced to Stacks Tag 015B applied to the
cycle/boundary sequences. Its statement includes every positive cohomological degree,
all incoming differentials, and the degree-zero kernel convention.

`lem-pc-short-complex-section-comparison`:
`lean/Sheaf/AlgebraicGeometry/ShortComplexSectionComparison.lean`.
This is the one remaining local comparison, sourced to Tags 015B and 01E4.
Its two first-cohomology hypotheses yield the boundary and homology surjections needed
for exactness of the particular section homology computation. No affineness,
quasi-coherence, resolution, or boundedness is assumed. The displayed morphism is
specified by the sheafification homology comparison, counit and adjunction.

Both nodes carry actual search records, complete proofs in words, Lean signatures,
and ancestry through the original section-theta node. No change records are necessary:
no existing definition, statement, or public interface was changed.


## Second reading by T2

1. Compared the existing module and its node with the repository using `diff`.
   The sole existing theorem signature is byte for byte identical; universe,
   visibility, definitions and the original public import are unchanged.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   There are no adaptations or change records. Verdict: pass.
2. Read all three modules and the private helper proofs, compiled the full sandbox
   in import order with `lcompile.py`, and scanned for forbidden declarations and
   holes. Exactly one `sorry` remains, the complete proof of the reported public
   theorem `shortComplex_sectionComparison_isIso`. No definition is hollow.
   Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
   for `section_acyclic_incoming_kernel_image`, and additionally `sorryAx` for the
   comparison and the original theta theorem. Thus theta is reduced, not yet proved
   without holes. The kernel/image constructions use actual universal maps; the
   long-exact-sequence witnesses are used only inside proofs. Verdict: pass.
3. Checked the new statements against their docstrings and Lean signatures.
   The first is the induction on the two cycle/boundary sequences, with the correct
   degree-zero incoming kernel K.X 0. The remaining local comparison requires exactly
   the two section-surjectivity consequences of first-cohomology vanishing. For f = 0
   its image is zero; for g = 0 the same quotient calculation applies; the empty open
   and zero complex give zero sections. The sheafification/counit adjoint is the
   cocycle-class map, not an arbitrary isomorphism. It is a strictly smaller part of
   the argument, not the original theorem under another name. Independent LeanFinder
   search for a left exact functor commuting with homology under boundary/kernel
   first-derived vanishing found only global exact-functor preservation lemmas.
   Qualified Loogle queries found no matching local criterion. Independent `rg`
   searches of Mathlib short complexes, upstream scheme modules and `lean/Sheaf`
   found no duplicate; `moduleSectionBoundary_eq_zero_iff` is useful for the first
   step but does not identify the displayed homology comparison. Closing that
   comparison needs a substantial normalization proof, not a short existing-lemma
   application. Both nodes have complete proofs in words and search records.
   Verdict: pass; retain one split-off hole, with no net hole reduction claimed.
4. Checked the top-down reduction and definitional normalization against
   `sectionCohomologyTheta` and `sectionCohomologyComparison`. The actual target proof
   supplies the two degree-one hypotheses from the proved induction and applies
   the comparison to K.sc p; the compiler verifies the displayed map agrees.
   All four discarded old proof dependencies are listed in `No longer needed`.
   Read `dag/units/sk-thm-p1.json`: neither this node nor the discarded spectral
   sequence helpers realizes a fixed unit step. No unit record is changed.
   Removed two redundant imports from the new modules and recompiled successfully.
   Remaining public imports provide statement types/definitions; both new imports
   in the original module and the dimension-shifting proof imports are non-public.
   Verdict: pass.
5. Checked both new node records, including their self-contained statements,
   exact Lean signatures, source, ancestry, chapter/unit, creation and searches.
   Their proof dependency is the existing full right-derived long exact sequence.
   The original node's two steps and dependencies now match its actual proof.
   Degree-zero and positive-degree transports in the proved helper match its node.
   Verdict: pass.

Second reading changed only the two redundant new-helper imports and this report.
The original docstring still gives a valid spectral-sequence argument; the actual
Lean proof and DAG now use the shorter dimension-shifting route described above.
No additional holes were closed or added by this reading.
