## What changed
Reduced `CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand`
to its localized pure-tensor calculation. Added a fully proved generic lemma
`CategoryTheory.homTensorSummandLocalized_ext` for maps into internal Hom from
one sheaf tensor. Its proof transposes the maps, uses the sheafification adjunction,
tests the presheaf tensor on pure tensors, and applies naturality under localized
restriction. The independent site universes are preserved using private, proved
presheaf tensor-Hom helpers patterned after HomTensorLocalizedExt.

Added HomTensorDifferentialSummandPure for the scalar calculation and imported both
new modules as proof-only imports in the assigned module. The assigned statement,
its universes and visibility are unchanged. No existing consumer is adapted.
The DAG now separates the calculation from the proved lifting step.
All three files compile through lcompile.py in import order.

## Proved and sorry left
Closed the original hole in
`CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_summand`
(lem-sc-hom-tensor-iterated-differential-summand) by reduction.
Proved `CategoryTheory.homTensorSummandLocalized_ext`
(lem-sc-hom-tensor-summand-localized-ext), including every private helper.
Added exactly one hole:
`CategoryTheory.homTensorDifferential_summand_pure`
(lem-sc-hom-tensor-differential-summand-pure).
This is a decomposition, not a net reduction in holes: one closed, one added.
There is no sorry in the assigned module or in the extensionality module.

The remaining statement only compares scalar values on localized pure tensors;
it does not assert equality on arbitrary sheaf tensor sections. Its docstring and
node spell out both Hom differential expansions, the d1 and d2 pure-tensor values,
the sign identity and the commuting subtractions. The sectionwise outer projection
formula was checked in a temporary compiler experiment. Negative degrees use the
same negOnePow addition identity; zero complexes, sections and differentials give
zero terms. No hypothesis of global pure-tensor generation is used.

## No longer needed
Removed the assigned module's direct imports of
Sheaf.Algebra.Homology.HomComplex and
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed.
The former remains a necessary underlying Hom-complex definition through
HomTensorDegreewise, so its node is not pruned.
The tensorClosed theorem (lem-pc-sheaf-modules-tensor-closed) is unnecessary for
this proof: the lifting lemma constructs the presheaf transposition and uses the
existing sheaf tensor comparison and adjunction directly. No new module imports
TensorClosed. The original degreewise, Hom-complex and total-tensor definitions
remain needed by the scalar calculation. No coproduct assembly node is introduced.
No claim is made that TensorClosed becomes unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong
The historical dedicated repair handoff in coord/returns/K4.md was read after
the first dry run refreshed the clone. Its rejected implementation is absent from
the restored baseline: neither HomTensorPureDifferentials nor HomTensorSummandPureExt
exists there. This delivery instead closes the baseline hole by the reduction above.
It contains no local irreducibility attribute on homTensorProjection and requires
no unsafe reducibility option. All three current modules compile well within the
60-second per-file limit (approximately 7, 19 and 7 seconds). The original assigned
signature is identical, and no consumer interface is changed. The previous rejection
of a proof-preserving repair as "nothing is proved" is avoided by actually closing
the original named hole; no repair-metadata exception is required. The second reader
can review these current files rather than the withdrawn three-file implementation.

No mathematical statement error found. The existing HomTensorLocalizedExt proves
extensionality for an entire total tensor term, whereas this item has already
restricted to one tensor summand. Its proved transposition argument was reused for
arbitrary tensor factors without the coproduct step. HomTensorDifferentialComponent
and HomTensorDifferential depend on this item, so importing either is circular.
The source .tex files are absent on this machine; the official Stacks pages for
Tags 0A90, 0A5Y and 03EO were read. LeanSearch returned Internal Server Error and
is recorded as unavailable. LeanFinder, Loogle and grep supplied external-cochain
formulas and the sign identity but no exact summand theorem.

## New nodes
lem-sc-hom-tensor-summand-localized-ext:
Sheaf.Algebra.Homology.HomTensorSummandLocalizedExt, a proved generic lifting
lemma for a single tensor, with no differential or total-complex assumptions.

lem-sc-hom-tensor-differential-summand-pure:
Sheaf.Algebra.Homology.HomTensorDifferentialSummandPure, the remaining localized
scalar computation, strictly the calculation part of the original argument.
Neither new node bypasses any realized unit step; the unit's realized lists are
empty. No existing signature or definition changed, so no change record is needed.

## Second reading by K4

1. Compared the assigned module with the repository version. The theorem signature,
   universes, visibility, and definitions are unchanged; only proof-only imports and
   the proof body differ. Verdict: pass.
2. Compiled all three delivered modules in import order with `lcompile.py`. The
   assigned theorem and `homTensorSummandLocalized_ext` have no `sorry`; the only
   remaining hole is the explicitly split `homTensorDifferential_summand_pure`,
   whose node, docstring, and statement match. No forbidden declarations or hollow
   definitions were found. Verdict: pass, with the documented decomposition.
3. Checked the two added statements against their declarations and edge cases
   (zero sections, zero differentials, and negative degrees). The extensionality
   statement is generic and the pure calculation is strictly the localized scalar
   reduction, so neither weakens the original target. Verdict: pass.
4. The proof uses the shortest available route: localized pure-tensor extensionality
   followed by the scalar reduction. Removed imports are proof-only and listed above;
   the original degreewise and hom-complex route remains in use. Verdict: pass.
5. The DAG nodes' declarations, statements, proof steps, dependencies, origins, and
   unit/chapter metadata agree with the Lean files. The unit's realized route is
   unchanged (empty realized lists). Verdict: pass.

Changed only this second-reading record; no Lean statements or definitions were
modified during review.
