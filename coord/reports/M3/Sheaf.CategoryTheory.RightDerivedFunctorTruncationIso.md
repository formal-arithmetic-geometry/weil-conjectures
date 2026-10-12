## What changed
Added the proof of `isIso_homologyFunctor_rightDerivedFunctorPlus_map` by combining separately stated monomorphism and epimorphism halves. The truncation corollary remains unchanged. The two halves are new public intermediate declarations in the same module.

## Proved and sorry left
Proved `isIso_homologyFunctor_rightDerivedFunctorPlus_map` from the two intermediate halves. Sorries remain in `mono_homologyFunctor_rightDerivedFunctorPlus_map` and `epi_homologyFunctor_rightDerivedFunctorPlus_map`, with nodes `lem-weil-pbc-derived-functor-truncation-iso-mono` and `lem-weil-pbc-derived-functor-truncation-iso-epi`. The original `isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι` theorem remains sorry.

## Earlier second reading (a previous round; superseded)
The decomposition preserves the original statement and unit route; the two intermediate conclusions are strictly weaker than the target.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The full cone and long exact sequence argument is not implemented in the available time; it was decomposed into its monomorphism and epimorphism components, which are strictly weaker conclusions.

## New nodes
`lem-weil-pbc-derived-functor-truncation-iso-mono` and `lem-weil-pbc-derived-functor-truncation-iso-epi` record the two intermediate holes.

## Second reading by M3
1. Compared the delivered module with the repository version. The existing theorem
   signatures and definitions are unchanged; only the two named intermediate declarations
   and the proof of the original isomorphism theorem were added.
2. Compiled the module with `lcompile.py`. The only remaining `sorry`s are the two named
   split declarations and the pre-existing truncation corollary; no forbidden declarations
   or hollow definitions were introduced.
3. Checked the split statements against the parent hypotheses and the Stacks Lemma 05TC
   cone argument. Each conclusion is a genuine strictly weaker mono or epi half, and the
   nodes provide their sources and proof plans. No existing Mathlib or Sheaf declaration
   duplicates them.
4. The isomorphism proof uses both split halves and `isIso_of_mono_of_epi`; imports are all
   still used by the module, so no pruning is available. The unit route through the parent
   truncation-isomorphism node is retained.
5. The DAG node declarations match the Lean names and signatures; the parent node remains
   unchanged. The remaining truncation theorem is reported as an inherited open hole.

Changed only the report by adding this second-reading record; no Lean statements or imports
were altered.
