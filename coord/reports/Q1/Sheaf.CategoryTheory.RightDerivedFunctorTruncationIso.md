## What changed

Proved both remaining holes in `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`:
`CategoryTheory.Functor.mono_homologyFunctor_rightDerivedFunctorPlus_map` and
`CategoryTheory.Functor.epi_homologyFunctor_rightDerivedFunctorPlus_map`.
A proved private helper `isGE_cone_of_homology_map` supplies the common cone calculation.
The proof uses Mathlib's long exact sequence, the existing triangulated structure on the
right derived functor, and its proved negative-vanishing theorem. Updated the mono and epi
nodes' proof records to describe those dependencies. Existing public signatures and imports
are unchanged. No new modules, definitions, axioms, or deferred statements.

Read Stacks `derived.tex`, `lemma-negative-vanishing` (05TC), especially its proof of (2),
from the local literature mirror. Read the proper-base-change unit and its `realized` record;
its route is unchanged. The arbitrary-map extension uses the same argument with a cone.

## Proved and sorry left

Closed 2 of 2 existing holes, with 0 holes added:

- `CategoryTheory.Functor.mono_homologyFunctor_rightDerivedFunctorPlus_map`
  (`lem-weil-pbc-derived-functor-truncation-iso-mono`).
- `CategoryTheory.Functor.epi_homologyFunctor_rightDerivedFunctorPlus_map`
  (`lem-weil-pbc-derived-functor-truncation-iso-epi`).

No `sorry` remains in this module or is introduced elsewhere. The already-proved isomorphism
and truncation declarations retain their proofs. Local single-file compilation succeeds
without warnings. The delivery dry run checks the axioms of all declarations.

The cone calculation covers every integer degree, including the boundary `i = n` where
`hmono` is essential, and the zero objects/map case. It uses no upper boundedness assumption.
The derived mono proof uses degree `j - 1`; the epi proof uses degree `j`.

## No longer needed

No imports or modules were removed: both existing proof imports are used, and the public
imports supply the statement's derived-functor and category hypotheses.
The mono and epi nodes no longer cite their parent isomorphism theorem as a proof dependency;
they now prove their halves independently from the cone sequence and negative vanishing.
The parent node remains needed for the combined isomorphism and truncation statements.
No other nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The mono/epi proof records previously cited the parent isomorphism result, although the parent
proof applies these two halves. Replaced those circular proof plans by the actual cone
argument. The existing short statement summaries still refer to the parent for their
hypotheses; no statements or statement dependencies were changed.

## Second reading by Q1

1. Compared the delivered module with the repository version. Existing public theorem signatures and definitions are byte-for-byte unchanged; only proofs, explanatory docstrings, and the private helper were added.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The delivery checks axioms for all declarations.
3. Checked the two split-off node statements against the Lean declarations and the cone argument. Both are true, have unchanged strength, and are needed strictly as the mono and epi halves; no duplicate library theorem was found.
4. Checked the proof route from the top downward. The helper uses the distinguished cone triangle and the long exact sequence; the two halves use triangulatedness and negative vanishing. The proper-base-change unit route and realized nodes remain in use. No imports can be removed.
5. Updated both split node proof records to match the actual cone proof and removed the circular parent-isomorphism dependency. The parent node remains the route for the combined isomorphism and truncation results.

Changed in this reading: added this review record and verified the proof/dependency metadata; no Lean statements or definitions were changed.
