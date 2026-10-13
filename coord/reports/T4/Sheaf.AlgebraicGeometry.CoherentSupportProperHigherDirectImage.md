## What changed

Proved `AlgebraicGeometry.isCoherent_schemeModuleHigherDirectImage_of_support_proper`
without changing its signature or public imports. Added proof imports for affine derived
cohomology, affine finite-presentation criteria, coherent affine sections, and the
classical/unbounded derived-functor comparison. Added two fully proved private helpers:
`qc_single` and `finitePresentation_of_quasicoherent_finiteType`.

The proof follows the existing support-factorization route. It constructs the heart
isomorphism identifying the derived closed-immersion pushforward with F in degree zero,
uses derived composition, and transports finite presentation from the proper classical
higher direct image. Updated the existing node's proof, proof dependencies, and origin.
Local compilation succeeds without warnings (11.3 seconds).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isCoherent_schemeModuleHigherDirectImage_of_support_proper`
(node `lem-pc-coherent-support-proper-higher-direct-image`).
No sorry remains in the delivered module, and no holes or new statements were added.
The proof uses the library's existing dependency declarations; this does not claim that
their entire transitive axiom closure is already sorry-free.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`.
Removed `lem-pc-affine-morphism-hi` as a direct proof dependency, replacing that step by
`lem-sc-affine-derived-cohomology`. The affine-vanishing node and module remain needed
transitively by that comparison, so no global pruning of them is claimed.
No other original node or module is made unnecessary. An experimental import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` was removed
from the final proof after compilation verified it was unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned proper-coherence declaration
uses classical natural-number higher direct images and requires a finite-presentation
instance for G. The proof supplies that instance on affine opens and explicitly bridges
the classical and unbounded definitions. Affine vanishing alone is replaced by the
existing affine derived-cohomology comparison to carry out the heart identification.
The blueprint unit's route is retained; its realized lists contain no node-level
constraint on this tool argument. No definitions, signatures, or other modules changed.

## Second reading by T4

1. Compared the entire module with the repository version. The existing theorem's
   signature is byte-for-byte identical, and every public import is unchanged.
   Only proof imports, fully proved private helpers, and the theorem proof were added.
   No definition, target, other module, or declaration visibility changed. Verdict: pass.
2. Independently compiled the delivered file with lcompile.py: exit 0, no warnings,
   11.3 seconds. Scanned the whole file: no sorry or prohibited declarations. Compiled
   a scratch copy with #print axioms for all three theorems. Both private helpers use
   only propext, Classical.choice, and Quot.sound. The main theorem additionally uses
   sorryAx through existing library dependencies, permitted while those remain open;
   no hole is introduced here. Checked the directions of the affine comparison,
   heart identification, composition, and classical/unbounded comparison isomorphisms.
   All terminate at exactly the stated higher direct image. Verdict: pass.
3. There are no split-off statements or new public statements, and no new nodes or
   change records. Both private helpers are fully proved. Searched lean/Sheaf and
   lean/WeilConjectures using finite-presentation/finite-type and single/quasi-coherent
   concepts: analogous helpers are private in other modules, not reusable public
   declarations. The finite-presentation argument uses actual affine sections and
   locality; the single-object argument handles zero cohomology in both directions.
   Checked p=0, F=0, and the identity closed immersion: none requires extra hypotheses.
   The local witnesses Z, G, and V are eliminated in a proof, not exported as a
   definition chosen from a mere existence theorem. Verdict: pass.
4. Read the existing dependency declarations and checked the proof from its conclusion
   back through proper coherence, derived composition, and support factorization.
   No shorter public theorem was found for this exact support-proper statement.
   Each added import supplies a named declaration actually used in the proof; all
   imports needed only for proofs are plain imports. The sole removed original
   proof dependency is lem-pc-affine-morphism-hi, explicitly recorded above; its
   module remains transitively needed. The unit sk-thm-picard-duality has empty
   realized statement/step lists, unchanged, and the support-factorization route
   continues to use the proper-coherence and derived-composition tools. Verdict: pass.
5. Compared the node JSON with the original: only proof, proof_deps, and proof_origin
   differ. The union of the proof-step uses equals proof_deps, and the three steps
   describe the Lean proof, including the finite-presentation and comparison steps.
   The statement, Lean signature record, chapter, unit, and blueprint are unchanged.
   Verdict: pass.

Second reading changed only this report: added the independent checks and explicit
axiom results. No Lean or node repairs were necessary. Closed 1 original hole;
added 0 holes; split off 0 statements. This is a proof from existing dependencies,
not a decomposition or a claim that the transitive library is already sorry-free.
