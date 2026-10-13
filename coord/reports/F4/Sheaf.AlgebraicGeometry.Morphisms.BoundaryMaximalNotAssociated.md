## What changed
Replaced the sorry in `AlgebraicGeometry.Scheme.boundary_maximal_not_associated`
by a complete proof from the finite localized restriction detector. The private
algebraic lemma `no_maximal_associated_of_annihilator_zero` is proved using
Mathlib's Noetherian annihilator characterization. The target signature is unchanged.
The finite restriction-map construction is stated in the new module
`Sheaf.AlgebraicGeometry.Morphisms.BoundaryLocalizedFiniteDetector`.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.boundary_maximal_not_associated` (one original hole).
Added: `AlgebraicGeometry.Scheme.boundary_localized_finite_detector`, node
`stage3-boundary-localized-finite-detector` (one hole). This is a decomposition,
not a net reduction in holes. No sorry remains in the item's module.
The private algebraic helper is fully proved. The remaining statement supplies
finite restriction data and does not mention associated primes or their exclusion.
It also drops the finite-generation hypothesis; the Lean proof performs the
annihilator and associated-prime contradiction separately.

## No longer needed
Removed proof imports from the item: `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, and
`Mathlib.Algebra.Module.LocalizedModule.Exact`. These ingredients remain needed
for the new geometric node and are imported there; they are not globally pruned.
Node `lem-weil-pbc-associated-prime-submodule` is no longer needed by this route:
the localized submodule is included directly in the finite restriction maps.
No existing statement module for that Mathlib leaf is pruned.
The other old proof dependencies, `pqf-lem-pushforward-qcoh` and
`lem-weil-pbc-affine-module-basic-open-localization`, move to the detector node;
they remain in the import closure. Removed the redundant explicit public import
`Mathlib.Algebra.Category.ModuleCat.Basic` from the new module (its ModuleCat
interface is already supplied by the sheaf imports). No library module is pruned.

## Where the brief, the DAG or earlier work was wrong
The previous attempt abandoned the item without compiling a reduction.
The geometric construction is now a precise named statement, and the remaining
combination is kernel checked. The original finite-product plan is retained.
The unit's realized steps are unchanged. Edge cases: an empty cover gives the
zero module; S=0 gives zero detection immediately; the injective multiplier
condition is compatible with Q_i=0. No finite-type hypothesis on N is needed.

## New nodes
`stage3-boundary-localized-finite-detector`: the finite basic-open restriction
injection localized at p, with injective multipliers from the maximal ideal.
Source: Stacks Project Tags 0AVN and 01LC; proof dependencies are the existing
qcqs pushforward and affine basic-open localization nodes. No change records
or forced adaptations are needed.


## Second reading by F4
1. Compared the delivered item with the repository using `diff -u`: the existing
   declaration signature and docstring are byte for byte unchanged. Only the
   proof, a private proved helper, and proof imports change. No definitions,
   target statements, change records, or forced adaptations are introduced.
2. Compiled both modules locally in import order, without errors or warnings.
   The sole remaining `sorry` is the named public detector theorem, exactly
   `:= by sorry`; there are no prohibited declarations or hollow definitions.
   Explicit scratch `#print axioms` checks cover both public declarations and
   the private helper. The helper uses only standard axioms; the upper result
   additionally inherits `sorryAx` from the detector.
3. Read the detector statement, its full docstring argument, and its node
   against Stacks Tags 0AVN and 01LC. It is the finite restriction-map part of
   the original argument, not a renamed associated-prime exclusion. The scalar
   injectivity and joint zero detection are sufficient, and neither finite
   generation of S nor finite type of N is needed for their construction.
   Empty U (or empty U intersect V) gives n=0 and S_p=0; S=0 and Q_i=0 cause
   no obstruction; U=top admits no boundary point. New leanfinder, loogle and
   grep searches with different queries found localization injectivity and
   finite basic-open cover ingredients, but no existing detector theorem.
   Also searched repository and upstream module sources. Completing the
   remaining geometry requires the finite-cover, restriction and localization
   construction; it is not a hole that closes by a short existing lemma.
   No data definition chooses witnesses from this existence theorem: witnesses
   are eliminated only inside the upper proposition's proof.
4. Checked the top-down algebraic proof and all old proof dependencies. Direct
   use of the annihilator characterization avoids the old associated-prime
   submodule detour. The other two dependencies remain below the detector.
   All imports serve signatures or the geometric proof plan; proof-only imports
   are plain imports. The finite-product route is retained. The unit record
   sk-prop-input-spreading has empty realized arrays in the baseline; this item
   is not a realization entry and changes no unit step or unit dependency.
5. Compared both node records with the Lean statements. The existing node's
   mathematical statement and statement dependencies are unchanged; its proof
   and proof_deps now describe the detector followed by the annihilator
   contradiction. The new node has the matching verbatim Lean signature,
   source, proof, searches, provenance, chapter and unit. Its proof_deps are
   the union of its step uses. Verdict: acceptable one-for-one decomposition,
   with no net reduction in holes and no globally pruned modules.

Second-reading changes: removed the redundant explicit ModuleCat.Basic import
from the new module, used the conventional mapsto lambda in the private proof,
removed the unused finite-generation statement dependency from the new node,
and made the report's dependency relocation and pruning claims explicit. The
mathematical statements and proof route were retained.
