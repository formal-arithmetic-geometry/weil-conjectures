## What changed

Proved `AlgebraicGeometry.Scheme.punctured_principal_restriction_kernel` without changing its signature. Added two proved modules, `PrincipalThickeningLocalDivision` and `PrincipalSectionStableAnnihilator`, and proof-only imports of these and `DepthTwoPunctureGlobalSections`. The private helper `bounded_local_division_gluing` glues corrected local coefficients. Updated the item node to the actual proof.

The proof chooses a uniform annihilator bound c, takes m=n+c, obtains local divisors of the restricted difference, multiplies them by g^c to remove ambiguity, glues, and applies canonical Hartogs to lift the divisor to R. Both new public inputs are proved: local divisibility uses `quotientBaseChange_closedImmersion_ideal`; uniform annihilator stabilization is proved directly from Mathlib ACC, localization, a finite affine cover, and sheaf separatedness.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Scheme.punctured_principal_restriction_kernel` (lem-sbc-punctured-principal-restriction-kernel).

Also proved `AlgebraicGeometry.Scheme.principal_thickening_local_division` (lem-sbc-principal-thickening-local-division) and `AlgebraicGeometry.Scheme.exists_principal_section_stable_annihilator` (lem-sbc-principal-section-stable-annihilator). No `sorry` remains in any delivered module; zero new holes. All three modules compile together without warnings using lcompile.py. This closes the item from existing library declarations; it does not claim that all transitive library dependencies are axiom-free.

## No longer needed

No original import is removed: the two public imports supply the unchanged statement. No existing node or module becomes unnecessary as a whole; the original definition dependencies remain statement dependencies. The derived complexes, derived global sections, pro-zero cohomology kernels and depth-three H^1 vanishing in the previous proof plan are unnecessary for this kernel assertion. They had no separate stated nodes here. The proof needs only depth-two Hartogs; the original depth-three signature and maximal-ideal hypothesis are preserved.

Removed exploratory imports of `Mathlib.RingTheory.Noetherian.Basic`, `Mathlib.RingTheory.Localization.Basic`, and `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` from the newly written files: the retained imports already expose the APIs used.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The old plan was longer than necessary: multiplying local divisors by a uniform torsion-annihilating power gives a direct gluing proof of the kernel claim. This is below the unit level. `sk-prop-input-spreading` and its route are unchanged. The original theorem docstring still records the alternative derived proof; the node records the delivered direct proof.

Edge cases checked in the proof: empty opens and schemes are handled by sheaf locality and empty finite covers; g=0 and nilpotent g are covered by annihilator stabilization; units are allowed in the general intermediate lemmas; no regularity of g, reducedness, domain, or completeness is assumed.

The generic existing theorem `lem-weil-pbc-quotient-base-change-closed-immersion-ideal` is used as a tool for the local quotient computation, not as a replacement of any unit step. LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source grep were performed and their actual results are recorded. Blueprint searches for principal quotient, local division, annihilator, and 01YB found no matching blueprint nodes. The Stacks source pages 01YB, 0H3E, and 01QQ were read online because this checkout has no regenerated literature text.

## New nodes

`lem-sbc-principal-thickening-local-division`: the geometric quotient-kernel input for arbitrary commutative R and arbitrary open W, without depth or local-ring hypotheses. It is proved from the existing quotient base-change theorem and principal-ideal identities. Module: `Sheaf.AlgebraicGeometry.Morphisms.PrincipalThickeningLocalDivision`.

`lem-sbc-principal-section-stable-annihilator`: uniform annihilation of all local principal power torsion on an arbitrary Noetherian scheme. Its proof establishes ring stabilization, transport through localization, a finite affine maximum, and sheaf locality. Module: `Sheaf.AlgebraicGeometry.PrincipalSectionStableAnnihilator`.

No statement or definition changed, and no change record or forced adaptation is needed.

## Second reading by T4

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof text and proof-only imports were added. The two new declarations are recorded as split nodes with matching statements.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no `sorry`, forbidden declarations, or hollow definitions. The two new declarations use only `propext`, `Classical.choice`, and `Quot.sound`; the target's remaining `sorryAx` comes from its pre-existing imported dependencies.

3. Checked the split statements against their edge cases and sources. Principal local division follows the quotient-base-change ideal formula, and the stable-annihilator statement is the Noetherian ACC assertion transported through localization and sheaf locality. Both are strictly simpler than the target and have complete proof docstrings and DAG nodes; no duplicate library theorem was found.

4. Read the proofs from the target downward. The route uses the existing depth-two Hartogs bijection, the two new inputs, and direct sheaf gluing; it preserves the unit route and avoids the unused derived-comparison plan. Imports used by proofs are plain imports, and exploratory imports were removed as reported above.

5. Verified that each node's Lean statement, proof steps, dependencies, and proof origin match the delivered code. No statement or definition change, forced adaptation, or additional change record is required.

Changed after review: appended this second-reading record only; Lean sources and DAG content required no repair.
