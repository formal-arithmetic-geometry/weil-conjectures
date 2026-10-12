## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affine_section_neighbourhood_of_finite`
in `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine` without changing its signature,
public imports, or definitions. Added proof-only imports of
`Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap` and
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.
Updated `lem-sc-ample-finite-principal-affine` proof, proof_deps and proof_origin to match.

The canonical section-ring morphism provides point primes and their nonvanishing dictionary.
The proof constructs the homogeneous ideal as the irrelevant ideal intersected with all point
primes outside the prescribed neighbourhood. A fully proved local calculation writes a section
of an ideal tensored with an invertible module using an affine free generator, and shows that
its image vanishes on the ideal support. Ample ideal sections then establish the noncontainment
hypotheses for graded prime avoidance. The final affine-intersection lemma supplies the open.

Validation: the module compiles locally without warnings. All added imports are used directly:
the canonical-map theorem and the invertibility comparison. The original five proof imports
are used. Empty E is handled by Fin 0 in the existing prime-avoidance theorem; empty Y and
arbitrary, possibly non-quasi-compact W are allowed. The local vanishing calculation also
handles the zero and unit ideal: for the unit ideal its support is empty; for the zero ideal
the image coefficient is zero. The unit statement and its route are unchanged.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Modules.exists_affine_section_neighbourhood_of_finite`
(node `lem-sc-ample-finite-principal-affine`).
No sorry remains in the delivered module. No holes added or split off; no new modules.
This is a proof from existing stated dependencies, some of which remain sorry in their own
modules, as intended in stage 3; it is not a claim of a sorry-free transitive axiom closure.

## No longer needed

None. Every original proof-dependency import and node is still used. The two initially
considered helper modules were scratch work and are not delivered: the existing canonical-map
statement supplied the point primes, and the ideal-tensor vanishing calculation was proved
inside the main proof. No existing module or node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The plan omitted the concrete Lean bridge from ideal-valued sections to vanishing on the
ideal support, and the point-prime dictionary. Both are now accounted for without new holes:
the former by a local proof using existing proved TensorSection lemmas, the latter by
`lem-sc-ample-proj-canonical-map`. The existing docstring's separate empty-E argument is not
needed by the implementation: graded prime avoidance already includes an empty family.
No mathematical statement was changed or disputed. The local invertibility comparison is the
already closed generic tool node `lem-pc-invertible-sheaf-instance`; this use does not replace
the curve-estimate unit route. Stacks Tag 09NV was read on its official online page because
the local literature/stacks-project tree is absent on this machine.

## Second reading by F2

1. **Visible declarations and statements.** Compared the delivered module with the repository
   version. The theorem signature is byte-for-byte unchanged; only the proof body and two
   proof-only imports were added. The DAG statement is unchanged and matches the Lean theorem.
   Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without errors or
   warnings. The delivered file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. An axiom print on the target reports only standard axioms together with
   `sorryAx` inherited from the still-open imported lemmas. Verdict: pass.

3. **Statements and dependencies.** No theorem was split off and no new statement was added.
   The proof uses the existing canonical-map, ideal-section, prime-avoidance, affine-cap,
   finite-affine, closed-subset, invertibility, section-ring, and tensor-product declarations;
   the node's `proof_deps` is exactly the union of the proof-step uses. A search found no
   existing shorter theorem for this result. Verdict: pass.

4. **Route and pruning.** The proof follows the node's five planned steps: choose an affine
   neighbourhood, construct point primes and the ideal, prove local vanishing on ideal support,
   apply ample ideal sections and graded prime avoidance, and finish with the affine-cap lemma.
   It handles empty finite sets through the existing avoidance theorem. No old dependency or
   import is unused, so nothing is pruned. Verdict: pass.

5. **DAG and unit agreement.** Updated node `proof`, `proof_deps`, and `proof_origin` describe
   the implementation exactly. The theorem's unit route remains represented by the existing
   unit realization; no unit statement or target was changed. Verdict: pass.

Changed in this second reading: appended this review record only; no Lean declarations or
statements were altered.
