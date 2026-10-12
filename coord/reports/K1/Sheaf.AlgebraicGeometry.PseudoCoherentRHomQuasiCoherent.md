## What changed

Closed `AlgebraicGeometry.pseudoCoherentRHomQuasiCoherent` without changing its signature
or any existing definition. Reused the pseudo-coherent clause of
`AlgebraicGeometry.rhom_supported_quasiCoherent`, rather than repeating its affine argument.
The underlying-object comparison `derivedRHomAlgebraModule_underlying` transports its
quasi-coherence to the algebra-valued derived Hom after scalar restriction.

Added two **proved** reusable lemmas, one per new module:

- `DerivedLocallyBoundedBelowGlobal.lean`: compactness gives a finite neighbourhood subcover;
  finite induction gives a common lower bound; section extensionality makes every lower
  cohomology sheaf zero. `DerivedCategory.isGE_iff` yields the uniform bound.
- `DerivedAlgebraQCohOfUnderlying.lean`: compute homology on the canonical Q-preimage and
  use exact restriction's `mapHomologyIso` and the derived factorization isomorphisms.
  Transport quasi-coherence and reflect zero cohomology by evaluating the identity equation.

Updated the original node's proof, proof dependencies and proof origin to this route.
No forced adaptations or signature/definition changes. All three modules compile without
warnings; all delivered proofs contain no `sorry`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.pseudoCoherentRHomQuasiCoherent`
(node `lem-sc-pseudo-coherent-rhom-qcoherent`).

Also proved `AlgebraicGeometry.derivedLocallyBoundedBelowGlobal`
(node `lem-sc-derived-locally-bounded-below-global`) and
`AlgebraicGeometry.derivedAlgebraQCohOfUnderlying`
(node `lem-sc-derived-algebra-qcoh-of-underlying`).

No holes remain in any delivered declaration. No holes added or split off.
The proof uses already stated theorems with existing holes, including
`rhom_supported_quasiCoherent`, `derivedRHomAlgebraModule_underlying`, and the exact-scalar
preservation instances of `DerivedRHomAlgebraModule`; this is a proof from existing DAG
statements, not a claim that its transitive axioms have already been closed.

## No longer needed

Removed the following **direct** proof imports and corresponding direct proof dependencies:

- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
  (`lem-sc-derived-open-restriction-adjunction-exact`).
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`
  (`lem-sc-affine-pseudo-coherent-rhom-qcoherent`).
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (`lem-pc-affine-qcoh-derived-equivalence`).
- `Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra`
  (`def-pc-derived-category-qcoh-algebra`); still supplied by a public statement dependency.
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).

The item's proof also no longer directly uses
`lem-weil-pbc-spec-module-tilde-sections` or the unfolding of
`def-pur-pseudo-coherent-complex`; pseudo-coherence is passed to the existing RHom lemma.
All these nodes remain needed transitively or for statements. Comparing import closures
found **no whole modules pruned**. The replacement RHom theorem imports its own affine and
perfect-complex dependencies; no claim is made that removing redundant direct imports
eliminates those modules from the target closure. No existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

The original plan's two local-affine steps are already contained in the pseudo-coherent
clause of `rhom_supported_quasiCoherent`. Its locality assertion still needs a genuine
compactness argument to supply the uniform bound; this delivery supplies that proof.

The unit `sk-thm-picard-duality` has empty realized statement and step arrays. Its fixed
statement and route were not changed. The reused general RHom assertion is a tool for the
same Stacks 0A6H step, not a replacement for a realized unit statement or step.

Edge cases: the common-bound induction starts with zero on an empty subcover, so empty
schemes are covered. Neither helper assumes nonzero algebra, nonempty scheme, a chosen
noncanonical witness, or extra quasi-coherence/local-derived-category hypotheses. The
scalar lemma uses the canonical Q-preimage representative and its specified isomorphism,
not an arbitrary witness selected from an unproved existence theorem.

Sources checked: [Stacks 0A6H](https://stacks.math.columbia.edu/tag/0A6H) states local
boundedness for a general scheme, and [Stacks 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
identifies the underlying derived internal Hom. The compactness and exact-cohomology
arguments use Mathlib declarations inspected in their sources. Literature files are not
present in this remote clone, so the cited official Stacks pages were read directly.

## New nodes

`lem-sc-derived-locally-bounded-below-global` records the fully proved finite-cover bound
lemma, independent of internal Hom and pseudo-coherence, in
`Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal`.

`lem-sc-derived-algebra-qcoh-of-underlying` records the fully proved exact scalar-restriction
criterion for arbitrary algebra-derived objects, independent of pseudo-coherence and
Noetherianity, in `Sheaf.AlgebraicGeometry.DerivedAlgebraQCohOfUnderlying`.

## Second reading by K1

1. Compared the main module with the repository. Existing signatures and definitions are
   byte-for-byte unchanged; only proof imports and the proof body changed. The two new
   helper modules and nodes are declared in this report. Verdict: pass.
2. All three files compile without warnings via `lcompile.py --all`; source inspection
   found no holes or prohibited declarations. The main theorem's printed axioms are
   propext, Classical.choice, Quot.sound and sorryAx from existing dependencies.
   The global-bound helper has only the three permitted axioms; the scalar helper also
   uses sorryAx from existing scalar exactness instances. Verdict: pass, conditional on
   the already-open imported proofs.
3. Both helper statements are strictly simpler parts of the argument, with complete
   proofs and matching nodes. Empty-cover and zero-algebra cases are valid. The canonical
   Q-preimage is used with its specified isomorphism. Searches found no duplicate helper
   declaration. No statements were split off with sorry. Verdict: pass.
4. The parent reuses the existing RHom theorem, then proves the finite-cover and scalar
   steps. The unit route is preserved. Every removed old proof dependency is recorded
   under No longer needed; no whole module is pruned. Verdict: pass.
5. Checked proof steps, proof_deps, proof_origin and Lean records of all three nodes
   against the code. The unit record is unchanged. Verdict: pass.

Second reading changed no Lean code or nodes; appended this independent review.
