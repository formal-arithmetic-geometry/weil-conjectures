## What changed

Replaced the sole sorry of `Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison`
without changing its signature, visibility, or public imports. Added two proof-only imports:
`Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology` and
`Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv`.

The connecting proof chooses an injective resolution, obtains additivity of the canonical
invariants composite from the given natural isomorphism, constructs the discrete topological
representation on E(F) directly, and applies Mathlib's `InjectiveResolution.isoRightDerivedObj`.
`NatIso.mapHomologicalComplex` transports the given natural isomorphism to the resolution;
applying homology gives a categorical isomorphism and hence an additive type equivalence.
This is composed with the same-universe resolution comparison and coefficient transport.
No data is chosen from a new unproved existence statement: the topological representation is
constructed, and the injective resolution is the existing Mathlib resolution interface.

Proved the new cross-universe coefficient comparison entirely from Mathlib. Its private helpers
recursively construct continuous equivariant linear equivalences of coinduced representations,
restrict to homogeneous invariants, and verify the differential by induction. An explicit
kernel equivalence identifies the boundary ranges, and `Submodule.Quotient.equiv` descends to
homology across universes. Concrete TopModuleCat kernel/cokernel data identifies these quotients
with categorical homology. Integer module instances are reconciled using `int_smul_eq_zsmul`.
Every private helper is proved or constructed without sorry.

Validation: all three modules compile together with lcompile.py, without warnings. The proof
covers degree zero as well: off-shape differentials, including the incoming degree-zero map,
are zero. The coefficient proof needs no compactness or joint continuity hypothesis. The
resolution statement retains compactness, Hausdorffness, total disconnectedness, arbitrary
integer coefficients, and representation universe at least the group universe. Trivial groups,
zero coefficients, degree zero, and different coefficient universes introduce no exception.

## Proved and sorry left

Closed the original hole:
`Rep.nonempty_equiv_rightDerived_continuousCohomology`
(node `lem-sc-discrete-invariants-continuous-comparison`). Its module has no sorry left.

Proved the newly added theorem:
`Rep.nonempty_equiv_continuousCohomology_coefficients`
(node `lem-sc-continuous-cohomology-coefficient-equiv`). Its module has no sorry.

Added one remaining hole, exactly the whole proof of the public theorem:
`Rep.nonempty_equiv_invariantResolution_continuousCohomology`
(node `lem-sc-discrete-resolution-continuous-cohomology`). This computes the homology of the
canonical invariant complex of a supplied injective resolution in a single coefficient
universe. It has no arbitrary Gamma, no natural isomorphism eta, no rightDerived expression,
no separate target coefficient universe, and no global injective-resolution existence
assumption. The resolution transport and arbitrary Gamma comparison are proved in the parent;
the coefficient universe comparison is independently proved. This delivery is a decomposition:
one original hole closed and one lower hole added, net zero holes, with the coefficient
transport and all connecting Lean code now complete.

## No longer needed

No original public import was removed: each supplies the unchanged statement or its instances.
No modules are claimed pruned from the targets' closure.

The parent no longer directly needs `lem-weil-pbc-effaceable-delta-functor-universal` or
`lem-weil-pbc-right-derived-universal-delta-functor`. These now belong to the proof dependencies
of `lem-sc-discrete-resolution-continuous-cohomology`, so they are not globally pruned.
`def-exc-discrete-modules-category` likewise remains a statement dependency and an analytic
comparison dependency. The parent proof dependencies now list the two new lemmas and the
Mathlib resolution/right-derived interfaces it actually uses.

The new coefficient theorem does not need the homogeneous/inhomogeneous change of variables,
profinite assumptions, discrete coinduced effacement, or delta-functor universality. It follows
directly from the recursive homogeneous complex and algebraic kernel modulo image.
Mathlib's continuous-cohomology Functoriality module was read but is not imported: its
categorical cochain maps require a common coefficient universe, whereas this proof works
on continuous intertwining maps and subquotients across universes.

## Where the brief, the DAG or earlier work was wrong

The existing `Rep.continuousCochains_derived_invariants` and its related exactness/effacement
interfaces require `[Finite A]` for the scalar ring. They cannot be specialized to integers.
This is a signature mismatch, not an obstacle caused by their remaining sorries. Adapting the
whole finite-ring interface would exceed this item and force unrelated changes, so the new
resolution comparison explicitly states the needed integer-coefficient result.

Stacks Section 0DVG (`section-continuous-group-cohomology`, read in the local literature copy)
asserts that the profinite comparison is known and leaves a future reference, rather than
providing its proof. The existing item's docstring supplies the effacement argument; that
argument is preserved in the new unresolved theorem and node, with proof_origin marked worker.
No existing statement or definition is corrected or weakened. The unit `sk-thm-br` is unchanged;
the new steps remain below its existing field-cohomology comparison route.

Mathlib search was run through msearch.py: LeanFinder and grep found the continuous cohomology
construction and same-universe functoriality, but no exact profinite resolution comparison or
cross-universe coefficient result. LeanSearch returned an HTTP Internal Server Error and is
recorded as unavailable. Blueprint searches for homogeneous cochains and injective resolution
continuous had zero matches; the broader continuous-cohomology matches describe finite-ring
cohomology or unrelated cohomological-dimension results.

## New nodes

`lem-sc-discrete-resolution-continuous-cohomology` is in
`dag/nodes/sec-curve-estimates/lem-sc-discrete-resolution-continuous-cohomology.json`, with
module `Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology`. It isolates the
remaining same-universe profinite computation for a supplied injective resolution, with its
source, complete proof sketch, searches, and inherited blueprint ancestry. This is the only
new sorry.

`lem-sc-continuous-cohomology-coefficient-equiv` is in
`dag/nodes/sec-curve-estimates/lem-sc-continuous-cohomology-coefficient-equiv.json`, with
module `Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv`. It states the proved
transport of homogeneous continuous cohomology under an equivariant integer-linear equivalence
of discrete coefficients across universes. It introduces no new hole.

No change records or forced adaptations are necessary: no existing signature, definition,
visibility, or public-import interface changes.

## Second reading by P3

1. PASS: diffed the existing module against the repository. Its theorem signature is
   byte-for-byte identical, as are its docstring, visibility, and existing public imports.
   Only its proof and two plain proof imports change. The other two modules are new;
   no existing definition, hypothesis, conclusion, or target changes. No change record
   or forced adaptation is required.
2. PASS: independently compiled all three modules together with lcompile.py, without
   errors or warnings. Scanned all delivered Lean files for forbidden declarations and
   holes: the only sorry is the whole proof of the named resolution theorem. Explicit
   scratch-copy #print axioms checks show only propext, Classical.choice and Quot.sound
   for the coefficient theorem; the parent and resolution theorem additionally show
   sorryAx, as expected from the declared remaining hole. Read every private helper: the
   recursive representation maps, kernel restriction, range equality, and quotient
   equivalence are real constructions. The parent constructs M directly; the supplied
   Mathlib injective resolution is used to compute homology, not as arbitrary new data
   chosen from an unproved existence lemma.
3. PASS: the remaining resolution theorem is a genuine smaller part of the argument:
   it fixes the invariant functor, supplies the resolution, and stays in one coefficient
   universe. The parent proves natural-isomorphism transport and composes the separately
   proved universe comparison. Checked degree zero (incoming differential is zero), the
   trivial group (only degree-zero invariants survive), zero coefficients, and arbitrary
   integer coefficients. Compactness and discreteness justify finite-image lifts and
   uniform local constancy of the contraction; the coinduced module has open stabilizers.
   The written effacement and homogeneous/inhomogeneous argument proves the claimed
   resolution comparison without a finite-ring assumption. Independent LeanFinder and
   grep searches using injective-resolution/fixed-point terminology found no exact
   existing comparison. Loogle returned unknown identifier InjectiveResolution, hence
   supplied no useful result. Read the existing finite-ring comparison and homotopy
   interfaces; their Finite A assumptions prevent specialization to integers. The
   remaining result requires substantial new formalization, not a short missing tactic.
4. PASS: read the proof from its target down through both new modules. No shorter
   available route found. The coefficient proof directly compares the existing recursive
   homogeneous complexes and concrete homology quotients across universes. Imports
   provide the public statement types/instances or are plain proof imports. Compared
   old and new proof_deps: the report accounts for the two universality nodes and the
   discrete-representation definition no longer directly used by the parent. They stay
   below the unresolved resolution node; no global pruning is claimed. The sk-thm-br
   unit and its realized field remain unchanged; all work is below its field-cohomology
   route. This is one hole closed and one added, net zero, not a completed comparison.
5. PASS: checked all three node records against the Lean signatures and proof bodies,
   including proof_deps equal to the union of proof-step uses. Existing-node edits are
   limited to proof, proof_deps and proof_origin. Both new nodes have source, proof,
   searches, creation record, blueprint ancestry, chapter/unit, and Lean records. Read
   the local Stacks Section 0DVG: it states the profinite comparison with a future
   reference, consistently with worker-origin proofs recorded here. The sole remaining
   theorem has its blueprint tag, source and full natural-language proof.

Second reading changed only this report: added the independent checks and explicit
axiom/edge-case verdicts. No Lean repair was needed; preserved the correct proofs.
