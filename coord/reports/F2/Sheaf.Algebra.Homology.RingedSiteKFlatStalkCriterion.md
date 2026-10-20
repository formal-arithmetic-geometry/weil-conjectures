## What changed

Completed `CochainComplex.ringedSite_kFlat_stalk_criterion` with its existing statement,
universes, hypotheses and both conclusions unchanged. The forward direction uses a reduced
flat resolution, its acyclic K-flat cone, and finite module tensor tests. The converse uses
exact stalks, signed total tensor comparison and the specified conservative family.

Added seven fully proved supporting modules under `Sheaf.Algebra.Homology`, with matching
nodes. All new public declarations have source references and complete proof descriptions.
No source-library files, existing definitions or other groups' modules were changed.

The main simplification is `RingedSitePoint.finitePresentation_retract`: a finite matrix over
the stalk ring specifies a point of the finite product of the ring sheaf. Coordinate
multiplication on the free sheaf module on that product gives a universal matrix. Inclusion
of the specified generator and coefficient projection split its stalk matrix. Taking
cokernels realizes the prescribed finite module as a retract. This uses the existing unique
normalized inverse-image free-module comparison. It does not choose arbitrary data from an
unproved mere existence theorem.

## Proved and sorry left

Closed the item's one hole: `CochainComplex.ringedSite_kFlat_stalk_criterion`.
Validation: all eight delivered Lean modules compile without errors or warnings through
`lcompile.py --all`; the main proof takes approximately four seconds.
During packet validation, some per-file axiom probes reached their sixty-second limit
although normal compilation completed within the limit. This affected the finite-matrix,
point-resolution and tensor helpers. The delivery tool records that the merge reruns
missing probes. No axiom violation was reported; this is not a claim that every probe ran.
Added zero holes; split off zero unfinished statements. No `sorry` remains in any delivered
Lean file. The seven additional proved declarations are:

- `CategoryTheory.RingedSitePoint.exact`
- `CategoryTheory.RingedSitePoint.acyclic_iff`
- `CategoryTheory.RingedSitePoint.tensor`
- `CategoryTheory.RingedSitePoint.flat`
- `CategoryTheory.RingedSitePoint.exists_kFlat_resolution`
- `CategoryTheory.RingedSitePoint.finitePresentation_retract`
- `CategoryTheory.RingedSitePoint.acyclic_tensor_finitePresentation`

These proofs use existing declared dependencies as authorized by stage 3; their remaining
upstream holes are not claimed closed. In particular, the normalized inverse-image free
comparison and independent inverse-image tensor comparison remain existing library inputs.
The singleton module adjunction, reduced flat-resolution construction, exactness argument,
retract construction and proof combining the steps are supplied here.

## No longer needed

Removed direct imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat`
- `Sheaf.CategoryTheory.Sites.FpStalkRealization`
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`
- `Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The route no longer uses good-site replacement
(`lem-trf-topos-localization-site-presentation`), slice restriction K-flatness
(`lem-sfb-ringed-site-restriction-kflat`), or localized finite-presentation realization
(`lem-sfb-site-fp-stalk-realization`). The universal matrix retract replaces all three.
The ordinary point tensor comparison replaces use of the larger cochain pullback coherence
statement (`lem-pur-cochain-pullback-tensor-coherence`). The independent-coefficient proved
cone and universal tensor-acyclicity helpers replace the corresponding equal-universe
statements. The categorical reduced flat resolution replaces application of the separately
stated site-resolution theorem.

The node proof and proof dependencies now follow the actual argument. Obsolete top-level
tool-use approvals were removed when no longer directly used, preserving the order of the
remaining approvals. No module is withdrawn: these are direct proof-route removals, and
other consumers and transitive imports can still require the old modules.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan is mathematically valid but its good-site replacement and slice
transport are unnecessary. A global sheaf whose stalk has the desired module as a retract
suffices for acyclicity tests; equality with a localized stalk is stronger than needed.
The retract construction works for arbitrary Grothendieck topologies, so the supporting
lemmas need no chosen precoverage or good-site hypothesis. The item's original `hJ` binder
is retained verbatim. The existing unit has no realized nodes bypassed by this proof.

Edge cases: the finite-product matrix construction allows either presentation dimension
to be zero; its point still exists by preservation of the empty finite product. The converse
selects no point, so an empty conservative family is included. Complexes are unbounded and
no flat-term condition is imposed on K. Only the chosen resolution uses flat terms.

## New nodes

`lem-sfb-ringed-site-point-acyclic`: A conservative point family detects acyclicity. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointAcyclic`.

`lem-sfb-ringed-site-point-exact`: Exactness of normalized module stalks. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointExact`.

`lem-sfb-ringed-site-point-flat`: Flat modules remain flat at normalized stalks. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointFlat`.

`lem-sfb-ringed-site-point-fp-retract`: Finite stalk modules are retracts of global module stalks. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointFinitePresentationRetract`.

`lem-sfb-ringed-site-point-kflat-resolution`: K-flat resolution with K-flat stalk. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointKFlatResolution`.

`lem-sfb-ringed-site-point-tensor`: Signed total tensor comparison for normalized stalks. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointTensor`.

`lem-sfb-ringed-site-point-universal-tensor`: Finite module tests from universal tensor acyclicity. Fully proved in `Sheaf.Algebra.Homology.RingedSitePointUniversalTensor`.

Change record: `coord/changes/f2-ringed-site-stalk-criterion-proof-interface.md`.
It records the public import removal and section commands flagged by preflight;
no existing definition or theorem statement changed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
