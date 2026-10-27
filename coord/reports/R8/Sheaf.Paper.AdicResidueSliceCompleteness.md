## What changed

Proved `AlgebraicGeometry.Scheme.adicResidue_slice_completeness` without changing
its statement. Three private helpers name its existing local test, unfold kernel
membership, and compare direct and iterated slice tests. Proof imports use the
existing module equivalence, localization restriction, and derived internal-Hom
restriction along an equivalence of sites. The original public import is retained.
The node proof and direct proof dependencies now record this route.

The site-equivalence comparisons are tools from `sk-lem-sf-mate`; they implement
the same iterated-slice argument recorded in this node, rather than changing the
integral-model unit route. All three comparisons are already proved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicResidue_slice_completeness`
(node `lem-sfb-adic-residue-slice-completeness`). Added zero holes and split off
zero statements. No `sorry` remains in the delivered module.

Validation: the complete proof compiled through `lcompile.py` in 11.1 seconds.
Temporary profiling and trace commands were then removed. The delivery tool
checks the cleaned source, its declaration axioms, and packet preflight.

## No longer needed

No existing Lean import was removed and no module is withdrawn. The original
node dependencies `lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-pur-kinjective-restrict-localized`, and `lem-pur-rhom-well-defined` are not
needed directly by this proof: the existing site-equivalence derived-Hom
comparison packages the representative and K-injective argument. They may
remain needed by other library proofs. In particular, no direct proof import of
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`,
`WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`, or
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap` is added; the latter
representative lemmas remain dependencies of existing comparison proofs.
The derived restriction definition stays in the direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The node's recorded general internal-Hom
dependency now attaches primarily to the shift interface. Its slice-restriction theorem compares overFunctor and
overMap on slices of one site; it does not by itself identify an iterated slice
with the direct slice. The existing NativeRestriction comparisons supply this
identification, so no third split of the completeness obligation is needed.
The kernel criterion and comparison are valid for arbitrary small ringed sites,
including zero rings and empty sites. No Noetherian, boundedness, affine, or
weak-contractibility assumption is used in the proof.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
