## What changed

Proved both original holes in `Sheaf.Paper.ECoefficientSmoothBaseChange` without
changing any public signature, definition body, or public import. Added proved private
helpers for the finite coefficient presentations, derived operations, cohomology windows,
quotient orders, and rational naturality.

The arithmetic uses Mathlib's finite p-group cardinality theorem: ell lies in the
uniformizer ideal, so a power of ell kills each finite quotient. Applied the existing
`adicSmoothBaseChange` to the lattice and transported the resulting integral exchange
through scalar localization and the specified rational presentation. The conditional
clause includes explicit comparisons of all four finite systems and their common
cohomology interval, followed by the exact representation equation.

Recorded the proof-context additions in
`coord/changes/A6-e-coefficient-smooth-base-change-proof-context.md`, as required by
preflight for added commands and private instances.

Updated the existing DAG node's proof, dependencies, proof origin, and obsolete tool
uses to match this implementation. No other module was adapted. The private comparison isomorphisms are irreducible, so later elaboration uses their
types without unfolding their constructions. Named private exactness instances and
direct cancellation of the derived realization units avoid repeating equivalence
constructions. Single-file remote
compilation passed with zero errors and warnings after import cleanup. An explicit
end to the proof section restores its elaboration options before appended commands.
The full diagnostic declaration/axiom probe completed in 49 seconds; no nonpermitted
axiom was found. The two temporary diagnostic files are not part of the packet.

## Proved and sorry left

Closed 2 of 2 original holes:

- `WeilConjectures.sbcPrimeUnitOnSource`.
- `WeilConjectures.eCoefficientSmoothBaseChange`.

Retained holes: none. Added holes: none. Split-off statements: none. All new private
helpers have complete proofs. The proof uses existing library declarations, including
the currently admitted `WeilConjectures.adicSmoothBaseChange`; this is a proof from
existing dependencies, not a claim that the entire downstream theorem is axiom-free.

## No longer needed

Removed these original private proof imports:

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: the adic theorem's
  signature already packages its coefficient datum; it does not request a new perfect
  resolution argument.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: the existing completed and finite
  operations suffice; their constructions are not rebuilt.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`: admissibility and the
  realization counit supply the required origin isomorphisms directly.
- `Sheaf.Paper.IntegralUniformCoefficient`: no direct use beyond the datum and
  categories already supplied through the retained interfaces.
- `Sheaf.Paper.PbcRationalCategory`: redundant direct import; its public interface
  already comes from `AdmissibleLattices`.

Retained `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` because it
realizes a unit-route step, as identified by preflight. Its comparison remains used
through the adic theorem, and its existing tool-use approval is retained.

Removed direct proof dependencies `def-pc-perfect-ring-complex` and
`lem-weil-valued-dvr-finite-quotients`. Quotient finiteness is already in the adic datum;
the exact residue-degree cardinality formula and quotient filtration are unnecessary.

Removed obsolete top-level tool uses:
`lem-weil-valued-dvr-finite-quotients`, `prop-weil-pbc-direct-image-limits`,
`lemma-weil-pbc-completed-pullback-reduction`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-normalized-constructible-local-effectivity`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
and `thm-weil-pbc-site-comparison`.
The proof applies the adic theorem rather than reconstructing its proof from these
results. Some remain transitive dependencies of that theorem or of the coefficient
datum. No module is withdrawn and no whole-library unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's final step called the square-admissibility window “exactly” the adic theorem's
window. In Lean these use different coefficient presentations and different finite
operation definitions. The delivery proves the missing comparisons through constant
scalar restriction, exact realization, derived composition, and homology, preserving
the actual four objects and the same interval.

The opening DAG step requested perfect quotient resolutions and a precise cardinality
formula, neither of which the current adic theorem asks the caller to provide. Nilpotence
of ell and the finite p-group theorem give the needed invertible cardinality directly.
The historical unit `sk-rem-rest` has no realized statement or proof steps to bypass.
Preflight identified finite-level comparison as a different unit-route module; its
original import is retained.

No statement or definition repair was required. The empty scheme, zero complex, level
n=0, arbitrary rational presentations, and ramified coefficient extensions require no
extra hypotheses: the comparisons are equivalences, the vanishing argument uses
faithfulness, and the arithmetic needs only ell in the maximal ideal.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
