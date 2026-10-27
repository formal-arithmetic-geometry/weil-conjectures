## What changed

Proved Profinite.normedScalarProfiniteCech_exact by the stated finite-quotient and
inverse-limit route. An integral cocycle is projected to all positive finite levels;
a first primitive comes from finite_coefficient_cech_primitive_lift with zero target
group, and exists_inverseLimit_cech_primitive supplies compatible primitives.
The ring homeomorphism in coefficientExtension_integers_profinite_tower transports
this back to the integers. Compactness bounds the original field-valued cocycle,
and a sufficiently small nonzero scalar clears its denominators. Fixed scalar multiplication
commutes with every boundary sum.

Moved scalarCechTuples and scalarCechDelete verbatim to the new module
Sheaf.Topology.ProfiniteCechTuples, reexported publicly by the original module.
FiniteCoefficientCechPrimitiveLift and InverseLimitCechPrimitive now publicly
import that module. This removes the cycle that otherwise prevents using their
proved lemmas to prove the assigned theorem. Their proofs and all declaration
signatures are unchanged. Updated the existing tuple node's Lean attachment and
the exactness node's proof plan. No definition, hypothesis, topology, or target changes.
Change record: coord/changes/profinite-cech-tuples-extraction.md.

## Proved and sorry left

Closed the one original hole: Profinite.normedScalarProfiniteCech_exact
(lem-sfb-normed-scalar-profinite-cech-exact). Holes closed: 1 of 1. Holes added: 0.
No sorry remains in any delivered module. No split-off statements are added.
The finite primitive, inverse-limit primitive, and arithmetic theorems used are
existing declarations. The proof closes the assigned hole relative to those dependencies;
this is not a claim that their complete import closure is free of sorry.

## No longer needed

Removed the proof import Sheaf.Topology.FiniteQuotientFiberProduct from the assigned
module. Its node lem-sfb-finite-quotient-fiber-product is not needed by this proof:
the tuple space is closed in the compact finite product, by its closed equalizers.
Removed its obsolete top-level tool_uses approval from the exactness node.
No module is withdrawn. No unit route is bypassed.

The separate node lem-weil-valued-dvr-finite-quotients is not a direct proof
dependency here: positive-level finiteness is already supplied by
Padic.finite_coefficientExtensionRing, and surjectivity is the quotient factor API.
It remains part of the arithmetic dependencies as appropriate.

The public imports of NormedScalarProfiniteCechExact in the two primitive modules
are replaced by ProfiniteCechTuples, since those modules need only the tuple definitions.
No arithmetic public import is removed from the assigned exactness module.

Fresh Mathlib searches used LeanFinder (continuous finite-p-adic Cech exactness),
Loogle (cechComplexFunctor), and grep (Cech exactness). They found group-cohomology
criteria and the abstract Cech complex construction, with no matching exactness theorem.
The existing declared primitive lemmas supply the required route.

## Where the brief, the DAG or earlier work was wrong

The stated finite and inverse-limit primitive lemmas matched the proof plan, but
both imported the exactness module to obtain its tuple definitions. The tuple
extraction resolves this structural cycle without changing their mathematical content.
The theorem docstring describes the older expanded finite-kernel induction; the
current DAG already extracts that induction into the two primitive lemmas, which
this proof uses directly. Mathlib supplies a sufficiently small nonzero scalar in the spectral norm, so no
choice of an additional uniformizer is needed for the localization step.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
