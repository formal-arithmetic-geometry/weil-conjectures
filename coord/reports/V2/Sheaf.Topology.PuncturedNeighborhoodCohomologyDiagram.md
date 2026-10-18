## What changed

Proved TopCat.puncturedGeneralizations_le_preimage in the assigned module using
Mathlib's mem_closure_iff. A specialization z of t lies in the open neighborhood N;
the closure criterion forces N to meet the singleton {t}. The definition already
gives t outside Z. All signatures, definitions, and imports are unchanged.
The final module passed remote single-file compilation without warnings (30.7 s).

## Proved and sorry left

Closed one of the two original holes:
TopCat.puncturedGeneralizations_le_preimage.

One original hole remains: TopCat.puncturedNeighborhoodCohomologyLeg_naturality,
attached to def-weil-pbc-punctured-neighborhood-cohomology-diagram. No holes added;
no split-offs. The original theorem's source and complete proof docstring remain.

## No longer needed

None. The sole original import remains necessary for the definitions. The original
node had no proof dependencies or numbered steps to prune. Experimental imports
and definition changes are excluded from the delivery. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing IsPullback interface gives coefficient naturality, boundary
compatibility, and degree-zero normalization, rather than naturality in the open.
For the remaining hole I proved a generic open-naturality helper by evaluating
free-sheaf generators in degree zero and then dimension shifting through an
injective embedding. The argument uses Abelian.Ext.covariant_sequence_exact₁,
Abelian.Ext.eq_zero_of_injective, and Abelian.Ext.comp_assoc. Degree zero uses
objectCohomologyEval₀_injective and toSheafify_naturality.
That helper and its two auxiliary calculations compiled
without holes in a diagnostic version (23.3 seconds). Its integration with the
punctured-subspace specialization still exceeds the per-file compile budget;
local aliases also required explicit bundled-space continuity and exactness
instances. Repeated attempts to control unfolding, make the final composition
explicit, and expose the canonical normalization property did not produce a
verified complete module. The partial delivery retains only the verified
containment proof. No false statement or missing nonemptiness assumption was
found; the containment proof handles empty Z and an empty subspace.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
