## What changed

Filled nine existing theorem proofs in `Sheaf.Paper.IntegralExceptionalInverseImage`.
The quotient-coordinate maps are a natural transformation of quotient towers; this gives
all quotient compatibilities and the coordinate functor laws. A proved private generic
helper repeats the existing derived-comparison argument with the etale evaluation package
fixed by the caller, then specializes it to the actual etale/pro-etale comparison and the
lifted complete integer ring. Localization and adjunction uniqueness give the three
normalization characterizations. All public signatures, definitions and public imports
are preserved. The node records these proofs and their actual dependencies.

Proof-only imports supply ordinary and unbounded coefficient images, conservative derived
evaluations, exact derived adjunction bounds, scalar-mate descent, integer-ring completeness,
and transport of adic completeness along a ring equivalence. No source-library file changes.
The module compiled through lcompile.py in 44.3 seconds before the final removal of an
unneeded proof import; the final packet is checked again by delivery.

## Proved and sorry left

Original holes: 12. Closed: 9. Added: 0. Split off: 0. This is a partial proof delivery.
All declarations below are in namespace `WeilConjectures` and attached to
`def-pur-adic-exceptional-system-realization`.

Closed:
- `integralExceptionalIdeal`
- `integralExceptionalRingMap_comp`
- `integralExceptionalCoordinates_comm`
- `integralExceptionalCoordinates_laws`
- `integralExceptionalCoordinatesInv_additive`
- `integralExceptionalComparison_exists`
- `integralExceptionalComparison_characterization`
- `integralExceptionalSupport_characterization`
- `integralExceptionalAdjoint_characterization`

The three original named theorem holes remain unchanged, with their original source and
proof docstrings:
- `integralExceptionalCoordinates_properties`: the additive equivalence between the
  concrete sequence-site modules and the generic quotient-coordinate systems.
- `integralExceptionalSupport_exists`: transport the complete normalized etale exceptional
  package to the lifted integer ring.
- `integralExceptionalInverseImage_on_ctf`: the natural comparison with every compatible
  constructible exceptional system.

Every added private helper is fully proved. There are no holes in definitions.
These are proofs from the existing declared dependencies; this report does not claim
that dependencies containing their own named holes are axiom-free.

## No longer needed

No original import, node, or module is pruned: the remaining construction obligations
still use the original route and its unit. The experimental direct sequence-site equivalence
was not retained. The proof does not import `Sheaf.CategoryTheory.SystemEvaluationTopos`
or privately import `Sheaf.Paper.CoefficientEvaluationModels`; these were exploratory
imports only. No declaration in the adopted source tree is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps. Its existing statement is unchanged; the node now
records the actual partial proof route. The generic `coefficientSystemDerivedComparison`
chooses both evaluation packages, whereas this module fixes its etale package in advance.
The private helper uses the same existing construction with that package fixed instead
of assuming its existential witness is definitionally the caller's package.

The etale-adjoint theorem is stated for the integer ring of a field in the site-value
universe. This item's ring is instead a ULift of the original smaller integer ring.
These presentations are canonically equivalent, but are not definitionally identical;
applying that theorem directly does not discharge `integralExceptionalSupport_exists`.

Unrestricted simplification of the coordinate object expanded the site constructions.
Using `dsimp only`, keeping constant sheafification locally irreducible, and proving the
comparison argument generically in this same file kept the validated module below the
unchanged compile limit. No file or proof was split into another module for compilation.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
