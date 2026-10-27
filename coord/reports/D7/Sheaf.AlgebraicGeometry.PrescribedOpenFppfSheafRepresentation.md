## What changed

Filled the proof of
`AlgebraicGeometry.Scheme.existsUnique_prescribedOpen_fppfSheaf_representation`
in `Sheaf.AlgebraicGeometry.PrescribedOpenFppfSheafRepresentation` without changing its
statement or public imports. Added the private proof import
`Mathlib.AlgebraicGeometry.PullbackCarrier` for the existence of points in scheme pullbacks.

The proof first shows that all section types are subsingletons by sheaf separatedness on
the pullback of the etale covering sieve. It glues a section on U, proves that every
section on Z forces Z to factor through U, and uses `uliftYonedaEquiv` and componentwise
bijectivity to construct the representing isomorphism. Subsingletonness proves its
prescribed restrictions, uniqueness, and section formula. Monicity gives unique
factorizations, and the same support argument proves the singleton/empty alternative.
Empty covering families, empty opens, arbitrary index universes, and nonreduced test
schemes are included throughout. The existing node's proof and proof_origin now describe
this implementation; its mathematical dependency set is unchanged.

Searches through msearch leanfinder, loogle, and grep and local source searches found no
existing prescribed-open representation theorem. The representability search returned
Mathlib's Zariski gluing construction, which has different hypotheses; the Yoneda search
identified `CategoryTheory.uliftYonedaEquiv`, used directly here.

Validation: the complete module compiled cleanly through lcompile.py in 4.8 seconds.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.existsUnique_prescribedOpen_fppfSheaf_representation`
(node `lem-trf-prescribed-open-fppf-sheaf-representation`).

Original holes: 1. Closed: 1. Holes added: 0. Holes left: 0. Split off: 0.
No other Lean modules are delivered, and no new public declarations are added.

## No longer needed

None. No imports, nodes, or modules are pruned. The original covering base-change
argument is implemented by covering-sieve pullback stability for sheaf descent and
`Scheme.Pullback.exists_preimage_pullback` for its pointwise surjectivity assertion.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Proving global subsingletonness before gluing
simplifies the planned overlap, restriction, section-formula, and uniqueness calculations.
The unit route and all original hypotheses and conclusions are preserved.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
