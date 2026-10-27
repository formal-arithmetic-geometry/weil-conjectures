## What changed

Proved `AlgebraicGeometry.Scheme.IntegralAmbientTower.arithmetic` in
`Sheaf.Paper.IntegralAmbientCoefficientPresentation`, with its original signature.
Two private proof imports provide the existing PID perfect-model theorem and the
finite additive-order API. Updated the definition node's proof, proof dependencies,
and proof origin to describe this argument. No definitions, public imports, or
consumer interfaces changed. The final single-file server compile passed cleanly
with no warnings in 35 seconds.

The actual valuation ring already has proved principal-ideal, domain, and finite
maximal-ideal-power quotient instances in
`WeilConjectures.NumberTheory.Padics.Extension`. Transfer the first two properties
through `ULift.ringEquiv`. The generator hypothesis identifies the image of each
lifted ideal power with the corresponding maximal ideal power, and
`Ideal.quotientEquiv` transfers finiteness. Finiteness of the first quotient gives
positive finite additive order elementwise. For perfectness, supply the cyclic
surjection from `Fin 1 → A` to `A/I^n` to the existing proved PID-model theorem.
This is valid for every exponent, including the zero quotient at exponent zero;
no nonzero-generator argument or particular choice of uniformizer is required.

Searches: LeanFinder for perfect principal quotients returned ideal and quotient
algebra, with no exact perfectness result; Loogle found `Ideal.quotientEquiv`;
Mathlib grep found no `principalExact` or `twoTermResolution`. Source searches
found the existing concrete valuation-ring instances, the analogous lifted
arithmetic proof in `BoundedConstructibleComplete`, and the proved public
`DerivedCategory.scalar_perfect_cohomology_and_pid_models`. The latter is used
instead of copying private two-term resolution proofs. Its generic PID assertion
is a tool lemma, preserving the open-immersion unit's integral argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.IntegralAmbientTower.arithmetic`
(node `def-sfb-integral-ambient-coefficient-presentation`).
Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No statements split off and no new modules.

## No longer needed

No imports removed and no modules or DAG nodes withdrawn. The item had no
recorded proof dependencies to prune. A separate construction or transfer of the
specific uniformizer-power two-term resolution is unnecessary for arithmetic's
perfectness clause: the existing PID-model theorem applies to the cyclic
quotient directly. The existing `resolution`, `multiplication`, and
`quotientComplex` definitions remain part of the presentation unchanged.

## Where the brief, the DAG or earlier work was wrong

The definition node's proof and proof-dependency arrays were empty despite its
named arithmetic obligation. They now record the actual proof. No statement
error or repair was needed. The informal docstring proves torsion by a specific
ell-power annihilator; the Lean argument proves the unchanged existential
statement using finite additive order instead. Existing docstrings are retained.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
