## What changed

Proved `NumberTheory.dvr_galois_degree_data` in
`lean/Sheaf/NumberTheory/DvrGaloisDegreeData.lean`, with its full original signature and
visibility unchanged. No definitions or consumer modules changed.

Finite separable normalization is finite and Dedekind by Mathlib. Integrality identifies
maximal ideals with the primes over the base maximal ideal; lying over and the Dedekind
finiteness theorem give nonemptiness and finiteness. Dedekind localizations are DVRs, and
contraction of maximal ideals proves the local homomorphism property. Unit-times-power
factorization gives a positive uniformizer exponent. Mapping the principal maximal ideal
and applying `length_quotient_pow_maximalIdeal` identifies that exponent with
`Ideal.ramificationIdx`. The Galois restriction action supplies pretransitivity, equal
indices and equal residue degrees. The existing finite-flat Galois fundamental identity
and the cardinality of the field Galois group give the final degree formula.

Updated the original DAG node's proof, proof dependencies and proof origin to this route,
and removed its obsolete top-level tool approval for the unused general finite-fibre lemma.
The unit statement and its realized steps are not bypassed: this auxiliary node realizes
none of them. Its full DVR/Galois conclusion is proved unchanged.

Validation: the complete file compiles with no errors or warnings through `lcompile.py`,
also after removing all twelve proof-only imports. The final delivery preflight independently
checks compilation and axioms. The proof handles the degree-one case (e=f=g=1), while the
nonfield DVR hypothesis supplies the nonzero base maximal ideal needed for local DVRs.

## Proved and sorry left

Closed 1 of 1 original holes: `NumberTheory.dvr_galois_degree_data`
(node `lem-exc-dvr-galois-degree-data`). No sorry remains in the item, and no holes or
split-off statements were added. Every component is proved using existing Mathlib results;
the proof imports no Sheaf theorem with a remaining sorry.

## No longer needed

Removed these proof-only imports:

- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.RingTheory.Polynomial.RationalRoot`
- `Mathlib.RingTheory.DiscreteValuationRing.TFAE`
- `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
- `Mathlib.RingTheory.Localization.Integral`
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`
- `Mathlib.RingTheory.Ideal.GoingUp`
- `Mathlib.RingTheory.DedekindDomain.Dvr`
- `Mathlib.RingTheory.Invariant.Galois`
- `Mathlib.LinearAlgebra.Determinant`
- `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
- `Sheaf.RingTheory.DvrNormValuationSum`

The used Mathlib declarations remain available through the unchanged public imports.
The following planned dependencies are unnecessary for this proof and were removed from
the node's proof dependencies:

- `lem-sc-dvr-dimension-one`: the DVR is Dedekind directly; no explicit dimension equality
  is required.
- `lem-sc-integral-closure-dedekind-surjective-fibres`, module
  `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`: finite separability
  permits Mathlib's direct Dedekind integral-closure theorem. Ideal finiteness, lying over
  and inertia-degree positivity supply precisely the other needed claims.
- `lem-exc-dvr-norm-valuation-sum`, module `Sheaf.RingTheory.DvrNormValuationSum`:
  the degree identity is already a closed Mathlib finite-flat Galois theorem.
- `def-weil-endomorphism-determinant`: no field norm or determinant is used.

These modules and their dependencies need not be reached through this item; other parents
may still need them. No file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old eight-step plan was sufficient mathematically, but required substantially more
intermediate theory than the conclusion needs. The Mathlib searches already recorded the
Galois fundamental identity; installing finite normalization, fraction fields, the restriction
action and the Galois-group instance makes it apply. The quotient-length calculation also
provides the missing precise comparison between a uniformizer exponent and Mathlib's index.
The original statement is true and was not changed. No process/tool workaround was used.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
