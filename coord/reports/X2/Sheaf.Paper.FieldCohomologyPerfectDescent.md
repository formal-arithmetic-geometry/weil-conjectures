## What changed

Wrote the rational assembly from uniform residue Tor, finite dimension, integral
section perfectness, small finite-projective carriers, rationalization of a
prescribed integral model, and the existing projective Hom comparison. The two
published theorem signatures and the canonical integral-model lift are unchanged.
Added the proved generic small-carrier theorem and one section-rationalization
comparison statement. No data-valued definition uses an existence theorem. A private general-field
assembly lemma keeps coercions from finite subfields out of instance synthesis.
Local irreducibility attributes prevent unfolding the large chosen section
constructions while assembling model isomorphisms.

## Proved and sorry left

The rational theorem `WeilConjectures.field_cohomology_perfect_descent_rational`
is reduced to one new comparison hole, with residue Tor, model extraction, signed
Hom comparison and finite-dimensionality assembled explicitly in Lean.
`DerivedCategory.small_perfect_coefficient_lift` is proved without sorry.
The new hole is `WeilConjectures.sections_rational_model_comparison`
(node `lem-sf-sections-rational-model-comparison`). The existing
`WeilConjectures.field_cohomology_perfect_descent_qbar` remains sorry
(node `lem-sf-field-cohomology-perfect-descent`). Thus one of two original bodies
is closed and one lower hole is added: this is a decomposition, not a net proof.
All three delivery modules compiled together. The two original public theorem
signatures and public imports were compared against the current shared source
and are unchanged. Final compilation and axiom checks run in the delivery tool.

## No longer needed

Removed the direct proof imports of `Sheaf.Paper.SfDerivedDirectImage`,
`Sheaf.Paper.QcqsCompactSupportRealization`, `Sheaf.Paper.FiniteCoefficientPoint`,
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`, and
`Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`. Their interfaces are
already supplied by the statement imports or the two new argument modules.
No original DAG dependency is globally pruned: the direct-image, point-fibre and
localization ingredients occur in the split comparison, and the qbar theorem's
original common-stage route is retained. No source-library declaration or module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The integral perfectness theorem supplies large carriers over ULift R, whereas the
assigned conclusion requires small carriers over R and then its displayed canonical
lift. Added and proved this genuine resizing step rather than assuming the carriers
agree definitionally. The existing rational point-fibre normalization is stated
after a carrier lift, so a prescribed small model needs an explicit comparison
through coefficient transport and the size-descent counit.

## New nodes

`lem-sf-small-perfect-coefficient-lift`: the proved generic shrinking and lifted
coefficient comparison for perfect module complexes, including ordered support
endpoints and the zero complex.

`lem-sf-sections-rational-model-comparison`: rationalization of a supplied integral
ordinary or compact section presentation. It assumes a model presentation and
concludes its scalar extension, but asserts neither existence nor perfectness nor
anything about duals or cohomology; hence it is strictly one step of the rational
argument. Tested mathematically on zero/shifted models, torsion integral
representatives, empty schemes, and arbitrary rational representative isomorphisms.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
