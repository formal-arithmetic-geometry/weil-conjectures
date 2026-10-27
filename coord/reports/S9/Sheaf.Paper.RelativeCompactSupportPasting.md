## What changed

Filled the seven proof bodies in `Sheaf.Paper.RelativeCompactSupportPasting`.
All original public declaration signatures and constructions are unchanged.
Private proved helpers carry mate pasting, the ordinary square calculus, and the
canonical compositor identification. The ordinary open-unit comparison is proved
invertible for arbitrary coefficient rings through the existing localized-site
adjunction and fully faithful coefficient restriction.

The proper-factor identities follow from normalized pullback-square pasting and
the mate counit equation. The open-factor identities follow by transposing the
pulled-back unit; naturality combines them into the compact-support identity.
Three-step pasting follows by applying two-step pasting twice and transporting
along associativity. Finite evaluation uses the existing evaluation squares,
coefficient-exchange counit calculation, and beta evaluation.

The quotient-domain comparison identifies the canonical derived compositor with
localization of `moduleGComp`: normalized units fix the adjunctions, the section
formula fixes `moduleRComp`, and conjugation fixes its pullback comparison.
Substitution then identifies the two compactification-exchange definitions.
The existing comparison-localization module supplies the needed general
localization calculation. Its canonical-unit theorem is used without changing
any dependency module.

The complete module compiles through `lcompile.py` (36.9 seconds).

Updated the existing node's proof and proof dependencies to describe these
calculations. No new public statements, modules, axioms, or holes were added.

## Proved and sorry left

Original holes closed (seven):

- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryBetaInv_isIso`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.towerPasting`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryPasting`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.quotientDomainAgreement`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.finiteEvaluation`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.towerTriplePasting`
- `AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryTriplePasting`

Holes added: none. Holes left in the delivered module: none.
The existing canonical-composition existence/uniqueness theorem remains a proof
dependency in the library; it has not been duplicated or restated.

## No longer needed

Removed the direct proof imports
`WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`,
`Sheaf.Paper.IntegralFinitePullbackComposition`, and
`Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition`.
The evaluation interface already packages the K-injective comparison, and the
quotient proof uses the existing canonical comparison-localization calculation
directly. No library module is withdrawn. Existing public imports are preserved.
The node no longer directly needs `lem-weil-pbc-mate-pasting`: its required
counit calculation is proved privately from Mathlib's mate counit equation.
It also no longer directly needs `lem-weil-pbc-conjugate-iso-unit-equation` for
threefold pasting, which instead uses twofold pasting and equality elimination.
Removed these two obsolete entries from the node's top-level `tool_uses`.
The ordinary formulas are proved directly, so no faithfulness of evaluation or
constant-tower reduction is needed. Triple pasting uses the two-step formulas,
so no separate threefold mate or compositor theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The planned suggestion to infer ordinary transformation identities by evaluating
constant towers is unnecessary. The ordinary module compositors already descend
with the required coherence, and transposing the ordinary open-unit equation
gives the ordinary formulas directly. The proof record now says this explicitly.
The canonical compositor comparison required a normalization argument rather
than definitional equality; the existing localization proof provides it.
No statement or definition repair was needed.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
