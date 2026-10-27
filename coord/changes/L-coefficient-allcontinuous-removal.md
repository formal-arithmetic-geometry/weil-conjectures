# IsLocalizingAdmissibleCoefficient: the all-continuous algebraic closure removed

## Reason

Decision of the human, 2026-10-25. `IsLocalizingAdmissibleCoefficient` had a seventh case,
`Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))`: all continuous maps to
the algebraic closure. The blueprint list of sk-def-localizing-closure has six coefficients
A, Z_l, O_E, Q_l, E, Qbar_l. Its Qbar_l is sk-def-sfb-qlbar-condensed, the
finite-subextension-valued `padicAlgClRingObj`. Upstream SmoothPurity/Defs and UpperShriek
do not use the all-continuous ring either. That case pulled about 1333 open nodes into
batch 3 and 1337 into batch 4: the continuous-Qbar exceptional preservation, the topology
comparisons and the Gabber purity route.

## Old

```lean
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))
```

## New

```lean
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))
```

The algebraic closure is now the sixth disjunct, so every `Or.inr` chain that built it
has one `Or.inr` fewer.

Hypotheses that only lose this case:
- `rationalExceptional_preserves_constructibleFiniteTor` takes only `Λ ≅ C(-, E)`.
- The coefficient tables of `torsionCd_topological_serreHeart_cohomology_vanishes`,
  `supported_finite_model_scalar_rigidity` and `weakSerre_mem_supported_derived_generation`
  now list A, Z_l, O_E, Q_l and E.
- The same holds for the lemmas that pass their table on to these three:
  `affine_profinite_family_serreHeart_cohomology_vanishes`,
  `profinite_geometric_family_serreHeart_cohomology_vanishes`,
  `exists_uniform_serreHeart_bound_of_isProper`,
  `proper_wContractible_closedFibre_rigidity`, `closed_torsion_rigidity_serre_transfer` and
  `supported_three_term_scalar_rigidity`.

No conclusion changes. The proofs lose the branch for this case:
- ExceptionalInverseImageExistence, RationalExceptionalRestriction and
  CompactificationRefinementLocalizing (`admissible_standard`).
- ProperLocalizingAdmissibleCoefficients, QcqsProperHullTailBound,
  QcqsProperOpenBoundaryVanishing and MateOpenProperSupport.

The DAG nodes of these statements record the change in `statement_change`.

## Modules no longer used

The following modules exist only for the all-continuous ring. They stay in the library,
but no target uses them now:
- ContinuousQbarExceptionalPreservation, AlgClTopologyMateHomBijection and
  ConstructibleAlgClTopologyComparison.
- ProperLocalizingContinuousAlgCl, ContinuousAlgClProperLowerTail,
  ContinuousAlgClProperHeartFiniteness and RefinementBoundaryVanishing.

Two of them, ContinuousQbarExceptionalPreservation and ContinuousAlgClProperLowerTail, had
built the admissibility of the all-continuous ring. That admissibility is now a `sorry`
with a comment.
