# Tate twists: finite clauses split from the integral, rational and Q̄ℓ clauses

## Reason

Route audit 2026-10-25 (batch 3 #3 = batch 4 B), approved by the human 2026-10-26. The finite
twists of `Sheaf.Paper.ProEtaleTateTwists` (`spFiniteTwist_locallyFree`,
`spFiniteKummer_existsUnique`) used only the cover, root-generator and finite-coefficient clauses
of `Scheme.tateTwist_locallyFree`, but called the whole theorem, so their proofs reached the
integral, rational and algebraically closed twist clauses. The module also compiled in 67-70 s
alone, over the 60 s limit.

## Old

`Sheaf.Paper.TateTwistLocallyFree` held all definitions, helpers and `tateTwist_locallyFree`;
`ProEtaleTateTwists` obtained the finite clause from `tateTwist_locallyFree X ℓ E₀ (PadicAlgCl ℓ) emb`.

## New

* `Sheaf.Paper.TateTwistFiniteLocallyFree` (new): the finite definitions (`tateFiniteCoefficient`,
  `tateFiniteScalar`, `tateFiniteLine`, `tateFiniteTensor`, `TateSignedLine`, `tateComplexTwist`,
  `tateTensorRight`, `TateInverseTwists`), the finite helpers, and the new theorem
  `tateTwist_finite_locallyFree X ℓ`: the first four conjuncts of `tateTwist_locallyFree`
  (root cover, root compatibility, local trivialization, finite branch), proved from
  `tateRootCover` and `tateFiniteClause`. It imports no integral or rational twist module.
* `Sheaf.Paper.TateTwistIntegralLines` (new): the integral and rational twist definitions and
  their local calculations.
* `Sheaf.Paper.TateTwistLocallyFree`: the Q̄ℓ calculations and `tateTwist_locallyFree`, statement
  unchanged; it imports both new modules publicly, so every declaration name is still available
  to its importers.
* `ProEtaleTateTwists`: both finite uses call `tateTwist_finite_locallyFree`.

Compile times alone (one core): 13.7 s, 20.1 s, 33.2 s, 36.3 s. All 16 direct importers of
`TateTwistLocallyFree` and `ProEtaleTateTwists` compiled against the set; only
`ScalarExtensionFunctor` exceeds 60 s (72 s), as it did before the change (75 s).
DAG: `det-def-sp-tate-twist-locally-free` lists the new declaration; `def-pur-finite-tate-line-signed-comparison`
points to the new module.
