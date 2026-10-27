# lem-weil-finite-line-tensor-conditions

## Reason

The generic finite-line theorem's DAG record incorrectly depends on
`def-coefficient-twists-detailed`, in both statement and proof dependencies. Its exact
Lean signature quantifies over an arbitrary finite commutative ring A and an arbitrary
rank-one module sheaf L. It uses the ordinary sheaf tensor, with no Tate object or
coefficient field. Its Lean module `Sheaf.Paper.FiniteLineTensorConditions` does not
import `Sheaf.Paper.CoefficientTwistsDetailed`.

This stale edge creates a false cycle when the already-proved finite-line model theorem
is used to prove signed integral Tate-line constructibility: finite-line models ->
finite-line tensor conditions -> intrinsic coefficient twists -> the integral-line
constructibility theorem. Removing the paper-specific dependency records the genuine
more general proof. No Lean statement, proof, definition, import, or unit step changes.

## Old

The unchanged Lean signature is:

```lean
theorem finiteLineTensor_conditions (S : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1]
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := proEtaleConstantRing S A) L).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)]
    [PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)] :
    IsLocallyConstantProEtaleModuleSheaf S A L ∧
      (∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
        IsConstructibleProEtaleModuleSheaf S A M →
        IsConstructibleProEtaleModuleSheaf S A
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).obj M)) ∧
      ∀ (K : proEtaleDerivedCategory S A) (a b : ℤ),
        HasProEtaleTorAmplitude S A K a b →
        HasProEtaleTorAmplitude S A
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).mapDerivedCategory.obj K) a b
```

`stmt_deps` contains `def-coefficient-twists-detailed`,
`def-weil-finite-torsion-constructibility`, and `def-weil-finite-tor-amplitude`.
The proof step and `proof_deps` also contain `def-coefficient-twists-detailed`.
The exact old statement and dependency fields are retained verbatim in the node's
`statement_change` record.

## New

The Lean signature stays exactly the one above. Only the dependency records change.

The statement and Lean attachment stay verbatim. Remove only the paper-specific
`def-coefficient-twists-detailed` edge and cite the existing generic
`def-weil-sheaf-of-modules-category` and `def-pur-sheaf-tensor-product` instead.
The proof step also records the existing second-map naturality dependency already
present in `proof_deps`. No theorem is generalized, weakened, or replaced.

## Users

All five direct DAG citers retain their exact uses of the same theorem. Their statements
and proofs are unchanged. The signed integral line proof uses finite-line models as a
strict specialization to its ordinary finite scalar reduction. No target statement or
definition changes, and no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteLineTensorConditions | unclaimed | DAG dependencies corrected; no Lean edit |
| Sheaf.Paper.FiniteFieldLisseInternalHom | unchanged | Same generic finite-line theorem |
| Sheaf.Paper.IntegralLineRestrictions | unchanged | Same generic finite-line theorem |
| Sheaf.Paper.FiniteLocallyFreeLineModels | unchanged | Same generic finite-line theorem |
| Sheaf.Paper.TwistPreservesFiniteness | unchanged | Same generic finite-line theorem |
| Sheaf.Paper.TateTwistLocallyFree | unchanged | Same generic finite-line theorem |
| Sheaf.Paper.CoefficientTwistsDetailed | R2 | Uses the existing finite-line model theorem |

The node's `statement_change.citers` lists all five direct DAG citers individually;
every use still holds because the exact mathematical assertion is unchanged.

## Status

landed 20261026T002350-L-80243 2026-10-26 (merge of deliver/R2/Sheaf.Paper.CoefficientTwistsDetailed)
