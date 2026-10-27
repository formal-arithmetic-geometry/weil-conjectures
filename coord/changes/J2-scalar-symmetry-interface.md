# WeilConjectures.PurityFiniteSetting.finiteTensorSymmetryCoherence

## Reason

The newly landed symmetry consumer (Y7, now unclaimed) failed against the repaired
normalization and cochain comparison interfaces. Opening the original square locally
restored its proof, but took 68 seconds; moving conversion to its old scalar helper
took 88 seconds. The adopted source already constructs a braided native derived scalar
functor. Use this completed library result: transport braidedness along the exact same
left-adjoint comparison as the constructed model, then identify that model with the
chosen normalized core by uniqueness. This is a shorter proof of the identical public
statement and avoids rebuilding the native cochain braiding argument.

## Old

```lean
theorem finiteTensorSymmetryCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∀ U V, FiniteTensorSymmetrySquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorCore m hm hmn T) U V := by
  exact scalarSymmetry (P.finiteReductionRingHom m hm hmn).ulift T
    (P.finiteTensorCore m hm hmn T)
    (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.1
```

## New

```lean
theorem finiteTensorSymmetryCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∀ U V, FiniteTensorSymmetrySquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorCore m hm hmn T) U V := by
  let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  have hm' : P.FiniteTensorCoreNormalized m hm hmn T (finiteScalarMonoidalModel φ T) :=
    fun C D _ _ ↦ finiteScalarMonoidalModel_representative φ T C D
  have he : finiteScalarMonoidalModel φ T = P.finiteTensorCore m hm hmn T :=
    (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.2 _ hm'
  intro U V
  rw [← he]
  exact scalarModelSymmetry φ T U V
```

The two new private helpers prove transport of the braiding square and instantiate
the completed native braided scalar constructor. Their complete proofs are in the
module. Remove the twelve unused private cochain helpers and two now unused private
proof imports. Every public declaration, signature, public import and docstring remains
verbatim. Ordinary concurrent checking replaces `Elab.async false`. No new hole is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed (Y7 landed 2026-10-26) | Same public statement, proved by native braided scalar transport and normalized-core uniqueness. |

All importers continue to use the same public theorem. No adopted source file changes.

## Status

landed 20261026T070008-L-3329438 2026-10-26 (merge of deliver/J2/Sheaf.Paper.FiniteTensorSignedReduction)
