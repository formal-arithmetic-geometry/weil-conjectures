# exists_singletonTensorDegreeComparison_hom local limit witnesses

## Reason

Static preflight treats added attribute commands as possible changes to what
importers see. These are `[local instance]` registrations inside this module's
namespace/noncomputable section, used only to prove the existing theorem.
Fresh limit witnesses have definitionally equal but very large types containing
tensor-pullback section constructions; proof-irrelevance comparisons exceed the
60-second compile limit. Reusing the normalization predicate's witnesses makes
the complete proof compile in about 7 seconds. No existing declaration signature,
visibility, definition body, target meaning, or exported instance changes.

## Old

No local witness registration in this module. The original theorem signature is:

```lean
theorem exists_singletonTensorDegreeComparison_hom
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    ∃ f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n,
      IsSingletonTensorDegreeComparisonHom X F U W g n f
```

## New

The theorem signature above remains identical. Before the private proof helpers,
inside `namespace AlgebraicGeometry.Scheme` and `noncomputable section`, add:

```lean
set_option linter.auxLemma false in
attribute [local instance] IsSingletonTensorDegreeComparison._proof_1
  IsSingletonTensorDegreeComparison._proof_2
```

The linter option applies only to this registration. The generated names are
fragile under refactoring of the normalization module; the source comment records
that maintenance requirement. All new helpers are private and proved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom | F1 | Proof-only local registrations; signature unchanged. |
| Every importer of this module | unchanged | No exported interface change; no adaptations required. |

No definition or public statement changes, so no downstream adaptation or renewed
target statement review is required.

## Status

landed 20261013T095947-L-2456525 2026-10-13 (merge of deliver/F1/Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom)
