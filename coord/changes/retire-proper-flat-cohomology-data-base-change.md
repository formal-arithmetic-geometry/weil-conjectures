# AlgebraicGeometry.Scheme.Modules.proper_flat_cohomology_model_data_base_change

## Reason

Repair reviewer X-87b4c, head 87b4cd474, E2 (brief point 4). The arbitrary-complex
comparison is false: for the identity on Spec k, F = O, U = top, C = 0 and d = 0,
the q = 0 comparison would give 0 isomorphic to the nonzero structure sheaf.
Bounds, termwise flatness and quasi-coherence do not connect C with F.
The reviewer expressly requests deletion and restoration of the true parent hole.

## Old

```lean
theorem proper_flat_cohomology_model_data_base_change {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T)
    (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (ht : t ∈ U) (hU : IsAffine U.toScheme) (hCge : C.IsStrictlyGE 0)
    (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent) :
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))
```

## New

The entire declaration and misleading proof docstring are deleted. The disputed
explanation remains in the module, which now has no declarations or imports.
The node's lean record is null, proof and proof_deps are empty, and proof_origin
records this withdrawal. The node's historical statement is not replaced by a
weaker assertion.

The parent exists_proper_flat_cohomology_model_data retains its complete signature,
visibility and complete source proof docstring. Its entire proof body is restored
to `sorry`; its two proof imports of ProperFlatCohomologyDataConstruction and
ProperFlatCohomologyDataBaseChange are removed. Its node retains the full Cech
construction/comparison plan and five original mathematical proof dependencies;
proof_origin records that the implementation is open and the invalid split is withdrawn.
No target statement or definition changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProperFlatCohomologyDataBaseChange
--uses proper_flat_cohomology_model_data_base_change` reports only the declaring
module and ProperFlatCohomologyData as textual users of the deleted theorem.
The 699 transitive importers retain their interfaces through the unchanged parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyDataBaseChange | S3 | Withdraw false theorem and unused imports. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyData | unclaimed | Forced adaptation: remove two split imports and restore parent proof to sorry. |

The original parent compiles against the compiled baseline. Against the delivered
withdrawn module it fails at original line 56:8:

```
error(lean.unknownIdentifier): Unknown identifier `proper_flat_cohomology_model_data_base_change`
```

Only original import lines 10-11 and proof-body lines 52-56 change in the parent.
The repaired parent compiles against the delivered set. There is no available
valid theorem asserting the comparison for the arbitrary construction witness;
restoring the parent hole is the reviewer's exact conservative repair.

## Status

landed 20261012T213438-L-1178630 2026-10-12 (merge of deliver/S3/Sheaf.AlgebraicGeometry.ProperFlatCohomologyDataBaseChange)
