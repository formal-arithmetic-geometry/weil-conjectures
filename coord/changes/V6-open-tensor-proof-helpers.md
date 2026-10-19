# OpenTensorNormalization proof helpers

## Reason

Prove continuity, restriction exactness, the Cartesian-square bridge and the final
assembly without changing any existing interface. The static interface check may
classify added declaration-local elaboration options as command changes. All helper
declarations are private and proved. The local topology is used solely in proofs;
the public topology and every operation definition remain unchanged.

## Old

```lean
theorem restriction_exact (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    (restrict m j R).Additive ∧ PreservesFiniteLimits (restrict m j R) ∧
      PreservesFiniteColimits (restrict m j R) := by
  sorry
```

## New

```lean
theorem restriction_exact (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    (restrict m j R).Additive ∧ PreservesFiniteLimits (restrict m j R) ∧
      PreservesFiniteColimits (restrict m j R) := by
  have hc : (proEtaleOpenComposition j).IsCocontinuous
      (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  have : (openInclusion m j).IsCocontinuous (topology m U) (topology m X) := by
    cases m with
    | ordinary => exact hc
    | systems => exact system_cocontinuous (proEtaleOpenComposition j)
  have : (openInclusion m j).IsLeftAdjoint := by
    cases m with
    | ordinary => exact a.isLeftAdjoint
    | systems => exact (systemAdjunction a).isLeftAdjoint
  have : (restrict m j R).IsLeftAdjoint := by
    unfold restrict
    infer_instance
  have : PreservesFiniteLimits (restrict m j R) := by
    let V := toSheaf ((sheafCompose (topology m U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing m j R))
    have : PreservesFiniteLimits (restrict m j R ⋙ V) := by
      change PreservesFiniteLimits (toSheaf _ ⋙
        (openInclusion m j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology m U) (topology m X))
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ V
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩
```

Private helpers added: `verticalTopology`, `verticalSheaf_iff`, `topology_systems_eq`,
`system_continuous`, `system_cocontinuous`, `systemAdjunction`.
The declaration-local `backward.isDefEq.respectTransparency false` option permits
elaboration of the sectionwise product and module categories. No global option or
instance changes. Original proof-only imports that provide no remaining declaration
or proof dependency in Lean are removed; public imports remain identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenTensorNormalization | V6 | Five proofs completed; existing interfaces identical. |

Every importer receives the same public declarations and imports. No downstream module
is adapted. Since only proofs and private helpers change, target-statement review is
not reopened. The remaining two construction proofs retain their original statements.

## Status

landed 20261019T034328-L-421903 2026-10-19 (merge of deliver/V6/Sheaf.SixFunctors.OpenTensorNormalization)
