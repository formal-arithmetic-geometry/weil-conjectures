# baseChangeTargetSheafComparison

## Reason

Keep every existing signature and comparison morphism unchanged, but replace expensive
unfolding and automatic isomorphism inference by a proved API lemma. The original
sandbox proof attempted broad dsimp/simp on concrete derived functors and timed out.
The comparison remains the same three mathematical isomorphisms;
baseChangeTargetFunctorHigherImageIso and higherDirectImageMapIso spell out the
canonical functor-object conversions. The coefficient-morphism API constructs the
nested functor maps directly with explicit higher-image objects; its equations are
proved by reflexivity. The new proof of IsIso is proof irrelevant. The inverse pullback map also keeps the same data: only its commuting
triangle proof is replaced by the explicit symmetric lift_fst equation.

The added projection lemma targetPullbackComparison_snd packages an existing
pullback.lift_snd computation. Local transparency settings affect this file only.
No target statement or underlying mathematical definition changes meaning; the
existing target statement review does not reopen.

## Old

```lean
noncomputable def targetPullbackComparisonInv (U : Over T) :
    pullback (U.hom ≫ g) p ⟶ ((Over.pullback (pullback.fst g p)).obj U).left :=
  pullback.lift (pullback.fst (U.hom ≫ g) p)
    (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom)
      (pullback.snd (U.hom ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition))
    (by simp)
```

```lean
noncomputable def baseChangeTargetSheafComparison (U : Over T) :
    (baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
      (pullback.snd (U.hom ≫ g) p) q).obj (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F) ≅
    higherDirectImage Λ
      (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p) q
      (((((Over.pullback (pullback.fst g p)).obj U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        (((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  let a := targetPullbackComparison p g U
  let h := pullback.snd (U.hom ≫ g) p
  let h' := ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p
  let w : a ≫ h = h' := by
    dsimp only [a, h, h']
    unfold targetPullbackComparison
    exact pullback.lift_snd _ _ _
  let C := ((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let R := R+((h')_*[ModuleCat.{u + 1} Λ])
  have := targetPullbackTransition_isIso p g Λ U
    ((DerivedCategory.Plus.singleFunctor _ 0).obj C)
  let t := higherDirectImageTransition Λ a h h' w q C
  have : IsIso t := by
    dsimp [t, higherDirectImageTransition]
    infer_instance
  exact (baseChangeTargetFunctorIso Λ (pullback.fst (U.hom ≫ g) p) h q).app _
    ≪≫ asIso t
    ≪≫ (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R ⋙ H).mapIso
      (targetPullbackCoefficientIso p g Λ F U)
```

## New

```lean
noncomputable def targetPullbackComparisonInv (U : Over T) :
    pullback (U.hom ≫ g) p ⟶ ((Over.pullback (pullback.fst g p)).obj U).left :=
  pullback.lift (pullback.fst (U.hom ≫ g) p)
    (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom)
      (pullback.snd (U.hom ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition))
    (by exact (pullback.lift_fst _ _ _).symm)
```

```lean
lemma targetPullbackComparison_snd (U : Over T) :
    targetPullbackComparison p g U ≫ pullback.snd (U.hom ≫ g) p =
      ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p := by
  unfold targetPullbackComparison
  exact pullback.lift_snd _ _ _
```

```lean
noncomputable def baseChangeTargetSheafComparison (U : Over T) :
    (baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
      (pullback.snd (U.hom ≫ g) p) q).obj (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F) ≅
    higherDirectImage Λ
      (((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p) q
      (((((Over.pullback (pullback.fst g p)).obj U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        (((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  let a := targetPullbackComparison p g U
  let h := pullback.snd (U.hom ≫ g) p
  let h' := ((Over.pullback (pullback.fst g p)).obj U).hom ≫ pullback.snd g p
  let w : a ≫ h = h' := targetPullbackComparison_snd p g U
  let C := ((pullback.fst (U.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let R := R+((h')_*[ModuleCat.{u + 1} Λ])
  let t := higherDirectImageTransition Λ a h h' w q C
  have ht : IsIso t := higherDirectImageTransition_isIso_of_lower Λ a h h' w q C
    (targetPullbackTransition_isIso p g Λ U _)
  let I := baseChangeTargetFunctorHigherImageIso Λ (pullback.fst (U.hom ≫ g) p) h q
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
  let M := higherDirectImageMapIso Λ h' q (targetPullbackCoefficientIso p g Λ F U)
  exact I ≪≫ (@asIso _ _ _ _ t ht) ≪≫ M
```

The isomorphism-inference API is the proved theorem
AlgebraicGeometry.Etale.higherDirectImageTransition_isIso_of_lower in
lean/Sheaf/AlgebraicGeometry/HigherDirectImageTransitionIsIsoOfLower.lean.
No existing visibility or signature is changed. The new public APIs construct
only the existing mapped morphisms and isomorphisms, with explicit object types.
The auxiliary comparison_hom and paste_comparisons lemmas are private and proved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | J2 | Own module; the same comparison data and signature, with explicit proof APIs. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Uses the same comparison and naturality statement; no adaptation needed. |

The downstream name scan finds no other external use of either changed definition.
All 122 transitive importers retain the same existing public signatures.
The proved isomorphism API is publicly imported because the public comparison
definition uses it in its body. It adds a public API but no new dependency on an
unproved statement in the comparison definition. No other module is adapted by this delivery.

## Status

landed 20261014T170738-L-2556305 2026-10-14 (merge of deliver/J2/Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality)
