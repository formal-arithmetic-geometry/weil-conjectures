# AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_generic_comparison

## Reason

The assigned row of coord/retire-items.tsv identifies a duplicate of the canonical
WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison theorem.
Both versions are already proved. The source theorem has the identical conclusion and
omits only the unused normal-stalk hypothesis hS and generic-point membership hypothesis hηU.
Use that stronger, proved theorem and remove the duplicate declaration.

## Old

The declaration in Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison:

```lean
theorem GaloisCover.stalk_normalization_generic_comparison {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    letI : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
    ∃ W : GaloisCover G (pullback (pullback.snd c a)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s) S.functionField)))),
      letI : IsFinite W.π := W.isFinite
      ∃ β : pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) ≅
        (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).normalization,
        β.hom ≫ (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).fromNormalization = n
```

## New

Withdraw the Sheaf module using deleted.txt. Keep the following canonical declaration
verbatim in WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison:

```lean
theorem GaloisCover.stalk_normalization_generic_comparison {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    letI : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
    ∃ W : GaloisCover G (pullback (pullback.snd c a)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s) S.functionField)))),
      letI : IsFinite W.π := W.isFinite
      ∃ β : pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) ≅
        (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).normalization,
        β.hom ≫ (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).fromNormalization = n
```

The existing DAG node is attached to this canonical declaration. Its mathematical statement,
proof steps, dependencies and unit route remain in place.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison
--uses GaloisCover.stalk_normalization_generic_comparison` identifies these uses:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison | G7 (assigned retirement) | Withdraw duplicate; its node points to the canonical proved theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed in shared claim records | Redirect private proof import and omit hS and hηU at the application; declaration signature unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed in shared claim records | Redirect private proof import and omit hS and hηU at the application; declaration signature unchanged. |

The chart theorem additionally has a scoped `set_option linter.unusedVariables false in`
and a comment, because the public hS and hηU binders must remain while the canonical theorem
does not use them. The divisor-chart theorem already has this scoped linter option.

The other nine transitive importers do not mention this declaration; the two direct consumers
keep their existing public signatures, definitions and public imports, so those importers
require no adaptation. The two corresponding upstream consumers already use the canonical
module and argument list. No adopted-source file changes.

## Status

landed 20261020T221200-L-4154504 2026-10-20 (merge of deliver/G7/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison)
