# AlgebraicGeometry.Scheme.GaloisCover.trait_normalization_generic_section_comparison

## Reason

The assignment is listed as `retire` in `coord/retire-items.tsv`. The Sheaf copy has zero
holes and duplicates a proved theorem in
`WeilConjectures.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison`.
The upstream signature is stronger: it needs fewer hypotheses and returns the extending
ring map `ε : S.functionField →+* K` and its compatibility equation in addition to the
pullback comparison. Its Spec map supplies exactly the old existential witness `b`.
Retire the Sheaf copy and migrate its only direct importer in the same delivery.
The upstream source file, signatures, attributes, definitions and public imports are untouched.

The only DAG parent is `lem-sbc-trait-divisor-chart-section-generic-factor`; it keeps the
same dependency node, now attached to the upstream theorem. No unit statement or step is
bypassed. The source argument remains Stacks `pione.tex`, Tags 0EYI
(`lemma-tame-covering-split`, the root-chart base change at lines 7155–7177) and 0EYJ
(`lemma-extend-covering`, the trait case at lines 7210–7228).

## Old

The retired declaration, verbatim:

```lean
theorem GaloisCover.trait_normalization_generic_section_comparison {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
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
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
∀ (A : CommRingCat.{u}) (_ : IsDomain A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (δ : S.presheaf.stalk s →+* A), Function.Injective δ →
      ∃ (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField)
        (β : pullback n
          (Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ)) ≫ τ) ≅
            pullback Z.π (b ≫ sη)),
        β.hom ≫ pullback.snd Z.π (b ≫ sη) =
          pullback.snd n
            (Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ)) ≫ τ)
```

Its only direct importer was
`Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor`, whose private
import and comparison application were:

```lean
import Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison

  obtain ⟨b, β, hβ⟩ :=
    GaloisCover.trait_normalization_generic_section_comparison
      hS c σ hσ G hG q j hCη sη hsq hsj Z U hηU jU PA ψ hjU hψ
      s hs hmin hdvr A hAd K inferInstance inferInstance inferInstance δ hδ
```

## New

The Sheaf module is withdrawn through `deleted.txt`; its DAG attachment moves to this
existing, unchanged upstream declaration:

```lean
theorem GaloisCover.trait_normalization_generic_section_comparison {S C : Scheme.{u}}
    [IsNoetherian S] [IsIntegral S]
    (c : C ⟶ S) (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    {G : Type (u + 1)} [Group G] [Finite G]
    {Cη : Scheme.{u}} (j : Cη ⟶ C) (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU) (s : S)
    (A : CommRingCat.{u}) [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] (δ : S.presheaf.stalk s →+* A) (hδ : Function.Injective δ) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    let t := Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ))
    ∃ ε : S.functionField →+* K,
      ε.comp (algebraMap (S.presheaf.stalk s) S.functionField) = (algebraMap A K).comp δ ∧
      ∃ β : pullback n (t ≫ τ) ≅ pullback Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη),
        β.hom ≫ pullback.snd Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη) =
          pullback.snd n (t ≫ τ)
```

The consumer retains its exact theorem signature and public imports, and instead uses:

```lean
import WeilConjectures.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison

  obtain ⟨ε, _, β, hβ⟩ :=
    GaloisCover.trait_normalization_generic_section_comparison
      c σ hσ j sη hsj Z U jU PA ψ hjU hψ s A K δ hδ
  let b := Spec.map (CommRingCat.ofHom ε)
```

A declaration-local `set_option linter.unusedVariables false in` preserves its named
hypotheses while acknowledging the seven hypotheses no longer needed by the stronger
upstream comparison. No file-wide option changes.

## Users

The following includes all eight modules reported by `tools/downstream.py` and both
textual occurrences reported by its `--uses` check (the original declaration itself and
its consumer).

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison` | G8, assigned retire item | Withdraw duplicate and attach its node to the existing upstream theorem. |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor` | unclaimed | Replace the private import and adapt the comparison application; retain the existing theorem signature and all public imports. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource` | unclaimed | Indirect consumer; no source changes and no statement changes. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified` | unclaimed | Indirect consumer; no source changes and no statement changes. |

Only the first consumer is adapted. The seven indirect consumers keep their declarations
and proofs. The first two indirect consumers compile against the migrated consumer.
The next module, `StalkNormalizationTraitSectionChartGenericFactor`, times out at 60 s
also against the unmodified published baseline; no source edit is made to that module.
See the report for the exact scope and limitation of the optional downstream checks.
No target statement or definition changes meaning.

## Status

landed 20261020T221204-L-4154937 2026-10-20 (merge of deliver/G8/Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison)
