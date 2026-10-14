# AlgebraicGeometry.overlap_conjugate_restriction_explicit

## Reason

The Lean intermediate omitted the equation requiring theta to be the canonical conjugated transition. The natural-language node already requires this equation. An arbitrary endomorphism of a nonzero module (for example zero instead of identity, with identity base changes and repeated charts) need not commute with the canonical descent comparison. Restore the missing equation; the outer theorem and all targets keep their signatures.

## Old

```lean
theorem overlap_conjugate_restriction_explicit {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) (θ : S ⟶ T) :
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza S τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb T τb
    let W := (U.pullback₁ q).pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    ∀ (φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b)),
      modulesPseudofunctor.overlapPairBaseChangeHom (V.f a) (V.f b) p
        (V.pullbackHom p a) (V.pullbackHom p b) (W.f a) (W.f b)
        (V.pullbackHom_map p a) (V.pullbackHom_map p b) (A a) (A b) φ =
        ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom →
      overlapPairSquare V A p D ε a b φ
```

## New

```lean
theorem overlap_conjugate_restriction_explicit {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) (θ : S ⟶ T)
    (hθ : θ = overlapConjugatedTransition U t N M e a b ν ha hb hνa hνb S T τa τb) :
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza S τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb T τb
    let W := (U.pullback₁ q).pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    ∀ (φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b)),
      modulesPseudofunctor.overlapPairBaseChangeHom (V.f a) (V.f b) p
        (V.pullbackHom p a) (V.pullbackHom p b) (W.f a) (W.f b)
        (V.pullbackHom_map p a) (V.pullbackHom_map p b) (A a) (A b) φ =
        ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom →
      overlapPairSquare V A p D ε a b φ
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OverlapConjugateRestriction | M2 | The only caller supplies its existing transition equation. |

The declaration-use scan finds no external caller of the intermediate. The module has 1472 transitive importers; none mentions this intermediate declaration. The direct importers are OverlapModelChartFactorization, OverlapPairModelTransport and OverlapStageModelRestriction. Their signatures and interpretation do not change. No forced adaptation is included.

## Status

landed 20261014T090920-L-366460 2026-10-14 (merge of deliver/M2/Sheaf.AlgebraicGeometry.OverlapConjugateRestriction)
