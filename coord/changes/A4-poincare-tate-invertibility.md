# boundedConstructible_tateTwistDerived and boundedConstructibleTateTwist

## Reason

The source Lean theorem omitted the assumption that the coefficient prime is invertible on
X. The reviewed statement of `nt-target-poincare-tate-bc` already includes this assumption,
and explicitly requests repair of the unrestricted source signature. The blueprint Tate-twist
unit has the same domain. This delivery makes Lean agree with that reviewed statement.

STATEMENT-DISPUTED (previous unrestricted signature): in characteristic ell the ordinary
Tate module need not be a locally free line on a nonreduced scheme. For example group
algebras over an algebraic closure of F_ell on an infinite direct sum of Q_ell/Z_ell have
compatible group-like roots with arbitrarily large Tate rank. The ell-invertible local-basis
argument does not apply. This delivery does not claim to prove the unrestricted statement.

The bounded-constructible wrapper must therefore also accept the unit proof. Its six uses
in the same module receive `ell_isUnit ell X`, proved from the already existing assumption
`ringChar k != ell` by mapping a field unit along the structure morphism. No new assumption
is placed on trace, poincareMap, cupProduct, or their theorems. Their underlying derived
objects and morphisms are unchanged; only the proof of membership in the full subcategory
is replaced. No arbitrary witness of an unproved existence theorem is used in any definition.

No declaration of Challenge.lean changes. Any semantic review of a target using the bounded
wrapper should be reopened for this definition change; the intended target statements are
unchanged. The independent reviewer should check the repaired domain and all six uses.

The original private zero-twist helper and import are retained for upstream compatibility. The existing projection transformation is also given a named interface, `poincareProjection`,
with the monoidal structure inferred from the same category instance as the abstract duality
constructions. Its body is exactly `boundedConstructibleExceptionalProjection`; it chooses no
new data. The existing Poincare and cup constructions use this definitionally equal interface.
The isomorphism proof applies the same abstract Yoneda argument to the existing componentwise
projection isomorphisms in a generic private lemma. This avoids repeatedly comparing concrete
internal-Hom structures; no hypothesis, object, morphism or normalization is changed. Local
transparency and instance-priority annotations are confined to this file.

## Old

```lean
lemma boundedConstructible_tateTwistDerived (X : Scheme.{u}) (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) :=
  sorry

noncomputable def boundedConstructibleTateTwist (X : Scheme.{u}) (d n : ℤ) :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X ℓ d), boundedConstructible_tateTwistDerived ℓ X d n⟩
```

Previous Poincare and cup definitions:

```lean
noncomputable def poincareMap :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left d (2 * d)) ⟶
      (ihom ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

noncomputable def cupProduct :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj (𝟙_ _) ⊗
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
          (boundedConstructibleTateTwist ℓ X.left d (2 * d)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left d (2 * d)) :=
  Verdier.cupProduct (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)
```

## New

```lean
lemma boundedConstructible_tateTwistDerived (X : Scheme.{u})
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  apply boundedConstructible_shift_single
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := tateTwistOne_pullback_locally_trivial X ℓ hℓ (𝟙 X)
  refine ⟨𝒰, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (S.immersion a)
  let G := ProEtale.upperStar Ab.{u + 1} (𝒰.f i)
  let Φ := F.mapMod R ⋙ G.mapMod (F.obj R)
  let : F.Braided := ProEtale.CondensedRing.braided_sheafUpperStar _
  let : G.Braided := ProEtale.CondensedRing.braided_sheafUpperStar _
  have : WeaklyEtale (𝒰.f i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hHom (M) : Nonempty (Φ.obj ((ihom M).obj (𝟙_ _)) ≅
      (ihom (Φ.obj M)).obj (Φ.obj (𝟙_ _))) := by
    obtain ⟨eF⟩ := nonempty_pullback_ihom (S.immersion a) R M (𝟙_ _)
    obtain ⟨eG⟩ := nonempty_pullback_ihom (𝒰.f i) (F.obj R)
      ((F.mapMod R).obj M) ((F.mapMod R).obj (𝟙_ _))
    exact ⟨(G.mapMod (F.obj R)).mapIso eF ≪≫ eG⟩
  obtain ⟨e⟩ := powers_image_regular X ℓ Φ (h𝒰 i) hHom d
  refine ⟨1, 0, 0, ⟨?_⟩⟩
  exact e ≪≫ (Limits.biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm ≪≫
    (Limits.cokernelZeroIsoTarget (X := Mod.finiteFree _ 0)).symm

noncomputable def boundedConstructibleTateTwist (X : Scheme.{u})
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (d n : ℤ) :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X ℓ d),
    boundedConstructible_tateTwistDerived ℓ X hℓ d n⟩
```

The proved public helper is `AlgebraicGeometry.ProEtale.CondensedRing.ell_isUnit`.
All six local wrapper applications now pass `(ell_isUnit ell X)` between `X.left` and `d`.

Definitionally equal projection interface and its consumers:

```lean
noncomputable def poincareProjection :
    curriedTensorInsertFunctor₁
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p) ⟶
      curriedTensorPost
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (Functor.whiskeringLeft
          Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧
          Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧
          Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p) :=
  boundedConstructibleExceptionalProjection _ ℓ p

noncomputable def poincareMap :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) ⟶
      (ihom ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (poincareProjection ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

noncomputable def cupProduct :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj (𝟙_ _) ⊗
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
          (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) :=
  Verdier.cupProduct (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (poincareProjection ℓ p)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Poincare | A4 | Repaired theorem and wrapper; six local uses receive the proved unit argument. All other signatures keep their existing hypotheses. |
| TargetsCheck | maintainer | Downstream importer; no direct use of either changed declaration. No source adaptation required. |
| WeilConjectures | maintainer | Downstream importer; no direct use of either changed declaration. No source adaptation required. |

`tools/downstream.py WeilConjectures.PoincareDuality.Poincare --uses` was run for the
changed declarations and their local consumers. Every named direct use is inside the item.
There are no forced adaptations of a module held by another group.

## Status

landed 20261018T035847-L-1403567 2026-10-18 (merge of deliver/A4/WeilConjectures.PoincareDuality.Poincare)
