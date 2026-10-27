# AlgebraicGeometry.ProEtale.scalarModelRestrictionCriterion

## Reason

The intended extended stratification has exactly `S.n + 1` strata, with the complementary
stratum first. The old Lean interface supplied only heterogeneous equalities between its
domain and immersion functions. These do not expose equality of the index counts:
`cases hE_domain` fails on `(Fin (S.n + 1) → Scheme) = (Fin E.n → Scheme)`.

Add the intended count equality `hE_n : E.n = S.n + 1`, retaining both original
heterogeneous equalities of the domain and immersion functions. After aligning the counts,
these equalities are ordinary equalities in the generic transport lemma. A private
`LocalModel` structure keeps concrete sheaf pullbacks abstract while `cons_family` and
`transfer_family` carry out the finite-index case analysis and equality elimination.
The two image-cover hypotheses are retained with underscore-prefixed binder names because
the supplied stratification already provides the partition used by the proof.
No public definition is changed.

This is an interface correction faithful to the specified extension in the source.
No target changes; the old Lean proposition is not counted as a closed hole.

## Old

```lean
theorem scalarModelRestrictionCriterion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T X Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ T) (k : Y ⟶ T) [IsImmersion h] [IsImmersion k]
    (hdisjoint : Disjoint (Set.range h) (Set.range k))
    (hcover : Set.range h ∪ Set.range k = Set.univ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (eh : (CondensedRing.upperStar Λ h).obj H ≅ M)
    (ek : (CondensedRing.upperStar Λ k).obj H ≅ 0)
    (S : Scheme.FiniteLocallyClosedStratification X)
    (E : Scheme.Stratification T)
    (hE_domain : HEq E.domain (fun a : Fin (S.n + 1) ↦
      Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain a))
    (hE_immersion : HEq E.immersion
      (fun a : Fin (S.n + 1) ↦
        Fin.cases (motive := fun b ↦
          Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain b ⟶ T)
          k (fun b ↦ S.immersion b ≫ h) a))
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (P : ∀ a : Fin S.n, (C a).I₀ →
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : ∀ (a : Fin S.n) (r : (C a).I₀), Mod.IsFinitelyPresented Λ (P a r))
    (models : ∀ (a : Fin S.n) (r : (C a).I₀),
      (CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r)) :
    (∀ a : Fin S.n, Nonempty
      ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    (∀ (a : Fin S.n) (r : (C a).I₀), Nonempty
      ((CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r))) ∧
    Nonempty ((0 : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ≅
      cokernel (0 : Mod.finiteFree Λ 0 ⟶ Mod.finiteFree Λ 0)) ∧
    Nonempty (((upperStarFromPoint Y).mapMod Λ).obj 0 ≅ 0) ∧
    Nonempty ((CondensedRing.upperStar Λ (𝟙 Y)).obj
        ((CondensedRing.upperStar Λ k).obj H) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj 0) ∧
    (∀ a : Fin E.n, HasFiniteConstantLocalModel Λ (E.domain a)
      ((CondensedRing.upperStar Λ (E.immersion a)).obj H)) ∧
    IsConstantModelConstructible Λ T H
```

## New

```lean
theorem scalarModelRestrictionCriterion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T X Y : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ T) (k : Y ⟶ T) [IsImmersion h] [IsImmersion k]
    (_hdisjoint : Disjoint (Set.range h) (Set.range k))
    (_hcover : Set.range h ∪ Set.range k = Set.univ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (eh : (CondensedRing.upperStar Λ h).obj H ≅ M)
    (ek : (CondensedRing.upperStar Λ k).obj H ≅ 0)
    (S : Scheme.FiniteLocallyClosedStratification X)
    (E : Scheme.Stratification T)
    (hE_n : E.n = S.n + 1)
    (hE_domain : HEq E.domain (fun a : Fin (S.n + 1) ↦
      Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain a))
    (hE_immersion : HEq E.immersion
      (fun a : Fin (S.n + 1) ↦
        Fin.cases (motive := fun b ↦
          Fin.cases (motive := fun _ ↦ Scheme.{u}) Y S.domain b ⟶ T)
          k (fun b ↦ S.immersion b ≫ h) a))
    (C : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (P : ∀ a : Fin S.n, (C a).I₀ →
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : ∀ (a : Fin S.n) (r : (C a).I₀), Mod.IsFinitelyPresented Λ (P a r))
    (models : ∀ (a : Fin S.n) (r : (C a).I₀),
      (CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a)).obj M) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r)) :
    (∀ a : Fin S.n, Nonempty
      ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    (∀ (a : Fin S.n) (r : (C a).I₀), Nonempty
      ((CondensedRing.upperStar Λ ((C a).f r)).obj
          ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H) ≅
        ((upperStarFromPoint ((C a).X r)).mapMod Λ).obj (P a r))) ∧
    Nonempty ((0 : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ≅
      cokernel (0 : Mod.finiteFree Λ 0 ⟶ Mod.finiteFree Λ 0)) ∧
    Nonempty (((upperStarFromPoint Y).mapMod Λ).obj 0 ≅ 0) ∧
    Nonempty ((CondensedRing.upperStar Λ (𝟙 Y)).obj
        ((CondensedRing.upperStar Λ k).obj H) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj 0) ∧
    (∀ a : Fin E.n, HasFiniteConstantLocalModel Λ (E.domain a)
      ((CondensedRing.upperStar Λ (E.immersion a)).obj H)) ∧
    IsConstantModelConstructible Λ T H
```

## Users

`tools/downstream.py Sheaf.Paper.ScalarModelRestrictionCriterion --uses
scalarModelRestrictionCriterion` lists one downstream module, which only imports the file;
its textual declaration-use list contains only the declaring module. A whole-library search
confirms that no current Lean application needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ScalarModelRestrictionCriterion | B9 | Explicit count equation; complete proof. |
| Sheaf.Paper.OpenExtensionConstructibleFiniteTor | W4 | Import only; signature unchanged. |

The DAG also has two users: `lem-sfb-scalar-model-immersion-extension` and
`lem-sfb-open-extension-zero-constructible-finite-tor`. Both construct an extended
stratification by adjoining one stratum and satisfy the count equation by reflexivity.
Neither has a current Lean application. Their mathematical arguments and conclusions stay
unchanged. The item node's statement-change record lists both users.

## Status

landed 20261024T184643-L-3087952 2026-10-24 (merge of deliver/B9/Sheaf.Paper.ScalarModelRestrictionCriterion)
