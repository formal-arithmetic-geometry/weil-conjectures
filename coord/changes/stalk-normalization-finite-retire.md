# AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_finite

## Reason

Retire the Sheaf duplicate listed in coord/retire-items.tsv. The source library has the
stronger Scheme.stalk_normalization_finite: it proves the identical normalization pullback
finite under a subset of the hypotheses. The sole mathematical parent already imports and
applies that source theorem. A scratch proof retaining the entire old statement applies the
source theorem directly and compiles; both declarations have only standard axioms.

The DAG node is retained and attached to the source theorem. Its mathematical statement and
proof dependencies stay unchanged. No source-library declarations, attributes or imports change.

## Old

```lean
theorem GaloisCover.stalk_normalization_finite {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s)))
```

## New

Withdraw the old Sheaf declaration and use the existing source declaration:

```lean
theorem stalk_normalization_finite {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s)))
```

The old statement follows by:

```lean
  exact AlgebraicGeometry.Scheme.stalk_normalization_finite hS c q j hCη U PA s
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite | Q8 | Retired duplicate; no Lean importers. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Sole DAG parent; already calls Scheme.stalk_normalization_finite; unchanged. |

`tools/downstream.py` reports zero downstream modules. Sources under lean/ and quarantine/
contain no importer of the withdrawn module and no consumer of its fully qualified name.
The DAG parent lem-sbc-stalk-finite-etale-model keeps its dependency on the retained node;
its existing Lean call is precisely the replacement argument. No unit realized entry is
removed or bypassed. Target statements and all definitions they use keep their meanings.

## Status

landed 20261020T221315-L-4171474 2026-10-20 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite)
