# AlgebraicGeometry.Scheme.root_normalization_localization_comparison

## Reason

Repair reviewer X-42d0f E3: unrestricted i allows extra generic branches. The return explicitly
allows either Mono i or another sufficient branch-identification hypothesis. Use the explicit
cartesian square hbranch identifying the entire generic pullback of U. Mono i would imply this
square given hk, but the existing caller does not assume Mono i or IsOpenImmersion i. Its supplied
chart proves hbranch directly, without changing any caller signature or target statement.

## Old

```lean
theorem root_normalization_localization_comparison
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (H B : CommRingCat.{u}) [Algebra H B] (g : H)
    [(Ideal.span {g}).IsPrime] [IsLocalization.AtPrime B (Ideal.span {g})]
    [IsDomain B] [IsDiscreteValuationRing B]
    (hpi : Irreducible (algebraMap H B g))
    (ψ : Spec H ⟶ L)
    (k : Spec (CommRingCat.of (FractionRing B)) ⟶ U)
    (hk : k ≫ i = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ)
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (ρ : T.P ⟶ W.P) (hT : IsPullback ρ T.π W.π k)
    (hrootloc :
      let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
      let F0 := F.map (algebraMap H B)
      let γ := AdjoinRoot.map (algebraMap H B) F F0 dvd_rfl
      let := γ.toAlgebra
      IsLocalization ((Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)) (AdjoinRoot F0)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      (Ideal.span {AdjoinRoot.root
        ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)}).comap
        (algebraMap H A) = Ideal.span {g} →
      let C := a.normalization.presheaf.stalk x
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      let pi := algebraMap H B g
      let A0 := AdjoinRoot
        ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
      let N0 := Spec (CommRingCat.of A0)
      let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
      let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
      let a0 := pullback.snd (T.π ≫ j0) q0
      ∃ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
        letI := hqc
        letI := hqs
        IsFinite a0.fromNormalization ∧
        ∃ (x0 : a0.normalization),
          (a0.fromNormalization x0).asIdeal = Ideal.span
            {AdjoinRoot.root
              ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} ∧
          ∃ (e : a0.normalization.presheaf.stalk x0 ≃+* C),
            e ((a0.fromNormalization.stalkMap x0).hom
              (AlgebraicGeometry.StructureSheaf.toStalk A0 (a0.fromNormalization x0)
                (AdjoinRoot.root
                  ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))) =
              (a.fromNormalization.stalkMap x).hom t
```

## New

```lean
theorem root_normalization_localization_comparison
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (H B : CommRingCat.{u}) [Algebra H B] (g : H)
    [(Ideal.span {g}).IsPrime] [IsLocalization.AtPrime B (Ideal.span {g})]
    [IsDomain B] [IsDiscreteValuationRing B]
    (hpi : Irreducible (algebraMap H B g))
    (ψ : Spec H ⟶ L)
    (k : Spec (CommRingCat.of (FractionRing B)) ⟶ U)
    (hk : k ≫ i = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ)
    (hbranch : IsPullback k (𝟙 _) i
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ))
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (ρ : T.P ⟶ W.P) (hT : IsPullback ρ T.π W.π k)
    (hrootloc :
      let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
      let F0 := F.map (algebraMap H B)
      let γ := AdjoinRoot.map (algebraMap H B) F F0 dvd_rfl
      let := γ.toAlgebra
      IsLocalization ((Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)) (AdjoinRoot F0)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      (Ideal.span {AdjoinRoot.root
        ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)}).comap
        (algebraMap H A) = Ideal.span {g} →
      let C := a.normalization.presheaf.stalk x
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      let pi := algebraMap H B g
      let A0 := AdjoinRoot
        ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
      let N0 := Spec (CommRingCat.of A0)
      let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
      let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
      let a0 := pullback.snd (T.π ≫ j0) q0
      ∃ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
        letI := hqc
        letI := hqs
        IsFinite a0.fromNormalization ∧
        ∃ (x0 : a0.normalization),
          (a0.fromNormalization x0).asIdeal = Ideal.span
            {AdjoinRoot.root
              ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} ∧
          ∃ (e : a0.normalization.presheaf.stalk x0 ≃+* C),
            e ((a0.fromNormalization.stalkMap x0).hom
              (AlgebraicGeometry.StructureSheaf.toStalk A0 (a0.fromNormalization x0)
                (AdjoinRoot.root
                  ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))) =
              (a.fromNormalization.stalkMap x).hom t
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationDvrComparison | unclaimed | Forced proof adaptation: prove hbranch by transporting the chart pullback along beta and pasting the open-immersion lift square, then pass it to the corrected theorem. All existing signatures, definitions and imports unchanged. |

The direct import and declaration-usage search of lean/ finds only this caller. Indirect callers
see the same DVR comparison statement and conclusions. No target or definition changes.

## Status

landed 20261014T023940-L-17256 2026-10-14 (merge of deliver/V3/Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationLocalizationComparison)
