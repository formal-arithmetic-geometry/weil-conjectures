# AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.Statement

## Reason

The original type-producing proof destructures `factorization` with `obtain`. Lean
compiles this as a nested `And.casesOn` over an auto-generated auxiliary proof.
Destructuring the visible factorization theorem in a proof does not reduce that
match; using the generated name works but produces an unstable-auxiliary warning.
Replace only that destructuring with explicit conjunction projections. The same
factorization theorem supplies every equation and geometric instance, in the same
order. All arrow formulas and all hypotheses remain identical.

## Old

```lean
def Statement (P : WeilConjectures.PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [IsAffine U] [IsAffine V] [IsAffine T]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (f : U ⟶ V) (g : V ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (x : U ⟶ A d V) (y : V ⟶ A e T) [Etale x] [Etale y]
    (hx : x ≫ pr d V = f) (hy : y ≫ pr e T = g) : Prop := by
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  letI := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  letI : IsNoetherian U := ⟨⟩
  letI : IsNoetherian V := ⟨⟩
  letI : IsNoetherian T := ⟨⟩
  obtain ⟨hHJ, hHa, hGpr, hJq, hGs, hFt, _, _, hFpr,
    hGe, hGsep, hGlft, hGqc, hHe, hHsep, hHlft, hHqc,
    hJe, hJsep, hJlft, hJqc, hFe, hFsep, hFlft, hFqc,
    hQa, hWa, hRa, hWfa, hWga, hAda, hAea, hAdea, hAdVa, hAeTa, hAeVa,
    _, _, _, _, hRsq, hAffsq, hsq, hPe, hPde, hqQ, hHsq, hGsq,
    hHfe, hGge, hHfz, hGgz⟩ := factorization (k := P.field.k) f g d e x y hx hy
  letI := hGe
  letI := hGsep
  letI := hGlft
  letI := hGqc
  letI := hHe
  letI := hHsep
  letI := hHlft
  letI := hHqc
  letI := hJe
  letI := hJsep
  letI := hJlft
  letI := hJqc
  letI := hFe
  letI := hFsep
  letI := hFlft
  letI := hFqc
  letI := hQa
  letI := hWa
  letI := hRa
  letI := hWfa
  letI := hWga
  letI := hAda
  letI := hAea
  letI := hAdea
  letI := hAdVa
  letI := hAeTa
  letI := hAeVa
  letI := hsq
  letI := hPe
  letI := hPde
  letI := hqQ
  letI := hHfe
  letI := hGge
  letI := (geometryProperties d e f g).1
  letI := (geometryProperties d e f g).2.1
  letI := (geometryProperties d e f g).2.2.1
  letI := (geometryProperties d e f g).the project server
  letI := (geometryProperties d e f g).the project server
  letI := affineDimension d U
  letI := affineDimension e V
  letI := affineDimension (d + e) U
  let aU := U ↘ Spec (.of P.field.k)
  let aV := V ↘ Spec (.of P.field.k)
  let aT := T ↘ Spec (.of P.field.k)
  let aQ := pullback.fst (f ≫ g) g ≫ aU
  let t := pullback.diagonal (f ≫ g)
  let G := differenceSecond e f g y
  let HH := H f g x
  let JJ := J d f g y
  let FF := differenceTotal d e f g x y
  let qQ := R d f g ↘ Q f g
  let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
    (AffineSpace.homOfVector_over _ _).symm
  let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
    (AffineSpace.homOfVector_over _ _).symm
  let chiF := (pull P (pullback.diagonal f)).map
    (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
      hHfpr aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
  let chiG0 := (pull P (pullback.diagonal g)).map
    (normalizedE P (differenceFirst e g y) (pr e V) (pullback.fst g g)
      hGgpr aV).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal g) (differenceFirst e g y) (zero e V) hGgz.symm).inv.app _
  let tau :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      f (zero e V)).inv.app _ ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero e U) (AffineSpace.map (Coords e) f) (f ≫ zero e V)
      (AffineSpace.zeroSection_comp_map f).symm).hom.app _ ≫
    (pull P (zero e U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P e
        (AffineSpace.isPullback_map f) (pr e V ≫ aV)).hom
  let chiG := (pull P f).map chiG0 ≫ tau
  letI := (affineGeometry d e U).the project server.2.1
  letI := (affineGeometry d e U).the project server.2.2.1
  letI := (affineGeometry d e U).the project server.the project server
  let delta :=
    (pull P (zero (d + e) U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
        hAffsq (pr d U ≫ aU)).inv ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero (d + e) U) (first d e U) (zero d U)
      (affineGeometry d e U).2.1.symm).inv.app _
  let firstRoute := (gammaF P.Coefficient P d f g aT).hom ≫
    (pull P t).map
      ((normalizedE P HH qQ (a f g) hHa.symm aQ).hom ≫
        (pull P HH).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
            hRsq (pr (d + e) U ≫ aU)).inv ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          HH JJ FF hHJ.symm).inv.app _) ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      t FF (zero (d + e) U) hFt.symm).inv.app _ ≫ delta
  let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
    (pull P (s f g)).map
      (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (s f g) G (zero e U) hGs.symm).inv.app _
  let outputDirect := (pull P t).map
    (normalizedE P FF (pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
      hFpr.symm aU).hom
  let outputComposite := (pull P t).map
    ((normalizedE P HH (JJ ≫ pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
        (hFpr.symm.trans ((congrArg (fun v ↦ v ≫ pr (d + e) U) hHJ.symm).trans
          (Category.assoc HH JJ (pr (d + e) U)))) aU).hom ≫
      (pull P HH).map (normalizedE P JJ (pr (d + e) U)
        (JJ ≫ pr (d + e) U) rfl aU).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        HH JJ FF hHJ.symm).inv.app _)
  exact SameProEtaleMap P.Coefficient P chiF firstRoute ∧
    SameProEtaleMap P.Coefficient P chiG secondRoute ∧
    SameProEtaleMap P.Coefficient P outputDirect outputComposite
```

## New

```lean
def Statement (P : WeilConjectures.PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [IsAffine U] [IsAffine V] [IsAffine T]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (f : U ⟶ V) (g : V ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (x : U ⟶ A d V) (y : V ⟶ A e T) [Etale x] [Etale y]
    (hx : x ≫ pr d V = f) (hy : y ≫ pr e T = g) : Prop := by
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  letI := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  letI : IsNoetherian U := ⟨⟩
  letI : IsNoetherian V := ⟨⟩
  letI : IsNoetherian T := ⟨⟩
  let fac := factorization (k := P.field.k) f g d e x y hx hy
  let hHJ := fac.1
  let hHa := fac.2.1
  let hGpr := fac.2.2.1
  let hJq := fac.the project server
  let hGs := fac.the project server.1
  let hFt := fac.the project server.2.1
  let fac1 := fac.the project server.the project server
  let hFpr := fac1.1
  let hGe := fac1.2.1
  let hGsep := fac1.2.2.1
  let hGlft := fac1.the project server
  let hGqc := fac1.the project server.1
  let hHe := fac1.the project server.2.1
  let hHsep := fac1.the project server.2.2.1
  let hHlft := fac1.the project server.the project server
  let fac2 := fac1.the project server.the project server
  let hHqc := fac2.1
  let hJe := fac2.2.1
  let hJsep := fac2.2.2.1
  let hJlft := fac2.the project server
  let hJqc := fac2.the project server.1
  let hFe := fac2.the project server.2.1
  let hFsep := fac2.the project server.2.2.1
  let hFlft := fac2.the project server.the project server
  let fac3 := fac2.the project server.the project server
  let hFqc := fac3.1
  let hQa := fac3.2.1
  let hWa := fac3.2.2.1
  let hRa := fac3.the project server
  let hWfa := fac3.the project server.1
  let hWga := fac3.the project server.2.1
  let hAda := fac3.the project server.2.2.1
  let hAea := fac3.the project server.the project server
  let fac4 := fac3.the project server.the project server
  let hAdea := fac4.1
  let hAdVa := fac4.2.1
  let hAeTa := fac4.2.2.1
  let hAeVa := fac4.the project server
  let fac5 := fac4.the project server.the project server
  let hRsq := fac5.1
  let hAffsq := fac5.2.1
  let hsq := fac5.2.2.1
  let hPe := fac5.the project server
  let hPde := fac5.the project server.1
  let hqQ := fac5.the project server.2.1
  let hHsq := fac5.the project server.2.2.1
  let hGsq := fac5.the project server.the project server
  let fac6 := fac5.the project server.the project server
  let hHfe := fac6.1
  let hGge := fac6.2.1
  let hHfz := fac6.2.2.1
  let hGgz := fac6.2.2.2
  letI := hGe
  letI := hGsep
  letI := hGlft
  letI := hGqc
  letI := hHe
  letI := hHsep
  letI := hHlft
  letI := hHqc
  letI := hJe
  letI := hJsep
  letI := hJlft
  letI := hJqc
  letI := hFe
  letI := hFsep
  letI := hFlft
  letI := hFqc
  letI := hQa
  letI := hWa
  letI := hRa
  letI := hWfa
  letI := hWga
  letI := hAda
  letI := hAea
  letI := hAdea
  letI := hAdVa
  letI := hAeTa
  letI := hAeVa
  letI := hsq
  letI := hPe
  letI := hPde
  letI := hqQ
  letI := hHfe
  letI := hGge
  letI := (geometryProperties d e f g).1
  letI := (geometryProperties d e f g).2.1
  letI := (geometryProperties d e f g).2.2.1
  letI := (geometryProperties d e f g).the project server
  letI := (geometryProperties d e f g).the project server
  letI := affineDimension d U
  letI := affineDimension e V
  letI := affineDimension (d + e) U
  let aU := U ↘ Spec (.of P.field.k)
  let aV := V ↘ Spec (.of P.field.k)
  let aT := T ↘ Spec (.of P.field.k)
  let aQ := pullback.fst (f ≫ g) g ≫ aU
  let t := pullback.diagonal (f ≫ g)
  let G := differenceSecond e f g y
  let HH := H f g x
  let JJ := J d f g y
  let FF := differenceTotal d e f g x y
  let qQ := R d f g ↘ Q f g
  let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
    (AffineSpace.homOfVector_over _ _).symm
  let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
    (AffineSpace.homOfVector_over _ _).symm
  let chiF := (pull P (pullback.diagonal f)).map
    (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
      hHfpr aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
  let chiG0 := (pull P (pullback.diagonal g)).map
    (normalizedE P (differenceFirst e g y) (pr e V) (pullback.fst g g)
      hGgpr aV).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal g) (differenceFirst e g y) (zero e V) hGgz.symm).inv.app _
  let tau :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      f (zero e V)).inv.app _ ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero e U) (AffineSpace.map (Coords e) f) (f ≫ zero e V)
      (AffineSpace.zeroSection_comp_map f).symm).hom.app _ ≫
    (pull P (zero e U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P e
        (AffineSpace.isPullback_map f) (pr e V ≫ aV)).hom
  let chiG := (pull P f).map chiG0 ≫ tau
  letI := (affineGeometry d e U).the project server.2.1
  letI := (affineGeometry d e U).the project server.2.2.1
  letI := (affineGeometry d e U).the project server.the project server
  let delta :=
    (pull P (zero (d + e) U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
        hAffsq (pr d U ≫ aU)).inv ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero (d + e) U) (first d e U) (zero d U)
      (affineGeometry d e U).2.1.symm).inv.app _
  let firstRoute := (gammaF P.Coefficient P d f g aT).hom ≫
    (pull P t).map
      ((normalizedE P HH qQ (a f g) hHa.symm aQ).hom ≫
        (pull P HH).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
            hRsq (pr (d + e) U ≫ aU)).inv ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          HH JJ FF hHJ.symm).inv.app _) ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      t FF (zero (d + e) U) hFt.symm).inv.app _ ≫ delta
  let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
    (pull P (s f g)).map
      (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (s f g) G (zero e U) hGs.symm).inv.app _
  let outputDirect := (pull P t).map
    (normalizedE P FF (pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
      hFpr.symm aU).hom
  let outputComposite := (pull P t).map
    ((normalizedE P HH (JJ ≫ pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
        (hFpr.symm.trans ((congrArg (fun v ↦ v ≫ pr (d + e) U) hHJ.symm).trans
          (Category.assoc HH JJ (pr (d + e) U)))) aU).hom ≫
      (pull P HH).map (normalizedE P JJ (pr (d + e) U)
        (JJ ≫ pr (d + e) U) rfl aU).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        HH JJ FF hHJ.symm).inv.app _)
  exact SameProEtaleMap P.Coefficient P chiF firstRoute ∧
    SameProEtaleMap P.Coefficient P chiG secondRoute ∧
    SameProEtaleMap P.Coefficient P outputDirect outputComposite
```

## Users

The import/downstream search reports no modules downstream of the item module.
The only direct use of `Statement` is its own main theorem. The DAG parent
`lem-pur-diagonal-section-pasting` needs the same three equations and is unaffected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | Y7 | Explicit projections expose the same conjunction without generated proof names. |

No target statement, mathematical hypothesis, arrow, or equality is changed.
No consumer adaptation is needed. No unit route changes.

## Status

landed 20261025T203833-L-2861968 2026-10-25 (merge of deliver/Y7/Sheaf.Paper.DifferenceCoordinateSectionIdentifications)
