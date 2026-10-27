# DiagonalAffineTrace.MapPair and DiagonalAffineTrace.transportCoordinates

## Reason

The delivery compile exceeded the 60-second limit. Profiling located a 16-23 second
elaboration delay in the local finite-type instances in `MapPair`. Instance search
compares the structure maps while concrete affine-tower definitions are reducible.
Cache the supplied base finite-type and quasi-compactness proofs before installing
`Over` instances, then provide the finite-type composite directly with
`locallyOfFiniteType_comp` and the tower projection's existing finite-type proof.
Apply the same local proof changes in `transportCoordinates`.

Only proofs of proposition-valued local instances change; proof irrelevance makes
the resulting public definitions definitionally equal to the originals. No data,
endpoint, signature, attribute or import visible to consumers changes. These are
Sheaf definitions in the assigned module; no adopted-source definition is changed.

## Old

```lean
def MapPair (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (K : Scheme.proEtaleDerivedCategory S P.Ring) (d : ℕ) :=
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aS)
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aS))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  (Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N) ×
    (Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K)

def transportCoordinates (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsNoetherian S]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (hSN : IsUnit (N : Γ(S, ⊤)))
    (K : Scheme.proEtaleDerivedCategory S P.Ring)
    (Ke : Etale.DerivedCategoryModule P.Coefficient S)
    (eK : (comparison P.Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) (d : ℕ)
    (eL : Etale.affineLinearBaseCoefficient P.Coefficient N hA (affineTraceTower S d) d ≅
      P.diagonalTwistEtale (affineTraceTower S d) d)
    (integration : IntegrationSupport P.Coefficient N hA S d Ke ⟶
      (comparison P.Coefficient S).obj Ke) : MapPair P S aS K d :=
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : IsNoetherian X := affineTraceNoetherian S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aS)
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aS))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let e := sourceCoordinates P S d
    ((Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) Ke eK _ eL
  let ES := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let EX := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let η := e.hom ≫
    (comparison P.Coefficient X).map
      (ordinaryTranspose P.Coefficient N hN hA S hSN d Ke) ≫
    ProEtale.boundedSiteRho P.Coefficient
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f) Ke ≫
    (P.smoothPurityExceptionalOver f aS).map eK.hom
  let a := (P.smoothCompactSupport f).map (EX.functor.map e.hom) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification f)).hom.app _ ≫
    ES.functor.map integration ≫
    ES.functor.map eK.hom ≫ ES.counitIso.hom.app K
  ((⟨_, _, EX.functor.map η⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N),
    (⟨_, a⟩ :
      Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K))
```

## New

```lean
def MapPair (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (K : Scheme.proEtaleDerivedCategory S P.Ring) (d : ℕ) :=
  let hft : LocallyOfFiniteType aS := inferInstance
  let hqc : QuasiCompact aS := inferInstance
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := hft
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := hqc
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    @locallyOfFiniteType_comp _ _ _ f aS
      (affineTraceProjection_locallyOfFiniteType S d) hft
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  (Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N) ×
    (Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K)

def transportCoordinates (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsNoetherian S]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (hSN : IsUnit (N : Γ(S, ⊤)))
    (K : Scheme.proEtaleDerivedCategory S P.Ring)
    (Ke : Etale.DerivedCategoryModule P.Coefficient S)
    (eK : (comparison P.Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) (d : ℕ)
    (eL : Etale.affineLinearBaseCoefficient P.Coefficient N hA (affineTraceTower S d) d ≅
      P.diagonalTwistEtale (affineTraceTower S d) d)
    (integration : IntegrationSupport P.Coefficient N hA S d Ke ⟶
      (comparison P.Coefficient S).obj Ke) : MapPair P S aS K d :=
  let hft : LocallyOfFiniteType aS := inferInstance
  let hqc : QuasiCompact aS := inferInstance
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : IsNoetherian X := affineTraceNoetherian S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := hft
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := hqc
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    @locallyOfFiniteType_comp _ _ _ f aS
      (affineTraceProjection_locallyOfFiniteType S d) hft
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let e := sourceCoordinates P S d
    ((Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) Ke eK _ eL
  let ES := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let EX := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let η := e.hom ≫
    (comparison P.Coefficient X).map
      (ordinaryTranspose P.Coefficient N hN hA S hSN d Ke) ≫
    ProEtale.boundedSiteRho P.Coefficient
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f) Ke ≫
    (P.smoothPurityExceptionalOver f aS).map eK.hom
  let a := (P.smoothCompactSupport f).map (EX.functor.map e.hom) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification f)).hom.app _ ≫
    ES.functor.map integration ≫
    ES.functor.map eK.hom ≫ ES.counitIso.hom.app K
  ((⟨_, _, EX.functor.map η⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N),
    (⟨_, a⟩ :
      Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K))
```

## Users

`tools/downstream.py` with `--uses MapPair` and `--uses transportCoordinates` lists
the following users. The sole downstream module is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | S3 | Local proof elaboration only. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed (no local claim file) | Same signatures and definitionally equal data; no adaptation. |

An unchanged temporary copy of `DiagonalAffineTraceSiteComparison` compiled against
the delivered module using `lcompile.py --all`; the temporary copy is excluded from
delivery. No target statement meaning changes: only proposition proofs are replaced.

## Status

landed 20261025T143925-L-1111052 2026-10-25 (merge of deliver/S3/Sheaf.Paper.DiagonalAffineTraceCoordinates)
