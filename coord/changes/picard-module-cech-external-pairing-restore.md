# AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing

## Reason
The dispatcher assigned this existing module and its original named hole. Both were
present when the worker began. During the work, the clone changed; the dry-run tool's
refreshed `origin/sheaf-dag` no longer contains the assigned module or its DAG node.
This delivery restores the assigned theorem, with its original signature and a complete
proof, together with a proved Cech-only representatives theorem. This is recorded as an
interface addition relative to the refreshed baseline, rather than a signature change.
No target statement or coefficient definition is changed. An independent reader should
check this restoration against the current project state before landing it.

## Old
The refreshed delivery baseline has no
`Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing` module or
`AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing` declaration.
The assigned version at the start of the task had precisely the signature below, with
its whole proof `:= by sorry`.

## New
The restored declaration has the same signature as the assigned version and a complete
proof. A separate proved theorem
`AlgebraicGeometry.Scheme.Modules.picardExternalCech_moduleRepresentatives` supplies
ordinary module Cech representatives and their front/back cochain identity.

```lean
theorem picardModuleCech_externalPairing
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (cX : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcX : IsModuleCechComparison U F p cX)
    (cY : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcY : IsModuleCechComparison V G q cY)
    (cP : ((cechComplexFunctor
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcP : IsModuleCechComparison
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) (p + q) cP)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup : IsModuleCupProduct ((tensorPullback (pullback.fst f g)).obj F)
      ((tensorPullback (pullback.snd f g)).obj G) p q cup) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2
    let E := externalCupCoefficients f g F G
    let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
    ∀ (a : A.cycles p) (b : B.cycles q) (t : P.cycles (p + q)),
      P.iCycles (p + q) t = h ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) →
      cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso W E.presheafModuleCat
          (p + q)).inv
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso W
          (scalarPresheaf (pullback.fst f g ≫ f) E) (p + q)).hom
            (P.homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cX ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U
            (scalarPresheaf f F) p).hom (A.homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cY ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V
              (scalarPresheaf g G) q).hom (B.homologyπ q b)))))
```

## Users
Neither new module has an existing direct user on the refreshed baseline:
`tools/downstream.py` reports the assigned module as unknown. The prospective dependency
in this delivery is recorded below; its proof import adds no interface to its importers.
No existing user module needs an adaptation, and no claim other than the assigned item
was taken.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing | N3 | Restored assigned statement and proved it; proof-only consumer of the new representatives theorem. |
| Sheaf.AlgebraicGeometry.PicardExternalCechModuleRepresentatives | new, N3 | Added a proved Cech-only representatives theorem; no holes. |

## Status
landed 20261013T181116-L-2605423 2026-10-13 (merge of deliver/N3/Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing)
