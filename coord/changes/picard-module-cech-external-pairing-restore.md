# AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing

## Reason
This is the dedicated V4 repair of the returned N3 delivery. The checkout and
sandbox lacked both assigned modules; restore the exact modules and nodes from
`coord/repair-notes/Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing.json`.
Both restored modules compile together against the current shared build.
The dry run must still test the reported transitive batch import collision;
individual compilation cannot establish that the collision is fixed.

Beyond restoration, remove the redundant direct public ModuleCohomologyCupProduct
import (its declarations remain public through PicardExternalCechCupBidegree),
and simplify evaluation of the two refinement comparison squares using
ConcreteCategory.congr_hom directly. Every restored public signature is identical
to the returned patch. No target statement or coefficient definition changes.

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
| Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing | V4 | Restored assigned statement and proved it; proof-only consumer of the new representatives theorem. |
| Sheaf.AlgebraicGeometry.PicardExternalCechModuleRepresentatives | restored, V4 | Added a proved Cech-only representatives theorem; no holes. |

## Status
landed 20261014T075512-L-3666925 2026-10-14 (merge of deliver/V4/Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing)
