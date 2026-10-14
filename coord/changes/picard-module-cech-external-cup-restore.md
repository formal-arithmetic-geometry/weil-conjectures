# AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalCup

## Reason

The assignment snapshot contained this module and its node, with one sorry. During
this session the P3 parent delivery was rolled back: the fresh sheaf-dag base has
neither the module nor its node. The first dry run therefore required a restoration
record and new-node metadata. This delivery restores the assigned theorem with a
complete proof from the existing proved picardModuleCech_externalPairing.

The P3 return of 2026-10-14 reports a BatchProbe import collision between anonymous
instances in ModuleCupNaiveDerivedCompatibility and GlobalTensorPullbackMonoidalNormalization.
Follow the existing E3 pairing restoration: expand IsModuleCupProduct and
IsPicardExternalCechCupBidegree in the theorem's two hypothesis types and use the
lightweight CechCupProductCore/ModuleCupResolutionData imports. The n2 front/back
functions are definitionally equal to the original front/back functions. Every
binder, degree, cover equation, comparison, cycle, inclusion equality and conclusion
is retained with a definitionally equal type. No mathematical statement is changed.
The exact original predicate-wrapped signature is checked as an example by Lean.

## Old

The fetched base has no module or declaration. The exact assigned signature was:

```lean
theorem picardModuleCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison V G q cG)
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
      ((tensorPullback (pullback.snd f g)).obj G) p q cup)
    (l : ((curriedTensor (ModuleCat.{w} k)).obj
      (((picardCechFunctor f U).obj F).X p)).obj
        (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).X (p + q))
    (hl : IsPicardExternalCechCupBidegree f g U V F G p q l)
    (a : ((picardCechFunctor f U).obj F).cycles p)
    (b : ((picardCechFunctor g V).obj G).cycles q)
    (t : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).cycles (p + q))
    (ht : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).iCycles (p + q) t =
      l ((((picardCechFunctor f U).obj F).iCycles p a) ⊗ₜ[k]
        (((picardCechFunctor g V).obj G).iCycles q b))) :
    cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
      (externalCupCoefficients f g F G).presheafModuleCat (p + q)).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q)).hom
        (((picardCechFunctor (pullback.fst f g ≫ f)
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)).obj
              (externalCupCoefficients f g F G)).homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cF ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) p).hom
            (((picardCechFunctor f U).obj F).homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cG ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V (scalarPresheaf g G) q).hom
              (((picardCechFunctor g V).obj G).homologyπ q b)))))
```

The assigned import list was:

```lean
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
public import Sheaf.Paper.ModuleCohomologyCupProduct
import Sheaf.Paper.CechCupPullbackCompat
import Sheaf.Paper.CechComparisonMapNaturality
```

## New

The restored signature expands only the two predicate hypotheses:

```lean
theorem picardModuleCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison V G q cG)
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
    (hcup :
      ∀ (D : CupResolutionPairing
                ((tensorPullback (pullback.fst f g)).obj F)
                ((tensorPullback (pullback.snd f g)).obj G))
          (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
          (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
          (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
          c.val = D.pair p q ⊤ a.val b.val →
            cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (l : ((curriedTensor (ModuleCat.{w} k)).obj
      (((picardCechFunctor f U).obj F).X p)).obj
        (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).X (p + q))
    (hl :
      ∀ (a : ((picardCechFunctor f U).obj F).X p)
              (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
              TopCat.Presheaf.cechComplexFunctorXAddEquiv
                (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
                  pullback.snd f g ⁻¹ᵁ V ij.2)
                (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
                (p + q) (l (a ⊗ₜ[k] b)) y =
                tmulSection
                  (((fun (Q : X.Opens) (W : (Limits.pullback f g).Opens)
                      (h : W ≤ pullback.fst f g ⁻¹ᵁ Q) (s : Γ(F, Q)) ↦
                    ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE h).op
                      (((Classical.choose (exists_tensorPullbackAdjunction
                        (pullback.fst f g))).unit.app F).val.app (op Q) s))
                    (⨅ l, U (y (n2CupFront p q l)).1) _
                    (by
                      intro x hx
                      change (pullback.fst f g).base x ∈ ⨅ l, U (y (n2CupFront p q l)).1
                      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                      intro l
                      exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                        pullback.snd f g ⁻¹ᵁ V (y j).2) (n2CupFront p q l) hx).1)
                    (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a
                      (fun l ↦ (y (n2CupFront p q l)).1))))
                  (((fun (Q : Y.Opens) (W : (Limits.pullback f g).Opens)
                      (h : W ≤ pullback.snd f g ⁻¹ᵁ Q) (s : Γ(G, Q)) ↦
                    ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE h).op
                      (((Classical.choose (exists_tensorPullbackAdjunction
                        (pullback.snd f g))).unit.app G).val.app (op Q) s))
                    (⨅ l, V (y (n2CupBack p q l)).2) _
                    (by
                      intro x hx
                      change (pullback.snd f g).base x ∈ ⨅ l, V (y (n2CupBack p q l)).2
                      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                      intro l
                      exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                        pullback.snd f g ⁻¹ᵁ V (y j).2) (n2CupBack p q l) hx).2)
                    (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b
                      (fun l ↦ (y (n2CupBack p q l)).2)))))
    (a : ((picardCechFunctor f U).obj F).cycles p)
    (b : ((picardCechFunctor g V).obj G).cycles q)
    (t : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).cycles (p + q))
    (ht : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).iCycles (p + q) t =
      l ((((picardCechFunctor f U).obj F).iCycles p a) ⊗ₜ[k]
        (((picardCechFunctor g V).obj G).iCycles q b))) :
    cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
      (externalCupCoefficients f g F G).presheafModuleCat (p + q)).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q)).hom
        (((picardCechFunctor (pullback.fst f g ≫ f)
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)).obj
              (externalCupCoefficients f g F G)).homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cF ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) p).hom
            (((picardCechFunctor f U).obj F).homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cG ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V (scalarPresheaf g G) q).hom
              (((picardCechFunctor g V).obj G).homologyπ q b)))))
```

The restored import list is:

```lean
public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProductCore
public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing
```

The complete proof applies picardModuleCech_externalPairing to all the original data.
No axiom, definition, private helper, arbitrary witness or new sorry is added.

## Users

A source search of the fresh repository finds no remaining module importing this
withdrawn module or mentioning picardModuleCech_externalCup. The previous parent
PicardScalarCechExternalCup is also absent after the rollback. Hence no existing
consumer is adapted or changes meaning. A future consumer can supply the original
predicate hypotheses, as the exact original-signature example verifies. The removed
public imports from the assignment are not needed for the expanded signature; this
restoration deliberately does not re-export the colliding predicate import chain.
The module and its node remain in sk-prop-av-cube, following the same source route.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardModuleCechExternalCup | W3 | Restore the assigned theorem, definitionally equal expanded hypotheses, and complete proof. |

No target statement or definition used by a target changes. No module held by another
group is edited and no forced adaptation is claimed.

## Status

landed 20261014T093337-L-657923 2026-10-14 (merge of deliver/W3/Sheaf.AlgebraicGeometry.PicardModuleCechExternalCup)
