# CategoryTheory.diagramRingRestrictionPushforward proof-local instance scope

## Reason

Server preflight requested a change record because its interface scan detects the
new `section`, `end`, and `attribute [local instance]` commands. These commands
scope proved private caches for standard sheaf instances. They do not export an
instance or change a public declaration. The section ends before the existing
public theorem, and the theorem uses these caches only inside its proof.

All four existing public definitions and all public imports remain verbatim.
The theorem signature is identical to the original. No consumer needs adaptation.
No target statement, ring construction, or derived-category definition changes.

## Old

There was no private proof-helper section and no private instance-cache registration.
The public theorem signature was:

```lean
theorem diagramRingRestrictionPushforward
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (SX : Sheaf K RingCat.{u}) (SY : Sheaf L RingCat.{u})
    (hSX : ∀ (U : Cᵒᵖ) (a b : SX.obj.obj U), a * b = b * a)
    (hSY : ∀ (U : Dᵒᵖ) (a b : SY.obj.obj U), a * b = b * a)
    (BX : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    (BY : Sheaf (diagramSiteTopology J D L) RingCat.{u})
    (hBX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (hBY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : BY.obj.obj U), a * b = b * a)
    (aX : diagramSiteRing J C K SX ⟶ BX) (aY : diagramSiteRing J D L SY ⟶ BY)
    (s : RingedToposMorphism SX SY)
    (fB : RingedToposMorphism BX BY)
    (fS : RingedToposMorphism (diagramSiteRing J C K SX) (diagramSiteRing J D L SY))
    (hInvB : fB.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hInvS : fS.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hDirB : fB.direct = diagramCoefficientDirect J C D K L s.direct)
    (hDirS : fS.direct = diagramCoefficientDirect J C D K L s.direct)
    (hAdjB : HEq fB.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hAdjS : HEq fS.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hStructuralS : ∀ (j : J) (U : C),
      HEq (fS.ringMap.hom.app (Opposite.op (Opposite.op j, U)))
        (s.ringMap.hom.app (Opposite.op U)))
    (hRing : fB.inverse.map ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).map aY) ≫ fB.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).obj (diagramSiteRing J D L SY)))
        (hInvB.trans hInvS.symm)) ≫ fS.ringMap ≫
      (sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY))] :
    ∃ (rX : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)))
      (rY : DerivedCategory.{w} (ringedSiteModules.{u} BY) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
        (SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
        (SheafOfModules.restrictScalars.{u} aY).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (RB : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} BY))
      (RS : DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (etaB : fB.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RB)
      (etaS : fS.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RS),
      RB.IsRightDerivedFunctor etaB
        (HomologicalComplex.quasiIso (ringedSiteModules.{u} BX) (ComplexShape.up ℤ)) ∧
      RS.IsRightDerivedFunctor etaS (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} (diagramSiteRing J C K SX)) (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} BX) ℤ,
        I.IsKInjective → IsIso (etaB.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ℤ,
        I.IsKInjective → IsIso (etaS.app I)) ∧
      ∃! c : fB.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
          SheafOfModules.restrictScalars.{u} aX ⋙ fS.modules,
        (∀ M : ringedSiteModules.{u} BX,
          (diagramCoefficientUnderlying (diagramSiteRing J D L SY)).map (c.hom.app M) ≫
              fS.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
            fB.underlying.hom.app M ≫
              eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M))
                (hDirB.trans hDirS.symm))) ∧
        ∃! kappa : RB ⋙ rY ≅ rX ⋙ RS,
          ∀ M : CochainComplex (ringedSiteModules.{u} BX) ℤ,
            phiY.inv.app ((fB.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
                rY.map (etaB.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
              DerivedCategory.Q.{w}.map
                  ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app M) ≫
                etaS.app
                  (((SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj M) ≫ RS.map (phiX.inv.app M)
```

## New

The same public theorem signature is retained verbatim:

```lean
theorem diagramRingRestrictionPushforward
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (SX : Sheaf K RingCat.{u}) (SY : Sheaf L RingCat.{u})
    (hSX : ∀ (U : Cᵒᵖ) (a b : SX.obj.obj U), a * b = b * a)
    (hSY : ∀ (U : Dᵒᵖ) (a b : SY.obj.obj U), a * b = b * a)
    (BX : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    (BY : Sheaf (diagramSiteTopology J D L) RingCat.{u})
    (hBX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (hBY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : BY.obj.obj U), a * b = b * a)
    (aX : diagramSiteRing J C K SX ⟶ BX) (aY : diagramSiteRing J D L SY ⟶ BY)
    (s : RingedToposMorphism SX SY)
    (fB : RingedToposMorphism BX BY)
    (fS : RingedToposMorphism (diagramSiteRing J C K SX) (diagramSiteRing J D L SY))
    (hInvB : fB.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hInvS : fS.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hDirB : fB.direct = diagramCoefficientDirect J C D K L s.direct)
    (hDirS : fS.direct = diagramCoefficientDirect J C D K L s.direct)
    (hAdjB : HEq fB.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hAdjS : HEq fS.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hStructuralS : ∀ (j : J) (U : C),
      HEq (fS.ringMap.hom.app (Opposite.op (Opposite.op j, U)))
        (s.ringMap.hom.app (Opposite.op U)))
    (hRing : fB.inverse.map ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).map aY) ≫ fB.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).obj (diagramSiteRing J D L SY)))
        (hInvB.trans hInvS.symm)) ≫ fS.ringMap ≫
      (sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY))] :
    ∃ (rX : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)))
      (rY : DerivedCategory.{w} (ringedSiteModules.{u} BY) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
        (SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
        (SheafOfModules.restrictScalars.{u} aY).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (RB : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} BY))
      (RS : DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (etaB : fB.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RB)
      (etaS : fS.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RS),
      RB.IsRightDerivedFunctor etaB
        (HomologicalComplex.quasiIso (ringedSiteModules.{u} BX) (ComplexShape.up ℤ)) ∧
      RS.IsRightDerivedFunctor etaS (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} (diagramSiteRing J C K SX)) (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} BX) ℤ,
        I.IsKInjective → IsIso (etaB.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ℤ,
        I.IsKInjective → IsIso (etaS.app I)) ∧
      ∃! c : fB.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
          SheafOfModules.restrictScalars.{u} aX ⋙ fS.modules,
        (∀ M : ringedSiteModules.{u} BX,
          (diagramCoefficientUnderlying (diagramSiteRing J D L SY)).map (c.hom.app M) ≫
              fS.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
            fB.underlying.hom.app M ≫
              eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M))
                (hDirB.trans hDirS.symm))) ∧
        ∃! kappa : RB ⋙ rY ≅ rX ⋙ RS,
          ∀ M : CochainComplex (ringedSiteModules.{u} BX) ℤ,
            phiY.inv.app ((fB.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
                rY.map (etaB.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
              DerivedCategory.Q.{w}.map
                  ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app M) ≫
                etaS.app
                  (((SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj M) ≫ RS.map (phiX.inv.app M)
```

The added command scope, entirely before this theorem, is:

```lean
section

-- Private proved cache theorems and private proved helpers are declared here.
attribute [local instance] coefficientRingCompose coefficientAddCompose coefficientSheafify
  coefficientLocallyBijective

end
```

The private caches prove the standard `HasSheafCompose` instances for rings and
abelian groups, `HasSheafify` for abelian groups, and `WEqualsLocallyBijective` for
abelian groups. Only their local registration is new; each proof is `inferInstance`.
These are propositions. No private helper occurs in a public signature or in any
existing public definition body.

The declaration-scoped unused-variable linter option retains the original `hBY`
and `hStructuralS` binders, which the more general argument does not need.
Transparency options affect elaboration within this module. They introduce no
public instance, notation, variable, or attribute.

## Users

`tools/downstream.py Sheaf.CategoryTheory.DiagramRingRestrictionPushforward --uses
 diagramRingRestrictionPushforward diagramCoefficientInverse diagramCoefficientDirect
 diagramCoefficientAdjunction diagramCoefficientUnderlying` reports zero downstream
modules. Its five declaration searches find only the item module itself. This is
not a withdrawal: the existing DAG attachment and statement dependencies remain.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DiagramRingRestrictionPushforward | G2 | Complete its proof; public interface unchanged. |

There are no adapted modules and no forced adaptations.

## Status

landed 20261021T101040-L-1750 2026-10-21 (merge of deliver/G2/Sheaf.CategoryTheory.DiagramRingRestrictionPushforward)
