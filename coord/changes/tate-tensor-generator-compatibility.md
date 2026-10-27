# AlgebraicGeometry.Scheme.PurityIntegralTower.GeneratorCompatible

## Reason

The degree-zero, degree-one and tensor-step lemmas must share the existing predicate without importing their caller. Move it to a definition-only module and publicly re-export it from its original module. The name, type, visibility, universes, body, and quantifier order are unchanged. No target meaning changes.

## Old

```lean
def GeneratorCompatible
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (n d : ℕ) (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶
      quotientLine T ell n d) : Prop :=
      ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
        (v : W.unop ⟶ (toProEt T).obj U.unop)
        (a : coefficient ell (n + 1))
        (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (n + 1))).obj.obj U)
        (x : Fin d → (purTwistZlOne T ell).obj.obj W),
        (∀ i : Fin d, finiteTateLimitRootValue ell T n W (x i) =
          Units.map v.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T (ell ^ (n + 1)) U (z i))) →
        f.val.app W
            (1 • (@id (((realization T ell n).obj (finiteSheaf T ell n d)).val.obj W)
              ((toSheafify (ProEt.topology T)
              ((finiteSheaf T ell n d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
              ((finiteSheaf T ell n d).obj.map v.op
                (((ProEtale.comparisonAdjunction
                  (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).unit.app
                    (finiteEtaleTateTwist T (ell ^ (n + 1))
                      (coefficient ell (n + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
                  (finiteTateEtalePowerGenerator T _ (ell ^ (n + 1))
                    (CharP.cast_eq_zero _ _) U a d z)))))) =
          pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n)
            (integralLine T ell d) W (((scalars T ell n).app W).hom a)
              (integralGenerator T ell W d x)
```

## New

The identical definition is in `Sheaf.Paper.TateTensorGeneratorCompatibility`; the original module publicly imports it.

```lean
def GeneratorCompatible
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (n d : ℕ) (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶
      quotientLine T ell n d) : Prop :=
      ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
        (v : W.unop ⟶ (toProEt T).obj U.unop)
        (a : coefficient ell (n + 1))
        (z : Fin d → (T.rootsOfUnitySheaf (ell ^ (n + 1))).obj.obj U)
        (x : Fin d → (purTwistZlOne T ell).obj.obj W),
        (∀ i : Fin d, finiteTateLimitRootValue ell T n W (x i) =
          Units.map v.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T (ell ^ (n + 1)) U (z i))) →
        f.val.app W
            (1 • (@id (((realization T ell n).obj (finiteSheaf T ell n d)).val.obj W)
              ((toSheafify (ProEt.topology T)
              ((finiteSheaf T ell n d).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
              ((finiteSheaf T ell n d).obj.map v.op
                (((ProEtale.comparisonAdjunction
                  (ModuleCat.{u + 1} (coefficient ell (n + 1))) T).unit.app
                    (finiteEtaleTateTwist T (ell ^ (n + 1))
                      (coefficient ell (n + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
                  (finiteTateEtalePowerGenerator T _ (ell ^ (n + 1))
                    (CharP.cast_eq_zero _ _) U a d z)))))) =
          pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n)
            (integralLine T ell d) W (((scalars T ell n).app W).hom a)
              (integralGenerator T ell W d x)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TateTensorGeneratorMap | F3 | Definition moved and publicly re-exported; theorem signature unchanged. |
| Sheaf.Paper.TateTensorGeneratorIsIso | current server claim checked by delivery | Unchanged; receives the identical predicate through the same import. |

The unchanged direct importer was copied temporarily, compiled against this packet in import order (6.8 seconds), and removed from the sandbox. It will also be checked by deliver3.py. No adaptation is needed.

## Status

landed 20261027T233926-L-4137735 2026-10-27 (merge of deliver/F3/Sheaf.Paper.TateTensorGeneratorMap)
