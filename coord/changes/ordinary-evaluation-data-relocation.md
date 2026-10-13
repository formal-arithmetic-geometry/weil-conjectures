# AlgebraicGeometry ordinary evaluation data

## Reason

The finite-support assembly is reduced to independently provable source, target,
and diagonal-block calculations. Their signatures need the existing ordinary
evaluation definitions, so those definitions move unchanged to OrdinaryEvaluationData
and the original module publicly reexports that module. This prevents an import cycle.
The local preadditive instance is reactivated in each proof module.

## Old

The following declarations and their bodies lived in
`Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly`:

```lean
local instance localEvaluationPreadditive {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).1

/-- The existing module category on the localized site, written in the carrier form
used by internal Hom. This is an abbreviation, not a different module category.
Source: Stacks Project, Tag 08DL
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
abbrev localEvaluationModules (X : Scheme.{u}) (U : X.Opens) :=
  SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))

/-- The structure sheaf in degree zero on the localized site.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationUnit (X : Scheme.{u}) (U : X.Opens) :
    CochainComplex (localEvaluationModules X U) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ (localEvaluationModules X U))

/-- The ordinary Hom dual, with its actual Hom-complex differential.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationDual (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :=
  homComplex (R := X.sheaf.over U) P (localEvaluationUnit X U)

/-- The total tensor with the ordinary Hom dual.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationTensor (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) :=
  CochainComplex.mapBifunctor F (localEvaluationDual X U P) (curriedTensor _)

/-- The specified product projection of the recorded Hom complex.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationProjection (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n r s : ℤ) (h : r + n = s) :
    (homComplex (R := X.sheaf.over U) P F).X n ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X s) :=
  (Classical.choose (homComplex_projections_exists (R := X.sheaf.over U))) P F n r s h

/-- The ordinary evaluation on a tensor summand, followed by a Hom projection.
It is zero unless the dual degree cancels the input degree; otherwise it sends
`y tensor phi` to `x ↦ y * phi(x)`, using the unit action on the second module.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationComponent (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) :
    F.X p ⊗ (localEvaluationDual X U P).X q ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n)) :=
  if h : r + q = 0 then
    SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _
      ((β_ (P.X r) (F.X p ⊗ (localEvaluationDual X U P).X q)).hom ≫
        (α_ (F.X p) ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _
            (𝟙_ (localEvaluationModules X U))).symm
            (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
              SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (localEvaluationModules X U))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = r + n)).hom)
  else 0

/-- A chain map has the actual ordinary evaluation formula, with the tensor ordered
as `F tensor Hom(P,O[0])`. This predicate specifies maps, not just objects.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def IsLocalOrdinaryEvaluation (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F) : Prop :=
  ∀ (p q n r : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n h ≫ f.f n ≫
      localEvaluationProjection X U P F n r (r + n) rfl =
        localEvaluationComponent X U P F p q n r h

```

## New

Exactly the same declarations, signatures, visibility and bodies live in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationData`. The original module exposes them via:

```lean
public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
```

Their existing public imports move with them and remain transitively public.
No mathematical definition or target statement changes. No other existing module
requires adaptation. The relocated definitions select exactly the same specified
Hom projections; the new finite comparisons are used only in a theorem proof and
are uniquely determined by their inclusion or projection equations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential | A3 | No signature or body change needed; existing public reexport supplies the identical declarations. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand | unclaimed | No signature or body change needed; its public import of BoundedOrdinaryEvaluationAssembly supplies the identical relocated declarations through the public reexport. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | W4 | No signature or body change needed; existing public reexport supplies the identical declarations. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | unclaimed | No signature or body change needed; existing public reexport supplies the identical declarations. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation | unclaimed | No signature or body change needed; existing public reexport supplies the identical declarations. |

## Status

landed 20261013T100012-L-2464581 2026-10-13 (merge of deliver/J2/Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly)
