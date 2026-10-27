# WeilConjectures.PurCompactSupport.compactSupportProjectionCoefficientChange

## Reason

Correct the ordinary-square DAG dependency interface, without changing any Lean declaration.
The ordinary scalar/tensor and scalar/pullback maps are canonical balancing comparisons;
comparison_factorization is an already proved formal mate-pasting identity.
The generic square needs these defining maps, not integralCoefficientComparison or its
completed projection property. The old broad reference to that parent would create a DAG
cycle when the ordinary square is used to prove ordinaryCompletedSquare.
The existing definition node def-pur-integral-compact-support-coefficient-data supplies
the coefficient/restriction/mate/projection interface. The generic node now cites it alone
for this data and formal factorization. The proper/open argument and theorem are unchanged.
No target statement or definition changes meaning. No source-library module changes.

## Old

Node statement:

For coefficient systems R and S with their canonical inverse-image identifications, a compatible coefficient homomorphism a:R→S, and a fixed compactification c=(j,p) of f, ordinary derived scalar extension carries the proper-counit/open-tensor projection transformation for R to that for S under the normalized scalar/tensor, scalar/pullback and compact-support mate comparisons. This is the equality displayed in the attached Lean statement, for arbitrary unbounded K and L and arbitrary representative-normalized tensor models. No projection invertibility, quotient flatness, boundedness, completeness, or separated structure morphism is assumed. The operations and comparisons are those of [def-pur-integral-compact-support-coefficient-data] and [lem-pur-compact-support-integral-coefficient-comparison], with tensor models from [def-sfb-proetale-tensor-model].

Lean signature (unchanged):

```lean
theorem compactSupportProjectionCoefficientChange
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map Y)).map
        (((projectionMap R c aX aZ aY hR).app K).app L) ≫
      (comparison a c).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (image S c).map ((scalarTensor (a.map X) aX bX).hom.app
        (K, (pull R f).obj L) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))) =
    (scalarTensor (a.map Y) aY bY).hom.app ((image R c).obj K, L) ≫
      bY.tensor.map (Prod.mkHom ((comparison a c).app K) (𝟙 _)) ≫
      (((projectionMap S c bX bZ bY hS).app
        ((pbcDerivedExtend (a.map X)).obj K)).app
          ((pbcDerivedExtend (a.map Y)).obj L))
```

## New

Node statement:

For coefficient systems R and S with their canonical inverse-image identifications, a compatible coefficient homomorphism a:R→S, and a fixed compactification c=(j,p) of f, ordinary derived scalar extension carries the proper-counit/open-tensor projection transformation for R to that for S under the normalized scalar/tensor, scalar/pullback and compact-support mate comparisons. This is the equality displayed in the attached Lean statement, for arbitrary unbounded K and L and arbitrary representative-normalized tensor models. No projection invertibility, quotient flatness, boundedness, completeness, or separated structure morphism is assumed. The operations and comparisons are those of [def-pur-integral-compact-support-coefficient-data], with tensor models from [def-sfb-proetale-tensor-model]. The scalar/tensor and scalar/pullback comparisons are the canonical derived balancing comparisons, and the support comparison is the mate of coefficient restriction; no invertibility or normalization theorem for a finite field extension is used.

Lean signature (unchanged):

```lean
theorem compactSupportProjectionCoefficientChange
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map Y)).map
        (((projectionMap R c aX aZ aY hR).app K).app L) ≫
      (comparison a c).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (image S c).map ((scalarTensor (a.map X) aX bX).hom.app
        (K, (pull R f).obj L) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))) =
    (scalarTensor (a.map Y) aY bY).hom.app ((image R c).obj K, L) ≫
      bY.tensor.map (Prod.mkHom ((comparison a c).app K) (𝟙 _)) ≫
      (((projectionMap S c bX bZ bY hS).app
        ((pbcDerivedExtend (a.map X)).obj K)).app
          ((pbcDerivedExtend (a.map Y)).obj L))
```

## Users

The read-only downstream.py --uses audit finds the generic module and
Sheaf.Paper.ConcreteIntegralProjectionCone. The new consumer is listed too.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed | Node-only dependency clarification; Lean signature and proof unchanged. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Identical theorem application; no Lean adaptation or semantic change. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | N4 | New proof-only import and proof of ordinaryCompletedSquare. |

The only existing DAG citer, lem-sf-concrete-integral-projection-cone, still holds:
it uses the identical ordinary coefficient square. This audit is also recorded in
statement_change. No forced adaptation of another group's module occurs.

## Status

landed 20261025T211324-L-3933735 2026-10-25 (merge of deliver/N4/Sheaf.Paper.CompactSupportScalarProjectionIdentification)
