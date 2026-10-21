# Integral twist comparison definitions

## Reason

Move the four comparison definitions verbatim to a public definition module so the
geometric conjunction can be stated independently without importing its parent theorem.

## Old

In Sheaf.Paper.IntegralTwistBaseChange:

```lean
/-- Forget only the module structure of the published signed integral twist line.
Source: twist-power and internal-Hom clauses of the coefficient-twist blueprint
(blueprint: lem-weil-integral-twist-base-change). -/
abbrev integralTwistUnderlying (S : Scheme.{u}) (m : ℤ) :=
  (SheafOfModules.toSheaf _).obj (integralTwistLine l E S m)

/-- The underlying additive sheaf map of the canonical signed scalar map.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def integralTwistScalarUnderlying (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (m : ℤ) :
    integralTwistUnderlying l E S m ⟶ integralTwistUnderlying l F S m :=
  ⟨(PresheafOfModules.toPresheaf _).map (twistScalarMaps l E S F ι m).val⟩

/-- A local section transported along an inverse-image comparison, via its adjunct.
This uses source sections only at source objects and target sections at their base changes.
Source: scheme naturality in the final sentence of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def integralTwistInverseSection {X Y : Scheme.{u}} (h : X ⟶ Y)
    (ρ : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (integralTwistUnderlying l E Y m) ≅ integralTwistUnderlying l E X m)
    (m : ℤ) (V : Y.ProEtᵒᵖ) (x : (integralTwistLine l E Y m).val.obj V) :
    (integralTwistLine l E X m).val.obj ((proEtaleBaseChange h).op.obj V) :=
  (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _)
    (ρ m).hom).hom.app V x

/-- Normalization of the signed inverse-image identifications: unit, root tensor,
completed scalar action, positive powers, and dual evaluation. These are the canonical
pullback comparisons, rather than arbitrary isomorphisms of rank-one sheaves.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`, and the
Integral twist paragraph of `sk-prop-sfb-cartesian-coefficients-twists.proof.md`
(blueprint: lem-weil-integral-twist-base-change). -/
def IsIntegralTwistInverseComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X)
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (ρ : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (integralTwistUnderlying l E Y m) ≅ integralTwistUnderlying l E X m) : Prop :=
  (∀ (V : Y.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V),
    integralTwistInverseSection l E h ρ 0 V a =
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) ∧
  IsPurIntegralTwistComparison h l E α τ (ρ 1).hom ∧
  (∀ (m : ℤ) (V : Y.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V)
      (x : (integralTwistLine l E Y m).val.obj V),
    integralTwistInverseSection l E h ρ m V (a • x) =
      @id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj
        ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) •
          integralTwistInverseSection l E h ρ m V x) ∧
  (∀ (n : ℕ) (V : Y.ProEtᵒᵖ)
      (x : (integralTwistLine l E Y (Int.ofNat (n + 1))).val.obj V)
      (y : (integralTwistLine l E Y 1).val.obj V),
    integralTwistInverseSection l E h ρ (Int.ofNat (n + 2)) V
        (SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted l E Y) _ _ V x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E X) _ _
        ((proEtaleBaseChange h).op.obj V)
        (integralTwistInverseSection l E h ρ (Int.ofNat (n + 1)) V x)
        (integralTwistInverseSection l E h ρ 1 V y)) ∧
  ∀ (n : ℕ) (V : Y.ProEtᵒᵖ)
      (f : (integralTwistLine l E Y (Int.negSucc n)).val.obj V)
      (x : (integralTwistLine l E Y (Int.ofNat (n + 1))).val.obj V),
    ((integralTwistInverseSection l E h ρ (Int.negSucc n) V f).app
        (op (Over.mk (𝟙 ((proEtaleBaseChange h).op.obj V).unop))))
        (integralTwistInverseSection l E h ρ (Int.ofNat (n + 1)) V x) =
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V
        ((f.app (op (Over.mk (𝟙 V.unop)))) x)
```

## New

The identical declarations, signatures and bodies are in
Sheaf.Paper.IntegralTwistBaseChangeDefinitions, publicly imported by their original module.
No mathematical definition, statement or target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | unchanged; same public names and definitions |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | unchanged; same public names and definitions |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | unchanged; same public names and definitions |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | claimed | unchanged; same public names and definitions |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | unchanged; same public names and definitions |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | public import preserves API |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | new | receives identical definitions |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | new | states geometric clause |

## Status

landed 20261021T203629-L-3846235 2026-10-21 (merge of deliver/J4/Sheaf.Paper.IntegralTwistBaseChange)
