# ScalarPullbackCoefficientCoherence

## Reason

The coefficient composition and identity equations concern inverse image and scalar extension for arbitrary scheme morphisms. The structure imposed IsOpenImmersion even though its defining lambda and the complete proof in words use no extension by zero. The compactification projection input needs the equations for f, which is not assumed open. Remove this unused restriction; all old open cases remain special cases. The five existing consumers listed below compiled unchanged against this generalized interface. The existing theorem retains its hole and its docstring supplies the same natural-transpose proof for arbitrary morphisms.

## Old

```lean
structure ScalarPullbackCoefficientCoherence (m : Models.{u}) where
  composition : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Q : proEtaleDerivedCategory X A),
    (scalar m ψ U).map ((lambda m φ j).inv.app Q) ≫
      (lambda m ψ j).inv.app ((scalar m φ X).obj Q) ≫
      (constantPullback (A := C) j).map ((scalarComp m φ ψ X).hom.app Q) =
    (scalarComp m φ ψ U).hom.app ((constantPullback (A := A) j).obj Q) ≫
      (lambda m (ψ.comp φ) j).inv.app Q
  identity : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Q : proEtaleDerivedCategory X A),
    (lambda m (RingHom.id A) j).inv.app Q ≫
      (constantPullback (A := A) j).map ((scalarId m A X).hom.app Q) =
    (scalarId m A U).hom.app ((constantPullback (A := A) j).obj Q)
```

## New

```lean
structure ScalarPullbackCoefficientCoherence (m : Models.{u}) where
  composition : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X)
    (Q : proEtaleDerivedCategory X A),
    (scalar m ψ U).map ((lambda m φ j).inv.app Q) ≫
      (lambda m ψ j).inv.app ((scalar m φ X).obj Q) ≫
      (constantPullback (A := C) j).map ((scalarComp m φ ψ X).hom.app Q) =
    (scalarComp m φ ψ U).hom.app ((constantPullback (A := A) j).obj Q) ≫
      (lambda m (ψ.comp φ) j).inv.app Q
  identity : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (Q : proEtaleDerivedCategory X A),
    (lambda m (RingHom.id A) j).inv.app Q ≫
      (constantPullback (A := A) j).map ((scalarId m A X).hom.app Q) =
    (scalarId m A U).hom.app ((constantPullback (A := A) j).obj Q)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Its unchanged statement uses coefficient cocycles for arbitrary f through the new coherence module. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | D7 | New input_comp and input_id specialize the repaired clauses to arbitrary f. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Existing statements unchanged; old open specializations still apply. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Existing statements unchanged; old open specializations still apply. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Existing statements unchanged; old open specializations still apply. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Existing statements unchanged; old open specializations still apply. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Existing statements unchanged; old open specializations still apply. |

## Status

landed 20261025T201645-L-2595850 2026-10-25 (merge of deliver/D7/Sheaf.Paper.ConcreteProjectionReductionSquare)
