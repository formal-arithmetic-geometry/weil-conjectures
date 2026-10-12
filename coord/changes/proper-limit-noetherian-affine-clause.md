# AlgebraicGeometry.proper_limit_noetherian_affine_clause

## Reason

The universal assertion about arbitrary supplied systems is false: the constant singleton
system Spec ℚ has affine limit but its stage ring is not finite type over ℤ. Stacks
Tag 0A0P chooses affine approximations before forming the proper models. We follow that
construction instead. No Challenge declaration or definition changes.

## Old

```lean
theorem proper_limit_noetherian_affine_clause
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : IsAffine S)
    (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
    (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
    (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
    (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss)
    (hlimX : Nonempty (IsLimit (Cone.mk X πX)))
    (hlimS : Nonempty (IsLimit (Cone.mk S πS))) :
    (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
      RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
      Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op))
```

## New

```lean
theorem proper_limit_noetherian_affine_clause
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] (hS : IsAffine S) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
      (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
      (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss),
      Nonempty (IsLimit (Cone.mk X πX)) ∧ Nonempty (IsLimit (Cone.mk S πS)) ∧
      (∀ (i j : Λᵒᵖ) (a : i ⟶ j),
        IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
      (∀ i : Λᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Λᵒᵖ,
        LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
          QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
      (∀ i : Λᵒᵖ, πX.app i ≫ fs.app i = f ≫ πS.app i) ∧
      (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
        RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
      Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperLimitNoetherian | unclaimed | Proof branches on IsAffine S and selects the appropriate construction; statement unchanged. |

The only direct use of the declaration is the row above (checked with rg over lean/).
Transitive importers retain the same public theorem and definitions. No target meaning
changes. The corrected intermediate is not a Challenge target.

### Forced proof adaptation

The original ProperLimitNoetherian proof fails against the corrected clause at
line 86 with `Function expected at proper_limit_noetherian_affine_clause f hS`,
because it applies an existential result to the formerly supplied index type Λ.
Only its proof body (original lines 80--86) is replaced: branch on IsAffine S,
choose the affine construction in the affirmative branch, and choose the existing
core in the negative branch. The latter branch discharges the conditional affine
conclusion from the negative hypothesis. The adapted module compiles. The original
compiles against the baseline, as independently checked by deliver3.py. Signatures,
visibility and imports stay identical. No other module needs a forced adaptation:
the caller exports the identical statement and neither proof helper is re-exported.

## Status

landed 20261012T135319-L-1693699 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.ProperLimitNoetherianCore)
