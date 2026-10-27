# CategoryTheory.SectionsScalarCochain.pure

## Reason

Use equality transport on section types directly, avoiding construction and evaluation
of a categorical identity morphism each time a pure tensor occurs in the coherence
statement. This is the same sheafification-unit tensor. Equality induction on `e M`
reduces both implementations to the identical expression; the development check
`TransportPureValidation.lean` proves the original formula from the new definition.
The public signature and mathematical meaning are unchanged.

## Old

```lean
def pure {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (E : modules R ⥤ modules S) (e : ∀ M, E.obj M = SheafOfModules.changeOfRings f M)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    (E.obj M).val.obj W :=
  (eqToHom (e M).symm).val.app W
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf f M).presheaf).app W
      (a ⊗ₜ[R.obj.obj W, (f.hom.app W).hom] x))
```

## New

```lean
def pure {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)
    (E : modules R ⥤ modules S) (e : ∀ M, E.obj M = SheafOfModules.changeOfRings f M)
    (M : modules R) (W : Cᵒᵖ) (a : S.obj.obj W) (x : M.val.obj W) :
    (E.obj M).val.obj W :=
  Eq.ndrec (motive := fun N : modules S ↦ (N.val.obj W : Type r))
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf f M).presheaf).app W
      (a ⊗ₜ[R.obj.obj W, (f.hom.app W).hom] x)) (e M).symm
```

## Users

`tools/downstream.py Sheaf.Paper.SectionsScalarCochainCoherence --uses
CategoryTheory.SectionsScalarCochain.pure` reports only the item module. No downstream
Lean module requires adaptation. The definition retains the prescribed object equality
and transports in precisely its inverse direction; it makes no choice of tensor data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionsScalarCochainCoherence | J4 | Equality transport computes directly. |

## Status

landed 20261024T190135-L-3958391 2026-10-24 (merge of deliver/J4/Sheaf.Paper.SectionsScalarCochainCoherence)
