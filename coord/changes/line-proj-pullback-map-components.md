# lineProjPullbackMap

## Reason

The original sixfold composite repeatedly expands the adjunction-based composition
isomorphism, equality transport through the tensor-pullback functor, and recursive power
comparison during kernel conversion. A direct coefficient proof times out at 200000
heartbeats / 60 seconds. Pinning the four comparison components by their equalities to
the existing canonical maps lets the generic section API specialize without expansion.
The coefficient kernel check then takes about 0.13 seconds. No source-library body changes.

Each new definition chooses from the proved singleton predicate `c = canonical_map`.
The witness is explicit and the equality theorem is proved by `Classical.choose_spec`.
There is no choice from mere unproved existence. The proved
`lineProjPullbackMap_canonical` identifies the new composite with the old one in every degree.

## Old

```lean
noncomputable def lineProjPullbackMap {W W' T T' : Scheme.{u}}
    {f : W ⟶ T} {f' : W' ⟶ T'} {h : W' ⟶ W} {g : T' ⟶ T}
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n) (n : ℕ) :
    (tensorPullback f').obj (A'.piece n) ⟶ ((tensorPullback h).obj L).tensorPow n :=
  (tensorPullback f').map (β n).hom ≫
    (tensorPullbackSectionComp f' g).inv.app (A.piece n) ≫
    (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj (A.piece n)) hsq.symm)).hom ≫
    (tensorPullbackSectionComp h f).hom.app (A.piece n) ≫
    (tensorPullback h).map (ψ n) ≫ (boundaryPullbackPowIso h L n).hom
```

## New

```lean
noncomputable def lineProjPullbackMap {W W' T T' : Scheme.{u}}
    {f : W ⟶ T} {f' : W' ⟶ T'} {h : W' ⟶ W} {g : T' ⟶ T}
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n) (n : ℕ) :
    (tensorPullback f').obj (A'.piece n) ⟶ ((tensorPullback h).obj L).tensorPow n :=
  (tensorPullback f').map (β n).hom ≫
    (lineProjCompInv f' g (A.piece n)) ≫
    lineProjSquareCast hsq.symm (A.piece n) ≫
    (lineProjCompHom h f (A.piece n)) ≫
    (tensorPullback h).map (ψ n) ≫ lineProjPowHom h L n
```

The new public component definitions are `lineProjCompHom`, `lineProjCompInv`,
`lineProjSquareCast`, and `lineProjPowHom`, all in the item module, with a definition node
`def-trf-line-proj-comparison-components`. Their private equality lemmas identify them
with the old components; `lineProjPullbackMap_canonical` combines those equalities.
All existing signatures, including the theorem statement, stay unchanged. The meanings
of target statements are preserved by the canonical-map equality; the definition change
is explicitly submitted for independent review.

## Users

`tools/downstream.py Sheaf.TraceFormula.LineProjChartPullback --uses lineProjPullbackMap`
reports zero downstream modules and one module containing uses (the item itself).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.LineProjChartPullback | T1 | Same map by the proved canonical equality; proof now uses explicit component APIs. |

No consumer adaptation is forced. Unfinished parents still cite this item and it remains
in place with its original theorem signature and its full proof.

## Status

landed 20261024T191200-L-266688 2026-10-24 (merge of deliver/T1/Sheaf.TraceFormula.LineProjChartPullback)
