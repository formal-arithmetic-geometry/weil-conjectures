# refinementLowerStarId

## Reason

Specify the already inferred source and target module objects in `Mod.isoMk` explicitly.
Unfolding inference at the coherence calculation caused elaboration to exceed the single-file
budget in exploratory proofs. These arguments pin down the same module objects without
changing the isomorphism, the elaborated type, its components, or any theorem statement.
The naturality statement receives the same explicit arguments so both constructions agree
without expensive inference. No definition has proof data supplied by a new choice.

## Old

```lean
def refinementLowerStarId (X : Scheme.{u}) : lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
      (refinementLowerStarId_linear Λ X M))
    (fun v ↦ refinementLowerStarId_naturality Λ X v)


theorem refinementLowerStarId_naturality (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (v : M ⟶ N) :
    (lowerStar Λ (𝟙 X)).map v ≫
        (Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app N.X)
          (refinementLowerStarId_linear Λ X N)).hom =
      (Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
          (refinementLowerStarId_linear Λ X M)).hom ≫ v
```

## New

```lean
def refinementLowerStarId (X : Scheme.{u}) : lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj M) (N := M)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
      (refinementLowerStarId_linear Λ X M))
    (fun v ↦ refinementLowerStarId_naturality Λ X v)


theorem refinementLowerStarId_naturality (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (v : M ⟶ N) :
    (lowerStar Λ (𝟙 X)).map v ≫
        (Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj N) (N := N)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app N.X)
          (refinementLowerStarId_linear Λ X N)).hom =
      (Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj M) (N := M)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
          (refinementLowerStarId_linear Λ X M)).hom ≫ v
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Same term with implicit arguments made explicit; no semantic change. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Original consumer compiles unchanged against the delivered module (13.5 seconds). |

`tools/downstream.py Sheaf.Paper.CompactificationRefinementLocalizing --uses refinementLowerStarId`
found these two textual users. There are 253 downstream modules in total; their statement
meanings are unchanged because the definition and its type are definitionally the same.
A separate scratch check compiled in 21.0 seconds: `rfl` proves equality with the old
`NatIso.ofComponents` definition verbatim, and the new naturality theorem proves the old
unannotated type directly. No consumer adaptation is included. The definition's node is the unchanged refinement node;
this delivery updates only its proof description. No target signature or meaning changes.

## Status

landed 20261020T051352-L-1655069 2026-10-20 (merge of deliver/H3/Sheaf.Paper.CompactificationRefinementLocalizing)
