# AlgebraicGeometry.GrpObj.exists_identity_tangent_transport

## Reason

The Sheaf existential theorem duplicates the proved upstream construction
`identityTangentTransport` and its defining equation `identityTangentTransport_val`.
The retire inventory marks it DIFFERENT only because the existential name is
absent upstream. Its only direct consumer can use the construction and equation
directly, so that difference does not require retaining a duplicate module.

## Old

```lean
theorem exists_identity_tangent_transport
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    ∃ e : infPoints G ≃ schemeTangentSpace k G.left G.hom x,
      ∀ v : infPoints G, (e v).val =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
          (infPointsEquivTangentGroup G v).val.left
```

## New

Withdraw the Sheaf module and its existential wrapper. Use the existing upstream
construction and value theorem verbatim; no upstream file is modified:

```lean
def identityTangentTransport {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    infPoints G ≃ schemeTangentSpace k G.left G.hom (unitSection G (IsLocalRing.closedPoint k)) :=
  (infPointsEquivTangentGroup G).toEquiv.trans
    (Equiv.ofBijective _ (identityTangentTransport_aux G).snd)

/-- The defining formula of `identityTangentTransport`. -/
theorem identityTangentTransport_val {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] (v : infPoints G) :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    (identityTangentTransport G v).val =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom r)) ≫
        (infPointsEquivTangentGroup G v).val.left :=
  rfl

```

In `Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv`, change only the
private proof import to the upstream transport module and replace the existential
elimination by `let e := identityTangentTransport G` and
`have he := identityTangentTransport_val G`. All existing consumer signatures,
attributes and public imports remain identical. No target statement or definition
is changed. The unit route still uses the same transport and operations results.

The transport node now attaches to the upstream construction and value theorem;
the parent node records their direct use. All their mathematical dependencies stay.

## Users

`tools/downstream.py ... --uses exists_identity_tangent_transport` lists the
retired declaration itself and its single caller. Its module-level downstream
list also includes LieCotangentDual, which imports that caller.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport | F7 (this item) | Withdraw duplicated wrapper; retarget node upstream. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv | unclaimed | Proof-only import and witness selection adapted; signature unchanged. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual | unclaimed | Transitive user; no change needed because its imported theorem is unchanged. |

There are no other Lean callers or imports of the withdrawn module, including
quarantined modules. The only DAG parent of the transport node is the adapted
LieIdentityTangentEquiv node; its dependency remains, now attached upstream.

## Status

landed 20261020T221145-L-4150425 2026-10-20 (merge of deliver/F7/Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport)
