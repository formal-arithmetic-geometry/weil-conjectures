# AlgebraicGeometry.GrpObj.exists_lie_identity_tangent_linearEquiv

## Reason

Complete the retirement listed in coord/retire-items.tsv. The assigned Sheaf
module contains zero holes. Its existential theorem is a duplicate wrapper
around the already proved upstream construction lieIdentityTangentEquiv, which
has the identical field universe, group-object hypotheses, identity point,
structural residue map, and Module.compHom scalar action. The inventory's
DIFFERENT classification records only the absent existential declaration name.

## Old

```lean
theorem exists_lie_identity_tangent_linearEquiv
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    letI : Module k (schemeTangentSpace k G.left G.hom x) :=
      Module.compHom (schemeTangentSpace k G.left G.hom x) r
    Nonempty (Lie G ≃ₗ[k] schemeTangentSpace k G.left G.hom x)
```

The sole direct consumer imports the Sheaf module privately and obtains the
witness with `obtain ⟨E⟩ := exists_lie_identity_tangent_linearEquiv G`.

## New

Withdraw the duplicate Sheaf module through deleted.txt. Use this existing
upstream construction without modifying any source-library file:

```lean
def lieIdentityTangentEquiv {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    letI : Module k (schemeTangentSpace k G.left G.hom x) :=
      Module.compHom (schemeTangentSpace k G.left G.hom x) r
    Lie G ≃ₗ[k] schemeTangentSpace k G.left G.hom x
```

In Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual replace only its private
import by WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
and the witness-elimination line by `let E := lieIdentityTangentEquiv G`.
All public signatures, public imports, attributes and docstrings remain verbatim.
No target statement or public definition changes. The old Nonempty statement
follows immediately by introducing this explicit equivalence as its witness.

Retarget lem-ag-lie-identity-tangent-equiv to the upstream construction and its
apply theorem; record the consumer's direct use in its parent node. All three
proof dependencies of the tangent-equivalence node remain: Lie.Ring,
identityTangentTransport and identity_tangent_transport_operations. The
cotangent-dual node retains its dependencies unchanged. The unit sk-i-cartier
and its realized lists are unchanged; no mathematical step is bypassed.

## Users

The downstream tool finds exactly one downstream module, which is also the only
caller of the retired existential theorem. Searches of lean/, quarantine/,
dag/nodes/ and dag/units/ find no other caller, import or node attachment that
must be migrated. The only mathematical DAG parent is the cotangent-dual node;
it remains a parent of the same tangent-equivalence node, now attached upstream.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv | B5 (this item) | Withdraw duplicate existential wrapper and attach its node upstream. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual | unclaimed | Replace private proof import and select the upstream equivalence directly; public interface unchanged. |

The original consumer would import an empty withdrawn module and refer to the
removed exists_lie_identity_tangent_linearEquiv declaration, so both changed
lines are necessary. No source-tree declaration is removed or changed.

Validation: the adapted consumer compiles cleanly through lcompile.py. An
additional probe prints exactly propext, Classical.choice and Quot.sound for
both lieIdentityTangentEquiv and exists_lie_identity_cotangent_dual_equiv.

## Status

landed 20261020T233053-L-889724 2026-10-20 (merge of deliver/B5/Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv)
