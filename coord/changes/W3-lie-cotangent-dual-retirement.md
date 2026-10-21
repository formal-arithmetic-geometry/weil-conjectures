# AlgebraicGeometry.GrpObj.exists_lie_identity_cotangent_dual_equiv

## Reason

Complete the explicit retirement item in coord/retire-items.tsv (row for
Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual). This module has zero holes.
The inventory classified it DIFFERENT because the upstream construction has a
different name and supplies an explicit equivalence rather than an existential
wrapper. Its former Sheaf LieLocalDimension consumer has since been retired;
the current upstream consumer already uses the explicit equivalence directly.

## Old

```lean
theorem exists_lie_identity_cotangent_dual_equiv
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
    ∃ r : k ≃+* IsLocalRing.ResidueField R,
      letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv r
      letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
        RingHomInvPair.of_ringEquiv r.symm
      Nonempty (Lie G ≃ₛₗ[r.toRingHom]
        Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
```

The module also contains a private copy of cotangentDualScalarEquiv.

## New

Withdraw the duplicate Sheaf module using deleted.txt, and attach its existing
node to the adopted source-library construction, without changing that source:

```lean
def lieCotangentDualEquiv {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
    letI : RingHomInvPair (identityResidueEquiv G).toRingHom
        (identityResidueEquiv G).symm.toRingHom :=
      RingHomInvPair.of_ringEquiv (identityResidueEquiv G)
    letI : RingHomInvPair (identityResidueEquiv G).symm.toRingHom
        (identityResidueEquiv G).toRingHom :=
      RingHomInvPair.of_ringEquiv (identityResidueEquiv G).symm
    Lie G ≃ₛₗ[(identityResidueEquiv G).toRingHom]
      Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)
```

The canonical ring isomorphism is identityResidueEquiv G. Both declarations
use the identical universe, field, group object, identity point, local ring,
residue-field scalar structure, and RingHomInvPair instances. The old theorem
is recovered, with its signature unchanged, by the compiled proof

```lean
by
  exact ⟨identityResidueEquiv G, ⟨lieCotangentDualEquiv G⟩⟩
```

The reconstruction probe is retained only in the sandbox scratchpad. Its axiom
printout and that of lieCotangentDualEquiv contain exactly propext,
Classical.choice and Quot.sound. The unchanged upstream LieLocalDimension
consumer also compiles and has only those three axioms.

Retarget lem-ag-lie-identity-cotangent-dual to the upstream construction and
retain all three mathematical proof dependencies. Reconcile the proof text of
its only actual DAG parent, lem-ag-smooth-lie-local-dimension, with its existing
upstream proof, which already uses identityResidueEquiv and lieCotangentDualEquiv.
The parent dependency is retained. The other mentions in the tangent and residue
nodes are historical created.item and blueprint.from metadata, not dependencies.
No mathematical statement, definition, unit, unit step, or target changes.

## Users

The downstream tool reports zero current Lean importers and no other callers
of the retired declaration. Searches of lean/, quarantine/, dag/nodes/ and
dag/units/ confirm there is no hidden importer or quarantined parent. The one
DAG parent remains attached to the same node with the replacement construction.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual | W3 (this item) | Withdraw duplicate theorem and private construction; attach node upstream. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.LieLocalDimension | unclaimed | Existing parent already uses the upstream construction; no source edit. |

## Status

landed 20261021T001151-L-1379392 2026-10-21 (merge of deliver/W3/Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual)
