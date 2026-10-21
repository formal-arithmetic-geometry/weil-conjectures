# continuousLattice_finite_coproduct

## Reason

Restore the complete module assigned by coord/rework.tsv after the cluster-restore
quarantine. The archived source compiles against the current library. Replace its
access to a private helper of the much broader recollement module with the existing
public full-faithfulness API for condensed module extension by zero. Both public
theorem signatures, both public imports, all constructions, and the original
finite-biproduct proof remain unchanged. No definitions or target statements change.

## Old

The live item file is absent. Its preserved source is
quarantine/Sheaf/Paper/ContinuousLatticeFiniteCoproduct.lean.
The following archived proof-only import and local fact occur in that source:

```lean
import all Sheaf.Paper.CondensedOpenClosedRecollement
```

```lean
  have := openUnitIsIso Λ (Sigma.ι Y t)
```

The local fact occurs twice, in nonempty_pull_biproduct_shriek_iso and
biproduct_shriek_counit_isIso.

## New

Restore lean/Sheaf/Paper/ContinuousLatticeFiniteCoproduct.lean with both archived
public declarations and the complete construction. Replace the above import by:

```lean
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
```

At both uses, obtain invertibility of the same adjunction unit through the public
Full and Faithful instances and the generic adjunction theorem:

```lean
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
```

Update the existing node proof and proof_deps to cite the already closed
lem-sfb-finite-extension-by-zero-fully-faithful, explaining its module-object lift.
The statement, Lean attachment, source, and unit route are preserved.

## Users

The read-only downstream.py --allow-missing --uses scan lists no live Lean consumer.
A separate scan of the quarantine finds the consumer listed below, which still
needs this item and prevents withdrawal. Its finite-affine-lattice assembly step
was compiled against the restored public interface without proof or signature changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | C2 | Restore complete zero-hole proof; replace two private-helper uses by public API. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | quarantined; no live claim found | Its use of continuousLattice_finite_coproduct_of_coefficients remains valid; no adaptation. |

## Status

landed 20261021T021005-L-2688420 2026-10-21 (merge of deliver/C2/Sheaf.Paper.ContinuousLatticeFiniteCoproduct)
