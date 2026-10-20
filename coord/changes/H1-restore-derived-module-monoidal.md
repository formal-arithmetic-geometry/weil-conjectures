# AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison

## Reason

Restore the assigned zero-hole module from its quarantine archive. The upstream sync
restored the original concrete tensor counits, so they are no longer definitionally equal
to the retained generic tensor counits. The archived final proof consequently fails with
a type mismatch at `isLeftDerivedFunctor₂_upperStarTensor Λ f` and at the generic lift lemma.

## Old

```lean
lemma leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison :
    letI := upperStar_preservesFlat Λ f
    leftDerivedUpperStarTensor Λ f = (f)^*⟦Λ⟧.leftDerivedTensorComparison
```

The archived proof assumed definitional equality of the concrete and generic counits.
The definitions tensorCounitOfNatTrans, homotopyTensorCounit,
homotopyTensorLeftDerivedCounit and leftDerivedTensorUnitIso had default transparency.
Its node still named `monoidal_leftDerivedUpperStar`, now declared in the upstream module.

## New

```lean
lemma leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison :
    letI := upperStar_preservesFlat Λ f
    leftDerivedUpperStarTensor Λ f = (f)^*⟦Λ⟧.leftDerivedTensorComparison
```

Preserve the public signature and all construction bodies. Mark tensorCounitOfNatTrans,
homotopyTensorCounit, homotopyTensorLeftDerivedCounit and leftDerivedTensorUnitIso
`@[irreducible]` to control costly incidental unfolding. Their local proofs explicitly
unfold them at the component equations; the existing public unit-compatibility theorem
retains its signature. The definitions stay exposed for explicit unfolding by importers.
This is a transparency change and does not change any mathematical value. Prove the concrete/generic tensor
and counit equalities in private helpers, and transport the derived-lift universal property
through these equal counits with a private congruence lemma. Reattach the existing node to this retained compatibility lemma;
the upstream monoidal instance remains imported from its original module. Private generic component identities avoid unfolding the inverse
construction at the large concrete internal-module types. Representative calculations
are performed generically, and concrete equalities use congruence. Explicit derived
witnesses reduce repeated inference. The generic lift theorem is proved directly from
the comparison's component formula and derived uniqueness, so the former private
transport helpers are removed. All stated
proof dependencies and the unit route are preserved. No upstream source is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenPullbackGenerators | quarantined; no current holder found | Its import and use of upperStar_preservesFlat retain the same public API. |

Text search in both live and quarantine trees finds this one direct importer and no
external uses of the changed proof. `tools/downstream.py` cannot index the absent live
module, so the archived importer is included explicitly. No consumer adaptation is needed.
No target statement or definition changes its meaning.

## Status

landed 20261020T153747-L-2988216 2026-10-20 (merge of deliver/H1/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal)
