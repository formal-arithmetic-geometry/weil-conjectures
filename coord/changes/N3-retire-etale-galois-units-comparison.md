# AlgebraicGeometry.Scheme.nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup

## Reason

The assigned module is listed as a retirement item in coord/retire-items.tsv.
It has zero direct holes. The adopted source now provides the stronger additive
equivalence `cohomologicalBrauerGroupAddEquivGaloisUnitsH2`. Retire the duplicate
Sheaf theorem and attach its existing DAG node to that construction.

The former conservative retirement inventory noted different transitive imports
and a different declaration name. Neither prevents this retirement: there are
currently zero importers of the item, and the exact former proposition follows
from the source construction. No consumer environment gains another import.

## Old

```lean
theorem nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup (K : Type u) [Field K] :
    Nonempty (Field.GaloisUnitsH2 K ≃ (Spec (.of K)).CohomologicalBrauerGroup)
```

This theorem was in Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison. Its proof
composed the homogeneous/inhomogeneous comparison with the etale two-cocycle
comparison. Both are unnecessary for the direct source comparison.

## New

Withdraw the Sheaf module through deleted.txt. The retained source declaration is:

```lean
noncomputable def cohomologicalBrauerGroupAddEquivGaloisUnitsH2 (K : Type u) [Field K] :
    (Spec (.of K)).CohomologicalBrauerGroup ≃+ Field.GaloisUnitsH2 K
```

The old statement follows, for exactly the old universe and hypotheses, by:

```lean
  exact ⟨(cohomologicalBrauerGroupAddEquivGaloisUnitsH2 K).symm.toEquiv⟩
```

This proof was compiled in the sandbox using the exact old declaration. Both it
and the retained source construction have only propext, Classical.choice and
Quot.sound among their axioms (4.3-second successful compilation). There are no
new holes or declarations in the delivery.

The source construction directly specializes the stalk cohomology comparison in
degree two using its equivariant units stalk identification. The node's proof
fields now describe that route. The node's mathematical statement, source, unit
and statement dependencies are unchanged. Taking the inverse and forgetting
additivity changes neither coefficient group nor hypotheses; imperfect fields,
positive characteristic and all carrier universes remain included.

## Users

`tools/downstream.py` reports zero downstream modules. Text searches of both
library roots and quarantine find no import or application outside the item.
No consumer adaptations are needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | N3 | Retire the duplicate. |

The DAG parent lem-sc-field-brauer-comparison still cites the same comparison
node. That node remains realized by the retained source equivalence; its inverse
type equivalence is exactly the bijection the parent's argument requires. The
parent has no current Lean attachment and requires no Lean adaptation. Other
occurrences in node provenance are historical ancestry, not proof dependencies.
No unit or chapter record cites the retired module or declaration. The route of
sk-thm-br is preserved.

No adopted source declaration, signature, attribute, public import or definition
body is changed. The two source consumers of the retained construction continue
to use it as before.

## Status

landed 20261021T012416-L-2186534 2026-10-21 (merge of deliver/N3/Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison)
