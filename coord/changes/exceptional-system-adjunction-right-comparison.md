# Exceptional system adjunction right comparison

## Reason

The assigned theorem quantifies over every `TransportCoreData`, whose `realizeG`
is chosen independently of the two specified adjunctions and of `realizeF`.
The adjunction transport characterization proves that its equality holds exactly
for one comparison. This delivery constructs that comparison, proves its law and
uniqueness, and proves the obstruction for arbitrary nonidentity twists.
The original theorem remains unchanged and is marked `STATEMENT-DISPUTED`.

## Old

The existing field remains verbatim in `TransportCoreData`:

```lean
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
```

There was no `normalizedRealizeG`, no `TransportCoreData.normalizeRealizeG`,
and none of the seven added theorems. The original law theorem's signature
and its sole `sorry` are preserved verbatim.

## New

The item adds these fully defined constructions:

```lean
def normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  (Adjunction.rightAdjointUniq
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm)
    (operation (.integral E)).adjunction).symm

def TransportCoreData.normalizeRealizeG : TransportCoreData l Ω D hl c operation left :=
  { d with realizeG := normalizedRealizeG l Ω D hl c operation left d }

```

Both definitions use existing data explicitly; neither chooses a witness from
an unproved mere existence theorem. The uniqueness isomorphism is constructed
by `Adjunction.rightAdjointUniq` from the two given adjunctions.

The new proved theorems are `normalizedRealizeG_adjunction`,
`adjunction_law_iff_realizeG_eq`,
`TransportCoreData.normalizeRealizeG_adjunction`,
`existsUnique_system_adjunction_right_comparison`,
`not_adjunction_law_of_realizeG_ne`,
`not_forall_adjunction_law_of_realizeG_twist`, and
`not_forall_adjunction_law_of_neg_id_ne`.
Their complete signatures are recorded in the two new DAG nodes and item source.

The item adds `public import Mathlib.CategoryTheory.Adjunction.Unique` for the
explicit construction and a proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique` for its existing
`Adjunction.ofNatIsoRight_eq_iff`. No adopted source file changes.
No existing signature, definition, instance, attribute or public import changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction | G6 | New construction, seven proved theorems and dispute annotation. |
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem | unclaimed in current snapshot | Sole direct importer; existing names and signatures preserved; checked unchanged. |

The added names have no existing users. The source-only downstream scan reports
1323 transitive importers, but the only direct importer is the one listed above;
none mentions an added name. No consumer adaptation is needed.
No target statement or definition changes. The delivery tool checks related modules.

## Status

landed 20261028T034800-L-3544503 2026-10-28 (merge of deliver/G6/Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction)
