# principalTorsorLocalization

## Reason

The normalized Ext types repeatedly expanded the closed term of the open--closed sequence.
The declaration-only diagnostic took 25.4 seconds; naming that term reduced it to 18.5 seconds.
Cache the actual closed term as `principalTorsorClosedTerm` and use it in the same sequence.
The construction draft verified by reflexivity that the new sequence equals the old one.
There is no change to any existing signature or to the mathematical object.
The existing comparison definitions move to `PrincipalTorsorSignTypes`, publicly re-exported
by the assigned module, to permit the four independent comparison statements without a cycle.

Repair of returned head `25917ab2861`: the Users table below includes all four comparison
modules, including `PrincipalTorsorNormalizedNatural`. The correction is incorporated in this
delivery. If a reviewer supplies a further change-record override through `--apply-fixes`,
the required flat fix filename is `principal-torsor-localization-cache.change.md`; the
repository path remains `coord/changes/principal-torsor-localization-cache.md`.
The prior override used the repository basename without `.change`, causing the landing failure.
This packet already contains the corrected Users table; land this record directly without
an `--apply-fixes` override for it.

## Old

```lean
def principalTorsorLocalization {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h)
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
```

## New

```lean
def principalTorsorClosedTerm {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
    (disjoint_range_of_range_eq_compl W.ι i h)
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).X₃

/-- The published localization sequence on the integral constant sheaf. Its end terms
are canonically `j_! Z_W` and `i_* Z_Z`, by constant inverse-image comparison.
Source: Stacks Tag 0A45 (blueprint: lem-pur-principal-torsor-yoneda-sign). -/
def principalTorsorLocalization {T Z : Scheme.{u}} (i : Z ⟶ T)
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  let L :=
    openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
      (disjoint_range_of_range_eq_compl W.ι i h)
      ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  { X₁ := L.X₁
    X₂ := L.X₂
    X₃ := principalTorsorClosedTerm i W h
    f := L.f
    g := L.g
    zero := L.zero }
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PrincipalTorsorYonedaSign | E2 | Re-export the existing interface and prove the signed splice from the four comparison statements. |
| Sheaf.AlgebraicGeometry.PrincipalTorsorSignTypes | unclaimed, new | Own the relocated interfaces and cached closed term. |
| Sheaf.AlgebraicGeometry.PrincipalTorsorNormalizedComparison | unclaimed, new | State the independent normalized construction. |
| Sheaf.AlgebraicGeometry.PrincipalTorsorConnectingComparison | unclaimed, new | State coefficient connecting compatibility. |
| Sheaf.AlgebraicGeometry.PrincipalTorsorFramedComparison | unclaimed, new | State the framed-extension relative cocycle calculation. |
| Sheaf.AlgebraicGeometry.PrincipalTorsorNormalizedNatural | unclaimed, new | State naturality of normalized comparisons. |

`tools/downstream.py` and textual declaration searches found no current Lean consumers outside
this module. The DAG parents and the unit route remain attached to the unchanged statement.
No target statement or its mathematical meaning changes.

## Status

landed 20261023T151833-L-415865 2026-10-23 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PrincipalTorsorYonedaSign)
