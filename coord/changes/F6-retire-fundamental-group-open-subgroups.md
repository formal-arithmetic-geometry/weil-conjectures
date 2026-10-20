# AlgebraicGeometry.Scheme.FiniteEtale.connected_cover_open_subgroups

## Reason

Retire the duplicate Sheaf module under the human's 2026-10-20 hand-off,
coord/changes/retire-sheaf-twins-20261020.md and its coord/retire-items.tsv row.
The item already has zero holes. The actual repair replaces the two current
private consumer imports and the DAG attachment, and withdraws the duplicate.

The twin is not textually identical: it uses a small fundamental-group model,
IsSepClosed rather than IsAlgClosed, and IsConnected rather than scheme
ConnectedSpace. Basic.exists_isFundamentalGroup and toAutContinuousMulEquiv
provide the canonical topological group comparison with Aut(fiber s), compatibly
with evaluation. FundamentalGroup.Connected proves the two connectedness notions
agree. Upstream exists_iso_fiber_map_eq_iff is the pointed criterion;
nonempty_iso_iff gives conjugacy by a translated fibre point, equivalent to the
old g⁻¹hg formula by mul_smul and inv_smul_eq_iff.

The upstream index formula uses Nat.card of the fibre, not the scheme's rank.
Preserve the latter as the proved new lemma below, reusing the retiring module's
private degree proof and generalizing IsAlgClosed to IsSepClosed. Its proof uses
only proved library/Mathlib results. No proof is replaced by sorry, and no data
is selected from a merely existential unproved theorem.

## Old

The two current consumers had this proof-only import:

```lean
import Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
```

The retired public declaration had this signature (verbatim):

```lean
theorem connected_cover_open_subgroups
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    (∀ (P : Y.FiniteEtale), ConnectedSpace P.obj.left →
      ∀ p : (fiber s).obj P,
        IsOpen (MulAction.stabilizer (Aut (fiber s)) p : Set (Aut (fiber s))) ∧
        P.obj.hom.IsFiniteLocallyFreeOfDegree
          (MulAction.stabilizer (Aut (fiber s)) p).index) ∧
    (∀ H : Subgroup (Aut (fiber s)), IsOpen (H : Set (Aut (fiber s))) →
      ∃ (P : Y.FiniteEtale), ConnectedSpace P.obj.left ∧
        ∃ p : (fiber s).obj P, MulAction.stabilizer (Aut (fiber s)) p = H) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        (∃ e : P ≅ Q, (fiber s).map e.hom p = q) ↔
          MulAction.stabilizer (Aut (fiber s)) p = MulAction.stabilizer (Aut (fiber s)) q) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        Nonempty (P ≅ Q) ↔ ∃ g : Aut (fiber s),
          ∀ h : Aut (fiber s),
            h ∈ MulAction.stabilizer (Aut (fiber s)) p ↔
              g⁻¹ * h * g ∈ MulAction.stabilizer (Aut (fiber s)) q)
```

## New

The two current consumers instead have this proof-only import:

```lean
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
```

The classification node attaches to upstream galois_openSubgroups, with
exists_iso_fiber_map_eq_iff and exists_isConnected_stabilizer_eq recorded as
supporting declarations. No consumer calls connected_cover_open_subgroups.
The cover-degree comparison remains available to the lisse consumer through:

```lean
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberCardDegree
```

That new module publicly states (verbatim):

```lean
theorem isFiniteLocallyFreeOfDegree_index_stabilizer
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (P : Y.FiniteEtale) [IsConnected P] (p : (fiber s).obj P) :
    P.obj.hom.IsFiniteLocallyFreeOfDegree (MulAction.stabilizer G p).index
```

It has a proved private degree_eq_fiber_card helper and a complete orbit-stabilizer
proof of this public statement. Its node is lem-fet-geometric-fiber-degree.
The original item is absent from the sandbox and listed in deleted.txt; the
launcher represents its withdrawal by an empty module. No upstream signature,
attribute, public import or non-theorem body changes. No target is edited.

## Users

Complete source downstream.py closure (23 modules), plus the archived consumer.
The retired name has no source users outside its own declaration. Only two
current consumers need source edits; both compile individually. The other
modules retain their existing signatures and definitions. The retired module
only contributed one public theorem and four public imports, with no public
instances or elaboration attributes. The remaining dependency declarations used
by these consumers are available from their retained imports and the twin.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LisseTrivializedFiniteEtale | unclaimed | Private proof import switched to the official classification; also imports the proved degree-index lemma for its existing proof plan. Signature and proof unchanged. |
| TargetsCheck | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Only the private proof import switched to the official classification. Every declaration, proof body and public import retained verbatim. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.Statement | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No use of the retired theorem name; unchanged declarations and public imports. |
| Sheaf.Paper.DenseOpenPiOneSurjective (quarantined) | unclaimed; separate rework item | Archive retained verbatim; no call to the retired theorem. Its future rework must replace the archived private import with the official twin, as recorded in the classification node note. |

The quarantined parent is deliberately not restored, withdrawn or edited by this
packet: its rework row records an unrelated missing dependency. Its mathematical
proof dependencies, statement and Lean attachment are preserved. Its references
to cor-galois-open-subgroups now resolve via the updated node to the official twin.

## Status

landed 20261020T221142-L-4149887 2026-10-20 (merge of deliver/F6/Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups)
