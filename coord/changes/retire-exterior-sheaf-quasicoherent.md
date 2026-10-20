# AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine

## Reason

The retirement assignment in coord/retire-items.tsv names
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent and its upstream twin.
Both modules are already proved and contain zero holes. Their statements use two
constructions of the same exterior sheaf. Retire the duplicate theorem and migrate
its sole direct consumer without changing the consumer's public signature.

## Old

Module: Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent.

```lean
theorem isQuasicoherent_exteriorSheaf_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (exteriorSheaf M n).IsQuasicoherent
```

The direct consumer privately imports this module and applies the theorem to the
conormal module restricted to its affine inverse-image chart.

## New

The duplicate module is withdrawn through deleted.txt. The existing node
new-q1-exterior-sheaf-quasicoherent attaches to the unchanged upstream theorem in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent:

```lean
theorem isQuasicoherent_exteriorSheaf_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (exteriorPower M n).IsQuasicoherent
```

In Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections the private import
now names that upstream module. Two proved private helpers identify the constructions.
The exterior presheaves have identical object modules; uniqueness of the restriction
with its prescribed pure-wedge values proves their maps equal. Applying sheafification
to this equality gives exteriorSheaf M n = Scheme.Modules.exteriorPower M n. Rewrite
by this equality before invoking the upstream theorem in the existing proof.

The consumer's public imports, public theorem signature, and mathematical construction
are unchanged. The helper equalities hold on every scheme, for every degree, including
zero, empty opens, zero modules, and zero rings. They introduce no choice of new data.
No source-library file is edited. All target meanings and the unit route are preserved.
The two node proof descriptions are updated to match the upstream attachment and the
consumer's equality transport. Their mathematical statements and dependency sets stay.

## Users

Computed by tools/downstream.py with --uses isQuasicoherent_exteriorSheaf_of_isAffine.
All seven downstream modules are listed. Only the direct consumer mentions the theorem.
Claims were checked in coord/claims; all listed consumers were unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Indirect consumer; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Indirect consumer; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Immediate importer of the adapted consumer; public interface unchanged; compiled against it. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Replace the private import, add two proved private equalities, and rewrite before the upstream application; existing public signature preserved verbatim. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Indirect consumer; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Indirect consumer; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Indirect consumer; public interface unchanged; no adaptation. |

The item itself is the K4 retirement assignment. No other module directly imports it.
The delivery's preflight and axiom probe validate the adapted consumer. The independent
maintainer review checks this migration; the global build verifies the final landing.

## Status

landed 20261020T162313-L-3588413 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent)
