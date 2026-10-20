# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_affine_unit_bijective

## Reason

The human-authorized retirement item in coord/retire-items.tsv names
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit and its existing upstream twin.
The old file has zero holes. Its theorem is already proved upstream, with the canonical
PresheafOfModules.exteriorPower replacing exteriorSheafPresheaf in its statement.
The two presheaves have definitionally identical object modules. Their restriction maps
are equal by exteriorSheafRestriction_existsUnique and exteriorPower_map_ιMulti.
This equality is proved privately in each direct consumer, allowing both consumers to
retain exactly their existing public statements and definitions while using the upstream theorem.
No source-library file or target statement is edited.

## Old

In Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit:

```lean
theorem exteriorSheaf_affine_unit_bijective {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (U : X.affineOpens) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
        (exteriorSheafPresheaf M n)).app (op U.1))
```

## New

The duplicate module is withdrawn through deleted.txt. Its existing DAG node points to
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit and its declaration:

```lean
theorem exteriorSheaf_affine_unit_bijective {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (U : X.affineOpens) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
        (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).app (op U.1))
```

Each direct consumer replaces its private import of the retired module with the upstream
module. A proved private helper unfolds the two presheaf constructions, reduces equality
to their restriction maps, and invokes uniqueness of the restriction with its pure-wedge
formula. Rewriting the presheaf argument of the sheafification unit transports the source
theorem. The quasi-coherence proof reuses that result for each affine open; the conormal
chart proof uses it in LinearEquiv.ofBijective. The remaining proofs are unchanged.

The original DAG proof dependencies still describe the upstream theorem's principal-open
localization proof. Its parent nodes now explicitly record the presheaf-equality transport.
No new mathematical result, public declaration or proof obligation is introduced.

## Users

Computed with tools/downstream.py Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit
--uses exteriorSheaf_affine_unit_bijective: nine downstream modules; only the two direct
consumers mention the theorem. Holder information was read from the current claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent | unclaimed | Replace the proof import and transport the source theorem through a private, proved presheaf equality; public signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv | unclaimed | Replace the proof import and transport the source theorem through a private, proved presheaf equality; public signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Indirect consumer; public signatures of both direct consumers stay identical, so no adaptation is needed. |

The retired item itself is the E7 assignment. No additional consumer imports it.
Both adapted files compile alone through lcompile.py (12.5 s and 9.9 s).
Their public theorem signatures compare byte-for-byte equal with the original signatures.
The overlaid import closures contain no Sheaf/upstream twin pair and no reference to the
withdrawn module. The equality proof works for every n and every scheme, so degree zero,
empty opens, and zero rings need no extra assumptions. The delivery probe checks axioms.
All target meanings and the unit route are preserved.

## Status

landed 20261020T151216-L-2647231 2026-10-20 (merge of deliver/E7/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit)
