# ModuleCat.exists_raw_transport

## Reason

Retire the duplicate `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport`
under the human's 2026-10-20 hand-off in
`coord/changes/retire-sheaf-twins-20261020.md` and its row in `coord/retire-items.tsv`.
The official upstream theorem already proves the transport construction without
unused scalar-extension parameters. Its existing consumer already uses that API.
The Sheaf copy has zero proof holes and zero active or quarantined Lean importers.

## Old

The withdrawn Sheaf declaration had this exact signature:

```lean
theorem exists_raw_transport
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
    let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
    let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
    let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
    let U := restrictScalars.{u} eB.toRingHom
    let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
    let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    ∀ t : V ⋙ T₀ ≅ T ⋙ U.mapHomologicalComplex (.up ℤ),
      ∃ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
        (q : S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀), True
```

## New

The node now records the official declaration in
`WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransport`:

```lean
theorem exists_raw_transport {B₀ B : Type u} [CommRing B₀] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (eB : B₀ ≃+* B) :
    let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
    let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
    let U := restrictScalars.{u} eB.toRingHom
    ∃ E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀),
      Nonempty (S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀)
```

This theorem implies the entire legacy signature without adding hypotheses or
changing its conclusion. In the context of the old declaration, the complete
replacement proof is:

```lean
by
  intros π₀ π S₀ S V U T₀ T t
  obtain ⟨E, ⟨q⟩⟩ := exists_raw_transport eB
  exact ⟨E, q, trivial⟩
```

That proof was compiled against the official import as
`scratchpad/LegacyTransportCompatibility.lean`; both declarations' axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`. The official counit
consumer was separately compiled unchanged, including its axiom check. These are
sandbox verification files, not new library declarations or modules.

The node's mathematical statement and dependency IDs stay unchanged; its Lean
attachment and proof description identify the stronger upstream theorem. The
only DAG parent is `lem-pc-derived-extension-ring-equiv-raw-counit`. Its existing
Lean attachment already points upstream, and its proof already applies
`exists_raw_transport eB`; its statement, proof route and dependencies still hold.
The unit's own statement and steps are preserved. No upstream file is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport | X2 | Withdraw the unused duplicate through deleted.txt and repoint its DAG node to the proved upstream theorem. |
| WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCounit | unclaimed | Sole current DAG parent and historical consumer's official replacement; already imports the upstream transport and uses its simplified API. Compiles unchanged, with only the three allowed axioms. |

`tools/downstream.py` reports zero modules downstream of the Sheaf module and
only its own declaration as a textual use reachable from that module. An import
scan of both active roots and `quarantine/` finds no importers. The hand-off's old
consumer `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawCounit` is absent;
its DAG node already points at the official consumer in the table. The upstream
transport's source import closure contains no Sheaf modules or duplicate twins.

## Status

landed 20261020T233234-L-909796 2026-10-20 (merge of deliver/X2/Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport)
