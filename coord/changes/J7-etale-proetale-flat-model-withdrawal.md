# AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model

## Reason

Withdraw an obsolete auxiliary module under stage-3 step 8d. Its only former mathematical
parent, `lem-sfb-etale-proetale-scalar-pullback-cube`, now has a complete direct proof by
adjunction mates in `Sheaf.Paper.EtaleProEtaleScalarPullbackCube`. The proof and its current
DAG dependencies do not use the flat-model node. This packet includes that complete
replacement argument, corrects its stale proof docstring, and explicitly reconciles its
node with withdrawal. The unit `sk-prop-scalar-six` and the parent theorem stay intact.

The current item is present in lean/ and has no rework/quarantine row. Searches of every
active node's stmt_deps, proof_deps and proof-step uses found no parent edge. Searches of
lean/Sheaf, lean/WeilConjectures and quarantine found no external reference to its module
or ScalarCubeFlatModel namespace. No unit/chapter record mentions it. The sole textual
reference in the parent node is a historical review note, not a current dependency.

## Old

The following public theorem, with one sorry, and its 17 supporting public declarations
in `lean/Sheaf/Paper/EtaleProEtaleCubeFlatModel.lean`:

```lean
theorem simultaneous_flat_model
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      ∃ (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (p : P ⟶ K), Good Y.smallEtaleTopology A P ∧ QuasiIso p) ∧
    (∀ P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Good Y.smallEtaleTopology A P →
      Good (Scheme.ProEt.topology Y) A ((comparison A Y).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) A ((etale A f).ordinary.obj P) ∧
      Good (Y.smallEtaleTopology) B ((etaleScalar a Y).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology Y) B
        (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology X) A (((comparison A Y).comp (proetale A f)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology X) A (((etale A f).comp (comparison A X)).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) B (((etale A f).comp (etaleScalar a X)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology Y) B (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) B (((etaleScalar a Y).comp (etale B f)).ordinary.obj P) ∧
      (∀ i : Vertex, Good (Scheme.ProEt.topology X) B
        ((vertex a f i).ordinary.obj P)) ∧
      IsIso ((comparison A Y).representative P) ∧
      IsIso ((etale A f).representative P) ∧
      IsIso ((etaleScalar a Y).representative P) ∧
      IsIso ((proetaleScalar a Y).representative ((comparison A Y).ordinary.obj P)) ∧
      IsIso ((proetale A f).representative ((comparison A Y).ordinary.obj P)) ∧
      IsIso ((comparison A X).representative ((etale A f).ordinary.obj P)) ∧
      IsIso ((etaleScalar a X).representative ((etale A f).ordinary.obj P)) ∧
      IsIso ((comparison B Y).representative ((etaleScalar a Y).ordinary.obj P)) ∧
      IsIso ((etale B f).representative ((etaleScalar a Y).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((comparison A Y).comp (proetale A f)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((etale A f).comp (comparison A X)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etale A f).comp (etaleScalar a X)).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etaleScalar a Y).comp (etale B f)).ordinary.obj P)) ∧
      (∀ i : Vertex, IsIso ((vertex a f i).representative P)) ∧
      (∀ e : Face,
        derivedFace a f e (_root_.DerivedCategory.Q.obj P) ≫
            (vertex a f e.target).representative P =
          (vertex a f e.source).representative P ≫
            _root_.DerivedCategory.Q.map (ordinaryFace a f e P))) ∧
    (∀ (P P' : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (v : P ⟶ P'), Good Y.smallEtaleTopology A P → Good Y.smallEtaleTopology A P' →
      (comparison A Y).NaturalAt v ∧
      (etale A f).NaturalAt v ∧
      (etaleScalar a Y).NaturalAt v ∧
      ((comparison A Y).comp (proetaleScalar a Y)).NaturalAt v ∧
      ((comparison A Y).comp (proetale A f)).NaturalAt v ∧
      ((etale A f).comp (comparison A X)).NaturalAt v ∧
      ((etale A f).comp (etaleScalar a X)).NaturalAt v ∧
      ((etaleScalar a Y).comp (comparison B Y)).NaturalAt v ∧
      ((etaleScalar a Y).comp (etale B f)).NaturalAt v ∧
      ∀ i : Vertex, (vertex a f i).NaturalAt v)
```

Supporting declarations: Word, Word.comp, Good, etale, proetale, comparison, etaleScalar,
proetaleScalar, Vertex, Face, Face.source, Face.target, vertex, twoComplexIso,
ordinaryFace, derivedFace, Word.NaturalAt (all in the same ScalarCubeFlatModel namespace).

## New

No declarations in the withdrawn module. `deleted.txt` requests its withdrawal, and the
item node's lean attachment is explicitly null. The mathematical DAG node is preserved.
The existing parent theorem and its complete mate proof are retained verbatim; only its
proof documentation and node route explanation are reconciled. No target, source-library
module, statement, definition, attribute, or public import of any retained module changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| No downstream Lean module | none | No declaration consumer needs adaptation. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed | Included complete replacement proof; stale common-model docstring replaced by its actual mate argument; node explicitly records withdrawal of the old route. |

`tools/downstream.py` is the source-only consumer check. The direct searches also cover
quarantined consumers and the unit route, which are not inferred from zero Lean importers.

## Status

landed 20261021T134458-L-1194954 2026-10-21 (merge of deliver/J7/Sheaf.Paper.EtaleProEtaleCubeFlatModel)
