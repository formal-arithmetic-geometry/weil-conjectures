# AlgebraicGeometry.exists_geometric_generic_cover_model

## Reason

Retire the duplicate module listed by `coord/retire-items.tsv` under
`retire:Sheaf.AlgebraicGeometry.GeometricGenericCoverModel`.
The surviving declaration already exists in
`WeilConjectures.AlgebraicGeometry.GeometricGenericCoverModel` with an identical
statement (checked using the project's declaration parser), and its proof has
only `propext`, `Classical.choice` and `Quot.sound` as axioms.

The earlier kept-twins table warned about duplicate dependency environments.
That warning no longer applies here: every proof import of the live Sheaf module
already refers to the source library, and its only DAG parent is already realized
by `WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread`. That parent
imports the source model and applies the surviving theorem. Both were checked
in the published environment. No source-library declaration is removed or edited.

The additional Sheaf-only model-data theorem is not a consumer requirement: its
only use is the empty-index branch of the retired duplicate theorem. The source
proof handles that case using its proved private empty-fibre lemma, directly from
closed avoidance. It does not need the general model-data assertion. Update the
main node's proof and dependencies accordingly, and clear the historical helper's
Lean attachment and obsolete proof dependencies. A scan of actual DAG dependency
fields, including all proof-step uses, finds no other parent of that helper.

## Old

`Sheaf.AlgebraicGeometry.GeometricGenericCoverModel` declares:

```lean
theorem exists_geometric_generic_cover_model {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] {L : Type u} [Field L] (yη : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (S.residueField (genericPoint S)))) [IsFinite yη] [Etale yη] {I : Type u} [Finite I] (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη)) (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ) (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)), IsIrreducible ((pullback.fst (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) : ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T) (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧ (⋃ i, C i) = Set.univ ∧ (∀ i t, ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))), IsIrreducible ((pullback.fst ((pullback.snd f g).fiberToSpecResidueField t) z ≫ (pullback.snd f g).fiberι t) ⁻¹' C i)) ∧ ∀ i j, (A i ∩ A j).Nonempty → (C i ∩ C j ∩ (pullback.snd f g) ⁻¹' {η}).Nonempty
```

and the helper:

```lean
theorem exists_geometric_generic_cover_model_data {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] {L : Type u} [Field L] (yη : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (S.residueField (genericPoint S)))) [IsFinite yη] [Etale yη] {I : Type u} [Finite I] (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη)) (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ) (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)), IsIrreducible ((pullback.fst (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) : ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T) (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧ (⋃ i, C i) = Set.univ
```

The main node points to the Sheaf module and cites the model-data helper for
its empty-index branch.

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/GeometricGenericCoverModel.lean` using
`deleted.txt`. The retained source-library theorem has exactly this statement:

```lean
theorem exists_geometric_generic_cover_model {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] {L : Type u} [Field L] (yη : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (S.residueField (genericPoint S)))) [IsFinite yη] [Etale yη] {I : Type u} [Finite I] (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη)) (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ) (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)), IsIrreducible ((pullback.fst (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) : ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T) (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧ (⋃ i, C i) = Set.univ ∧ (∀ i t, ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))), IsIrreducible ((pullback.fst ((pullback.snd f g).fiberToSpecResidueField t) z ≫ (pullback.snd f g).fiberι t) ⁻¹' C i)) ∧ ∀ i j, (A i ∩ A j).Nonempty → (C i ∩ C j ∩ (pullback.snd f g) ⁻¹' {η}).Nonempty
```

Reattach `lem-sbc-geometric-generic-cover-model` to that source declaration.
For the empty-index branch record its actual closed-avoidance dependency in place
of the unused model-data helper. Set `lean` to `null` and clear obsolete proof
edges on `new-lem-sbc-geometric-generic-cover-model-data`, which is retained as a
historical node. No mathematical statement, definition or target changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GeometricGenericCoverModel | F7 | Withdraw duplicate main proof and its unused helper. |
| WeilConjectures.AlgebraicGeometry.GeometricGenericCoverModel | unclaimed; unchanged | Existing identical theorem supplies the main node; private empty-index proof replaces the old helper route. |
| WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread | unclaimed; unchanged | Only actual DAG parent of the main node; already imports and applies the retained source theorem. |

`tools/downstream.py Sheaf.AlgebraicGeometry.GeometricGenericCoverModel --uses
exists_geometric_generic_cover_model exists_geometric_generic_cover_model_data`
reports zero downstream modules. Repository and quarantine import searches find
no importer of the withdrawn module. The parent listed above needs no edit.
A dependency-field scan finds the main node is the helper's only parent and the
cover-spreading node is the main node's only parent. Other textual occurrences
are blueprint ancestry, not dependencies. No unit realization uses the helper;
`sk-prop-normal-form` has empty realized lists. The main argument and unit route
remain represented by the surviving identical theorem.

## Status

landed 20261020T233142-L-899548 2026-10-20 (merge of deliver/F7/Sheaf.AlgebraicGeometry.GeometricGenericCoverModel)
