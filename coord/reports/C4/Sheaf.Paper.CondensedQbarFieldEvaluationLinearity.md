## What changed

The original module now proves `condensedQbar_field_evaluation_linear` from the coefficient-only square. Private proved helpers establish tensor compatibility of the specified comparison, compatibility with the internal action, and the explicit scalar-action formulas for both field fibers. The public signature is unchanged.

Added `Sheaf.Paper.CondensedQbarFieldPointCoefficientValue`, with a complete proof of singleton normalization. It constructs constant bounded functions using their finite generated intermediate fields, computes the terminal coefficient inverse, and applies `globalCoefficientIso_test` and naturality. No data is chosen from an unproved existence theorem.

Added `Sheaf.Paper.CondensedQbarFieldCoefficientSquare` for the remaining coefficient-only equation. Its proof plan uses the proved normalization. This is strictly a part of the original argument: it has no module parameter and makes no assertion about module actions.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.condensedQbar_field_evaluation_linear` by a decomposition. All module-action and tensor calculations in its module are proved.

Proved `AlgebraicGeometry.ProEtale.condensedQbar_field_point_coefficient_value` (node `lem-weil-pbc-condensed-qbar-field-point-coefficient-value`), with zero holes in that module.

Added one hole: `AlgebraicGeometry.ProEtale.condensedQbar_field_coefficient_square` (node `lem-weil-pbc-condensed-qbar-field-coefficient-square`). This is the only sorry in the delivery. It still needs the composed-adjunction unit identity in the specified geometric interfaces, followed by the singleton evaluation-coherence square and cancellation. The normalization of both endpoint values is already proved. The scalar square is checked in words for identity embeddings, zero scalars, and arbitrary transcendental embeddings; no algebraicity hypothesis is needed.

Counts: one old hole closed, one new hole added, net zero holes closed. This is a decomposition, not a complete proof of the original obligation. The additional singleton-normalization theorem is fully proved.

## No longer needed

Removed the direct import `Sheaf.Paper.ProfinitePointPullback` from the original module;
it is already publicly imported by `Sheaf.Paper.GeometricFieldProEtaleEvaluation`.
No globally reachable nodes/modules are pruned. The original node's direct proof dependency
on `lem-weil-pbc-profinite-point-pullback` moves to the coefficient-square node. It remains
needed for that square and is not counted as pruning. Both original public imports remain
necessary. The new proof-only import of `PushforwardMonoidal` supplies the tensor calculation.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no existing definition or public signature was changed. The dry-run checker groups Loogle and LeanFinder as one search kind and also requires LeanSearch; a separate recorded LeanSearch was added. The numbered plan is mathematically usable. The module-action part and the bounded-function normalization were implemented and compiled; the remaining composition of the point and scheme adjunction interfaces was not completed. Scratch work includes a proved generic scheme-adjunction pasting identity, but its specialization and the complete coefficient square were not brought into a checked final proof. These attempts are not claimed as delivered results.

For the next reader, the following generic pasting helper was checked in scratch with the same imports, universe, opens, and namespace as the delivered modules. It is not a delivered library declaration. Its specialization to the point adjunction and the final coefficient-square assembly remain open; neither is claimed as checked by this snippet.

```lean
private theorem scheme_unit_pasting {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hfg : f ≫ g = k)
    (P : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (U : Z.ProEt) :
    ((upperStarLowerStarAdjunction Ab g).unit.app P).hom.app (op U) ≫
      ((upperStarLowerStarAdjunction Ab f).unit.app ((upperStar Ab g).obj P)).hom.app
        (op ((Scheme.proEtaleBaseChange g).obj U)) ≫
      ((upperStar Ab f).obj ((upperStar Ab g).obj P)).obj.map
        ((MorphismProperty.Over.pullbackComp f g k hfg.symm).hom.app U).op ≫
      (((upperStarComp Ab f g).inv.app P) ≫
        (eqToHom (congrArg (upperStar Ab) hfg)).app P).hom.app
          (op ((Scheme.proEtaleBaseChange k).obj U)) =
    ((upperStarLowerStarAdjunction Ab k).unit.app P).hom.app (op U) := by
  subst k
  have h := unit_conjugateEquiv_symm
    (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} f))
    (lowerStarComp Ab.{u + 1} f g).inv P
  have hh := congrArg (fun a ↦ a.hom.app (op U)) h
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, lowerStarComp_inv_app_hom_app, Category.assoc] at hh
  let B := (upperStar Ab f).obj ((upperStar Ab g).obj P)
  let C := (upperStar Ab (f ≫ g)).obj P
  let α := (upperStarComp Ab f g).inv.app P
  let s := (MorphismProperty.Over.pullbackComp f g).hom.app U
  have hn := α.hom.naturality s.op
  change B.obj.map s.op ≫ α.hom.app _ = α.hom.app _ ≫ C.obj.map s.op at hn
  change _ ≫ _ ≫ B.obj.map s.op ≫ α.hom.app _ = _
  rw [hn]
  change _ ≫ _ ≫ α.hom.app _ ≫ C.obj.map s.op = _
  change ((upperStarLowerStarAdjunction Ab (f ≫ g)).unit.app P).hom.app (op U) ≫
    C.obj.map ((MorphismProperty.Over.pullbackComp f g).inv.app U).op =
      ((upperStarLowerStarAdjunction Ab g).unit.app P).hom.app (op U) ≫
      ((upperStarLowerStarAdjunction Ab f).unit.app ((upperStar Ab g).obj P)).hom.app
        (op ((Scheme.proEtaleBaseChange g).obj U)) ≫
      α.hom.app (op ((Scheme.proEtaleBaseChange f).obj
        ((Scheme.proEtaleBaseChange g).obj U))) at hh
  erw [← reassoc_of% hh]
  rw [← C.obj.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id]
  erw [C.obj.map_id, Category.comp_id]
```

## New nodes

`lem-weil-pbc-condensed-qbar-field-point-coefficient-value` records the proved singleton-normalization step in its own module. It depends on the existing coefficient construction and geometric field interfaces.

`lem-weil-pbc-condensed-qbar-field-coefficient-square` records the coefficient-only part still open. Its source and full proof in words are in the theorem docstring and node. Its plan uses the proved singleton normalization and the existing point-pullback and field-evaluation coherence. No change records or forced adaptations are required.

## Second reading by C4

1. I compared the delivered evaluation-linearity module with the repository version. The
   public theorem signature is byte-for-byte unchanged; the added modules and DAG entries are
   declared in this report, with no accidental changes to existing declarations. Verdict: pass.

2. I compiled all three sandbox modules with `lcompile.py --all`. The two completed modules
   compile without errors or warnings, and the only remaining `sorry` is the named theorem
   `condensedQbar_field_coefficient_square`; there are no forbidden declarations or hollow
   definitions. Scratch copies with `#print axioms` for every delivered declaration show
   only `propext`, `Classical.choice`, and `Quot.sound` for all helpers and the normalization
   theorem; the square and target additionally have precisely the expected `sorryAx`.
   Verdict: pass subject to the explicitly documented split hole.

3. I checked the split statements against the definitions and searched the Lean sources for
   existing declarations. The point-normalization theorem is fully proved and the coefficient
   square is a strictly smaller coefficient-only statement, with matching docstrings and DAG
   nodes. Independent LeanFinder searches for scalar-action naturality and composed-unit
   compatibility found only general Mathlib tools, including `unit_conjugateEquiv_symm`,
   not the specified geometric square. Neither duplicates an existing library theorem.
   Verdict: pass.

4. I traced the proof from the target downward. The target uses the tensor/action helpers and
   the coefficient square; the coefficient square retains the point-pullback dependency and
   the unit route. The imports are minimal for the delivered proofs, and no reachable module
   or node is pruned. Verdict: pass.

5. I checked the `proof`, `proof_deps`, `proof_origin`, `lean` records, and unit/chapter fields
   of the three DAG nodes against the Lean proofs and declarations. The target node keeps its
   unit and its unchanged statement; the two new nodes are marked `split` with complete source
   and proof descriptions. Verdict: pass.

I changed only the report: I added this second-reading record and explicitly named the
removed direct `ProfinitePointPullback` import under `## No longer needed`. No Lean proof,
statement, definition, import, or DAG node required repair.
