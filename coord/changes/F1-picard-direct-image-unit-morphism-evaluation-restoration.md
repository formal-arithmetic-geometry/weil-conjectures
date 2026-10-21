# AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_evaluation

## Reason

Restore the complete evaluation theorem from its recorded quarantine archive.
coord/rework.tsv records a cluster-restore rollback at 5f7b33eac on 2026-10-20,
not a mathematical withdrawal. The live module is absent. Its declaration attachment
and the parent proof still require this theorem. The assigned repair is to return
this implementation to lean/; it is not a new proof-hole closure.

The archived proof compiles unchanged against the current published dependencies
in 11.9 seconds with no errors or warnings. It applies the already proved
picardAdjunctionSectionEvaluation to the ordinary pullback adjunction, uses
Mathlib's canonical structure-sheaf transpose equation, and cancels the inverse
structure-sheaf comparison and inverse Hom equivalence. The resulting restricted
evaluation is definitionally the fixed picardDirectImageSectionMap. All hypotheses
remain arbitrary: no flatness, properness, invertibility of L or nonempty scheme
assumption is added.

## Old

The live path lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismEvaluation.lean
is absent. The preserved implementation is at
quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismEvaluation.lean.
Its signature, under the existing shared derived-category parameter, is:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

theorem picardDirectImageUnitMorphism_evaluation
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (picardDirectImageUnitMorphism f L W k t ξ).val.app (Opposite.op ⊤)
        (1 : Γ(pullback f (t ≫ k), ⊤)) = picardDirectImageSectionMap f L W k t ξ
```

## New

Restore the missing Lean path byte for byte from that archive. Its signature is:

```lean
theorem picardDirectImageUnitMorphism_evaluation
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    (picardDirectImageUnitMorphism f L W k t ξ).val.app (Opposite.op ⊤)
        (1 : Γ(pullback f (t ≫ k), ⊤)) = picardDirectImageSectionMap f L W k t ξ
```

The complete proof, public import, private proof import, universe, shared parameter,
visibility, documentation and elaboration options are unchanged. The associated
node gains only a Lean restoration note; its attachment, statement, proof steps,
proof dependencies and unit route are preserved. The archive is not deleted.
No source-library declaration or target statement changes.

## Users

The prescribed tools/downstream.py --allow-missing --uses command reports no live
consumers, because the item and its consumers are quarantined. A supplementary
source scan over lean/Sheaf, lean/WeilConjectures and both quarantine roots, with
live sources taking precedence, finds one direct importer and 15 transitive
consumers in total. They are all separate quarantined rework items. Local claim
snapshots do not establish their current remote holders; none is adapted here.

The direct consumer's proof rewrites by this theorem twice (lines 129-131 of its
archive). The restored file preserves its full interface and exact proof, so those
rewrites retain the same mathematical meaning. The node
lem-sc-picard-direct-image-section-map-restriction cites this item in proof_deps
and its proof step; that dependency remains attached. An import-only scratch
consumer checks rewriting by the restored theorem through its public interface
and compiles in 2.9 seconds, after recompiling the restored module in 10.7 seconds.
The theorem's printed axioms are exactly propext, Classical.choice and Quot.sound;
there is no sorryAx. The complete quarantined parent is not compiled in this
delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction | separate quarantined rework; not adapted | Direct proof importer and declaration user; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; not adapted | Transitive importer; identical theorem, proof and interface. |

No consumer statement is weakened, strengthened or otherwise changed. No forced
adaptation is included. The independent delivery reader can compare the complete
restored source with the archive and verify the retained node and consumer route.

## Status

landed 20261021T023307-L-2945480 2026-10-21 (merge of deliver/F1/Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismEvaluation)
