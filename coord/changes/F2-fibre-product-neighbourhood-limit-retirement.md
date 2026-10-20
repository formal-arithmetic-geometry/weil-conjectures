# AlgebraicGeometry.fibre_product_neighbourhood_limit

## Reason

The human-approved hand-off in coord/changes/retire-sheaf-twins-20261020.md and
row retire:Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit of
coord/retire-items.tsv require retiring the Sheaf copy in favour of its official
twin. The prerequisite Sheaf.AlgebraicGeometry.StrictHenselization has now been
retired by W4, so the earlier kept-pair import-clash reason is obsolete.

The official theorem has the same name and neighbourhood-limit conclusion.
Its vertex is strictLocalization rather than the small coordinate-ring colimit
strictHenselizationScheme. They are canonically isomorphic by
`Scheme.Spec.mapIso (Scheme.smallStrictHenselizationColimitIso s).symm.op`;
this expression was checked by Lean. A separate Lean check established
`Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
(Scheme.strictHenselizationAffineCone s).π.app (op (op j)) =
(Scheme.strictHenselizationCone s).π.app (op (op j))`
using `Functor.Final.ι_colimitIso_inv`. Thus this comparison respects the
specified affine legs as well as the vertices.
Both theorem signatures retain the same qcqs hypotheses and geometric point.

No source-library file is modified. The mathematical node statement and all
parent dependencies are preserved; its Lean attachment points at the official
theorem. The removed module is listed in deleted.txt, so normal delivery writes
the withdrawal stub. No theorem is replaced with sorry.

## Old

In Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit:

```lean
theorem fibre_product_neighbourhood_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    ∃ (p : Scheme.strictHenselizationScheme s ⟶ S)
      (q : (Functor.const (Scheme.pointSmallEtale s).fiber.Elements).obj (Over.mk p) ⟶
        CategoryOfElements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget S),
      (∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
        (q.app ((Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).obj
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              j))).left =
          (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
            (Spec (unop
              ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
                j).1.left)).isoSpec.inv) ∧
      Nonempty (IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone
        { pt := Over.mk p, π := q }))
```

## New

Use the existing declaration in
WeilConjectures.AlgebraicGeometry.FibreProductNeighbourhoodLimit:

```lean
theorem fibre_product_neighbourhood_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    ∃ (p : Scheme.strictLocalization s ⟶ S)
      (q : (Functor.const (Scheme.pointSmallEtale s).fiber.Elements).obj (Over.mk p) ⟶
        CategoryOfElements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget S),
      (∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
        (q.app ((Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).obj
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              j))).left =
          (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) ≫
            (Spec (unop
              ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
                j).1.left)).isoSpec.inv) ∧
      Nonempty (IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone
        { pt := Over.mk p, π := q }))
```

The Sheaf module has no remaining declarations.

## Users

The current import scan and tools/downstream.py report no live downstream
module. The historical sole consumer is quarantined; it does not call the
removed theorem. Its archive is preserved, as required by the quarantine rules.
No parent DAG dependency is dropped: all still reach the same mathematical node,
which now names the official theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit | F2 | Withdrawn; the mathematical node points at the official theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | quarantined, unclaimed | Historical private import only; no use of fibre_product_neighbourhood_limit. Archive preserved, and its future restoration must use the official import. No live consumer to adapt. |

## Status

landed 20261020T162540-L-3620656 2026-10-20 (merge of deliver/F2/Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit)
