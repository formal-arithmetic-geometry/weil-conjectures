# AlgebraicGeometry.Scheme.strictHenselization_structural_ringHom_flat

## Reason

This is the explicit retirement assignment in `coord/retire-items.tsv`, row
`retire:Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`,
under the human's 2026-10-20 hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The old module has zero holes;
retiring its duplicate declaration is the repair.

The upstream theorem is fully proved. It uses `strictHenselization` and
`strictLocalizationToBase`, whereas the Sheaf copy uses the small representative
colimit `strictHenselizationRing` and `strictHenselizationStructuralMap`.
These rings are canonically isomorphic, rather than definitionally equal.
The compiled verification below proves compatibility over the base and derives
the exact old conclusion from the source theorem, without additional hypotheses.
This reconciles the retirement request with the present API difference.

There are zero active Lean importers of the Sheaf module. The four consumers
listed in the retirement row are all archived by the sync at the paths recorded
in `coord/rework.tsv`; they have not been mistaken for unused mathematics.
Their archive files, rework assignments, Lean attachments and DAG edges are
preserved. The four corresponding upstream modules are present and already
import the upstream flatness theorem. They were compiled verbatim, individually,
through `lcompile.py`: normalization finite 4.9 s, generic etale 2.5 s, purity data
4.4 s, finite etale model 4.9 s, all exit 0, no warning. Rework of an archived
consumer retains its own scope; when restored on the small-ring API it must use
the comparison argument below rather than treating the ring models as
definitionally equal.

The node `lem-sbc-affine-strict-henselization-structural-flat` now attaches to the
upstream theorem. Its statement, proof dependencies, all incoming edges and unit
membership remain unchanged. The unit route still uses the same flatness lemma.
No source-library file, target statement or definition is changed.

## Old

```lean
theorem strictHenselization_structural_ringHom_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom
```

Declared in `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`.

## New

```lean
theorem strictHenselization_structural_ringHom_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    RingHom.Flat b.hom
```

Use the existing declaration in
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`.
The Sheaf copy is withdrawn through `deleted.txt`; delivery leaves the usual empty
module stub, for the maintainer's pruning.

For reproducibility, this complete verification compiled in 3.0 s through
`lcompile.py`, with both printed axiom lists equal to
`[propext, Classical.choice, Quot.sound]`. It is a scratch check, not a new public
library declaration or a new dependency:

```lean
module

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

@[expose] public section

set_option linter.privateModule false

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_over_base
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (Scheme.smallStrictHenselizationColimitIso s).hom ≫
      Scheme.strictHenselizationStructuralMap s = Scheme.strictLocalizationToBase s := by
  classical
  let : HasColimit (Scheme.strictHenselizationDiagram s) := inferInstance
  let := (Scheme.strictHenselization_properties s).2.1
  let : (Scheme.strictHenselizationAffineInclusion s).IsEquivalence :=
    Scheme.strictHenselizationAffineInclusion_isEquivalence s
  let F := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s
  let j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s) :=
    Classical.choice (IsCofiltered.nonempty (C :=
      SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)))
  have hsmall := (Scheme.exists_strictHenselizationStructuralMap s).choose_spec j
  have hlarge := Scheme.strictHenselizationStructuralMap_eq s j
  have hleg : colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op j) ≫
      (Scheme.smallStrictHenselizationColimitIso s).hom =
      (Scheme.smallStrictHenselizationCocone s).ι.app (op j) :=
    Functor.Final.ι_colimitIso_hom F.op (Scheme.strictHenselizationDiagram s) (op j)
  change _ = Scheme.strictHenselizationStructuralMap s at hsmall
  have hleg' : Spec.map (Scheme.smallStrictHenselizationColimitIso s).hom ≫
      (Scheme.strictHenselizationCone s).π.app (op (op j)) =
      (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) := by
    change Spec.map (Scheme.smallStrictHenselizationColimitIso s).hom ≫
      Spec.map (colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op j)) =
      Spec.map ((Scheme.smallStrictHenselizationCocone s).ι.app (op j))
    rw [← Spec.map_comp, hleg]
  rw [← hsmall]
  simp only [← Category.assoc]
  rw [hleg']
  simpa only [Category.assoc] using hlarge

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem small_structural_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ Scheme.strictHenselizationRing s)
    (hb : Spec.map b = Scheme.strictHenselizationStructuralMap s) :
    RingHom.Flat b.hom := by
  let e : Scheme.strictHenselizationRing s ≅ Scheme.strictHenselization s :=
    Scheme.smallStrictHenselizationColimitIso s
  have hcomp : Spec.map (b ≫ e.hom) = Scheme.strictLocalizationToBase s := by
    rw [Spec.map_comp, hb]
    exact comparison_over_base s
  have hf := Scheme.strictHenselization_structural_ringHom_flat R s (b ≫ e.hom) hcomp
  have h := hf.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv))
  change ((b ≫ e.hom) ≫ e.inv).hom.Flat at h
  have he : (b ≫ e.hom) ≫ e.inv = b := by simp
  rw [he] at h
  exact h

#print axioms Scheme.strictHenselization_structural_ringHom_flat
#print axioms small_structural_flat

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Quarantined by the upstream sync; the archive, rework row, Lean attachment and dependency edges remain intact. Its active source counterpart already calls the replacement theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Quarantined by the upstream sync; the archive, rework row, Lean attachment and dependency edges remain intact. Its active source counterpart already calls the replacement theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Quarantined by the upstream sync; the archive, rework row, Lean attachment and dependency edges remain intact. Its active source counterpart already calls the replacement theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Quarantined by the upstream sync; the archive, rework row, Lean attachment and dependency edges remain intact. Its active source counterpart already calls the replacement theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Already imports the upstream flatness module and applies its theorem with the upstream ring and structural morphism. Recompiled verbatim; no edit. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Already imports the upstream flatness module and applies its theorem with the upstream ring and structural morphism. Recompiled verbatim; no edit. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Already imports the upstream flatness module and applies its theorem with the upstream ring and structural morphism. Recompiled verbatim; no edit. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Already imports the upstream flatness module and applies its theorem with the upstream ring and structural morphism. Recompiled verbatim; no edit. |

The parent nodes for the four archived consumers still cite
`lem-sbc-affine-strict-henselization-structural-flat`. Three additional DAG citers
(`lem-per-finite-quotient-strict-local-invariants`,
`lem-per-divisor-purity-strict-local-criterion`, and
`lem-per-etale-immediate-component-criterion`) also retain their edges: flatness
of the strict local structural map is still available from the same node.

## Status

landed 20261020T154613-L-3135954 2026-10-20 (merge of deliver/G1/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat)
