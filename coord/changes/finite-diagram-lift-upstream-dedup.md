# AlgebraicGeometry.finite_diagram_lift_of_models

## Reason

The assigned Sheaf module already contains no holes and compiles. It is listed
as a retirement item in `coord/retire-items.tsv`; the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md` requests retiring it. Its upstream twin
also proves the finite-generator and finite-relation lifting argument. The Sheaf
module has no importers, so withdraw the duplicate under brief step 8d and attach its
node to the proved upstream declaration. No source-library file is changed.

The upstream statement packages the comparison isomorphism as `Nonempty`, while the
former statement quantifies it existentially. These propositions are equivalent by
eliminating and introducing `Nonempty`; no hypothesis or mathematical clause changes.
A scratch theorem with the exact original signature compiles from the upstream theorem.

## Old

```lean
theorem finite_diagram_lift_of_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Finite A] [Quiver.{v} A]
    [Finite (Σ a b : A, Quiver.Hom a b)]
    (R : Type v) [Finite R] (s t : R → Paths A)
    (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt)
    (i : Iᵒᵖ) (V : A → Over (D.obj i))
    (hV : ∀ a, LocallyOfFinitePresentation (V a).hom ∧
      QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom)
    (α : ∀ a, (Over.pullback (c.π.app i)).obj (V a) ≅ F.obj a)
    (hR : ∀ r, F.map (p r) = F.map (q r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i) (G : Paths A ⥤ Over (D.obj j))
      (β : G ⋙ Over.pullback (c.π.app j) ≅ F),
      (∀ a, G.obj a = (Over.pullback (D.map h)).obj (V a)) ∧
      (∀ r, G.map (p r) = G.map (q r))
```

Former location: `Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels`.

## New

```lean
theorem finite_diagram_lift_of_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Finite A] [Quiver.{v} A]
    [Finite (Σ a b : A, Quiver.Hom a b)]
    (R : Type v) [Finite R] (s t : R → Paths A)
    (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt)
    (i : Iᵒᵖ) (V : A → Over (D.obj i))
    (hV : ∀ a, LocallyOfFinitePresentation (V a).hom ∧
      QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom)
    (α : ∀ a, (Over.pullback (c.π.app i)).obj (V a) ≅ F.obj a)
    (hR : ∀ r, F.map (p r) = F.map (q r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i) (G : Paths A ⥤ Over (D.obj j)),
      Nonempty (G ⋙ Over.pullback (c.π.app j) ≅ F) ∧
      (∀ a, G.obj a = (Over.pullback (D.map h)).obj (V a)) ∧
      (∀ r, G.map (p r) = G.map (q r))
```

Existing location: `WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels`.
The Sheaf file is withdrawn; it has no replacement declaration.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels --uses
AlgebraicGeometry.finite_diagram_lift_of_models` reports zero downstream modules;
its textual name search lists only the declaration in the item itself. A full Lean
source import/name search independently found no consumer of the Sheaf module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels | D6 | Withdraw unused duplicate. |
| WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels | unchanged | Existing proof supplies the node. |

No consumer adaptation or target review is required: no definitions or target types change.

## Status

landed 20261020T131948-L-1395407 2026-10-20 (merge of deliver/D6/Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels)
