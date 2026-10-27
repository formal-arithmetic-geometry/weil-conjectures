# AlgebraicGeometry.Scheme.sections_intersection_structure_colimit

## Reason

Preflight requires a change record for added command scopes in the proof implementation.
The exported theorem statement and all six existing definitions are verbatim unchanged.
There is no semantic interface repair: the additions are a helper namespace with a local
`open`, a backward elaboration option scoped to one private theorem, and suppression of the
unused-variable lint scoped to the public theorem's inherited binder names. The private
comparison definitions are marked irreducible to avoid expanding chosen sheafifications.
All private helpers are proved. No private helper appears in an exported signature or in an
existing public definition.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

theorem sections_intersection_structure_colimit
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) :
    (∀ s : intersectionSections X U, ∃ (i : I) (a : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a = s) ∧
    (∀ (i : I) (a a' : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a =
        intersectionRestriction X U (U i) (fun x hx ↦ hx i) a' →
      ∃ (k : I) (hki : U k ≤ U i),
        X.presheaf.map (homOfLE hki).op a = X.presheaf.map (homOfLE hki).op a') ∧
    (∃ ι : intersectionOpenDiagram X U ⟶
        (Functor.const _).obj (intersectionSections X U),
      (∀ V, ι.app V = intersectionRestriction X U V.unop.val
        (fun x hx ↦ V.unop.property.elim (fun i hi ↦ hi ▸ hx i))) ∧
      Nonempty (IsColimit (Cocone.mk (intersectionSections X U) ι)) ∧
      Nonempty (IsColimit ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι))) ∧
      Nonempty (IsColimit ((CategoryTheory.forget CommRingCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι)))) ∧
    (∀ (Y : Scheme.{u}) (g : X ≅ Y) (V : I → Y.Opens)
        (hUV : ∀ i : I, U i = g.hom ⁻¹ᵁ V i),
      ∃! t : intersectionStructureSheaf Y V ⟶
          (TopCat.Sheaf.pushforward CommRingCat
            (intersectionMap g.hom U V (fun i ↦ (hUV i).le))).obj
              (intersectionStructureSheaf X U),
        (∀ W : Y.Opens,
          HEq
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion Y V)).unit.app Y.sheaf).hom.app (op W) ≫
              t.hom.app (op ((Opens.map (intersectionInclusion Y V)).obj W)))
            (g.hom.app W ≫
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion X U)).unit.app X.sheaf).hom.app
                  (op (g.hom ⁻¹ᵁ W)))) ∧
        (∀ i : I,
          intersectionRestriction Y V (V i) (fun y hy ↦ hy i) ≫
              t.hom.app (op ⊤) ≫
                (intersectionStructureSheaf X U).obj.map
                  (homOfLE (fun _ _ ↦ trivial)).op =
            g.hom.appLE (V i) (U i) (hUV i).le ≫
              intersectionRestriction X U (U i) (fun x hx ↦ hx i)))
```

## New

The following shows the added command scopes (helper bodies omitted here; all are in the
module). The theorem signature at the end is exactly the old signature.

```lean
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

-- Additional proved private helpers are grouped in this namespace:
namespace IntersectionProof
open TopCat.Sheaf
-- private definitions and theorems only
end IntersectionProof

-- Scoped only to the private assembly theorem:
set_option backward.isDefEq.respectTransparency false in
private theorem intersection_sets_sections -- proved helper

-- Scoped only to the original theorem, preserving its inherited binder names:
set_option linter.unusedVariables false in
theorem sections_intersection_structure_colimit
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) :
    (∀ s : intersectionSections X U, ∃ (i : I) (a : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a = s) ∧
    (∀ (i : I) (a a' : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a =
        intersectionRestriction X U (U i) (fun x hx ↦ hx i) a' →
      ∃ (k : I) (hki : U k ≤ U i),
        X.presheaf.map (homOfLE hki).op a = X.presheaf.map (homOfLE hki).op a') ∧
    (∃ ι : intersectionOpenDiagram X U ⟶
        (Functor.const _).obj (intersectionSections X U),
      (∀ V, ι.app V = intersectionRestriction X U V.unop.val
        (fun x hx ↦ V.unop.property.elim (fun i hi ↦ hi ▸ hx i))) ∧
      Nonempty (IsColimit (Cocone.mk (intersectionSections X U) ι)) ∧
      Nonempty (IsColimit ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι))) ∧
      Nonempty (IsColimit ((CategoryTheory.forget CommRingCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι)))) ∧
    (∀ (Y : Scheme.{u}) (g : X ≅ Y) (V : I → Y.Opens)
        (hUV : ∀ i : I, U i = g.hom ⁻¹ᵁ V i),
      ∃! t : intersectionStructureSheaf Y V ⟶
          (TopCat.Sheaf.pushforward CommRingCat
            (intersectionMap g.hom U V (fun i ↦ (hUV i).le))).obj
              (intersectionStructureSheaf X U),
        (∀ W : Y.Opens,
          HEq
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion Y V)).unit.app Y.sheaf).hom.app (op W) ≫
              t.hom.app (op ((Opens.map (intersectionInclusion Y V)).obj W)))
            (g.hom.app W ≫
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion X U)).unit.app X.sheaf).hom.app
                  (op (g.hom ⁻¹ᵁ W)))) ∧
        (∀ i : I,
          intersectionRestriction Y V (V i) (fun y hy ↦ hy i) ≫
              t.hom.app (op ⊤) ≫
                (intersectionStructureSheaf X U).obj.map
                  (homOfLE (fun _ _ ↦ trivial)).op =
            g.hom.appLE (V i) (U i) (hUV i).le ≫
              intersectionRestriction X U (U i) (fun x hx ↦ hx i)))
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.IntersectionStructureSections --uses
sections_intersection_structure_colimit` reports three declaration users: the defining module,
`IntersectionCanonicalAffineEmbedding` and `IntersectionSectionsFlatBaseChange`.
There are 47 transitive module importers; their public interface is unchanged.
No consumer requires adaptation. The consumers use the same four conclusions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntersectionStructureSections | D6 | Existing hole replaced by proof; scopes confined to helpers/theorem. |
| Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding | unclaimed in the shared claim snapshot | No change; statement and definitions remain identical. |
| Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange | unclaimed in the shared claim snapshot | No change; statement and definitions remain identical. |

## Status

landed 20261023T230633-L-3454233 2026-10-23 (merge of deliver/D6/Sheaf.AlgebraicGeometry.IntersectionStructureSections)
