/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Finite-presentation data at an inverse limit

Source: Stacks Project, Limits, Tags 01ZM, 07RP and 07RR
(blueprint: lem-weil-pbc-etale-finite-data-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite-presentation étale objects, morphisms, equalities, finite diagrams with relations,
and coverings descend along an inverse system of qcqs schemes with affine transition maps.
Source: Stacks Project, Limits, Tags 01ZM, 07RP and 07RR.
(blueprint: lem-weil-pbc-etale-finite-data-descent)

Proof:
1. Use transitivity of fibre products (`def-pc-fibre-product`) and the cone identities
   (`lem-weil-pbc-limit-affine-transition`) for base-change bookkeeping. Base change preserves
   étaleness (`lem-weil-pbc-etale-scheme-base-change`) and finite presentation
   (`lem-weil-pbc-qcqs-morphism-permanence`); morphisms between étale objects are étale
   (`lem-weil-pbc-etale-composition-cancellation`).
2. Descend a finite-presentation object by `thm-pd-spreading-out` (01ZM), then descend its
   étaleness by `lem-weil-pbc-descend-etale` (07RP), retaining finite presentation.
3. Descend morphisms and equality of morphisms by `thm-pd-spreading-out` (01ZM (2), (3)).
4. Descend finitely many objects to a common stage, then the finitely many arrows, then the
   finitely many relations. Directedness supplies each common stage. Functoriality of base
   change preserves relations and the comparison isomorphisms at every later stage.
5. For a covering, form the finite coproduct (`lem-weil-pbc-scheme-coproduct-family`);
   its map to the target is locally of finite presentation with qcqs source and target
   (`lem-weil-pbc-finite-coproduct-lfp-qcqs`). Its base change is surjective, so descend
   surjectivity by `lem-weil-pbc-descend-surjective` (07RR).
6. Surjectivity persists by `lem-weil-pbc-surjective-base-change`. The base-changed
   coprojections cover by `lem-weil-pbc-etale-covering-base-change`, hence the original
   finite family covers at every later stage (`def-weil-pbc-etale-site`).

"Étale of finite presentation" is written out as `Etale`, `LocallyOfFinitePresentation`,
`QuasiCompact` and `QuasiSeparated` of the structure morphism, and base changes as
`Over.pullback`. `Paths A` is the free category on the finite quiver of arrows; its identity
paths encode empty chains. A natural isomorphism compares all objects and generating arrows over the
base. Coverings are written as joint surjectivity of the selected incoming arrows. -/
theorem etale_finite_data_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ U : Over c.pt,
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      ∃ (i : Iᵒᵖ) (Ui : Over (D.obj i)),
        (Etale Ui.hom ∧ LocallyOfFinitePresentation Ui.hom ∧
          QuasiCompact Ui.hom ∧ QuasiSeparated Ui.hom) ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Ui ≅ U)) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V,
        ∃ (j : Iᵒᵖ) (h : j ⟶ i)
          (ψj : (Over.pullback (D.map h)).obj U ⟶ (Over.pullback (D.map h)).obj V),
          (Over.pullback (c.π.app j)).map ψj ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  V).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  U).hom ≫ ψ) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ χ : U ⟶ V, (Over.pullback (c.π.app i)).map ψ = (Over.pullback (c.π.app i)).map χ →
        ∃ (j : Iᵒᵖ) (h : j ⟶ i),
          (Over.pullback (D.map h)).map ψ = (Over.pullback (D.map h)).map χ) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (R : Type v) [Finite R] (s t : R → Paths A)
      (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt),
      (∀ a, Etale (F.obj a).hom ∧ LocallyOfFinitePresentation (F.obj a).hom ∧
        QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom) →
      (∀ r, F.map (p r) = F.map (q r)) →
        ∃ (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (α : G ⋙ Over.pullback (c.π.app i) ≅ F),
          (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
            QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) ∧
          (∀ r, G.map (p r) = G.map (q r)) ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i),
            (∀ a, Etale ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              LocallyOfFinitePresentation ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiCompact ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiSeparated ((G ⋙ Over.pullback (D.map h)).obj a).hom) ∧
            (∀ r, (G ⋙ Over.pullback (D.map h)).map (p r) =
              (G ⋙ Over.pullback (D.map h)).map (q r)) ∧
            ∀ (a b : Paths A) (f : a ⟶ b),
              ((G ⋙ Over.pullback (D.map h)) ⋙ Over.pullback (c.π.app j)).map f ≫
                  (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app b =
                (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app a ≫ F.map f) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (F : Paths A ⥤ Over c.pt)
      (α : G ⋙ Over.pullback (c.π.app i) ≅ F),
      (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
        QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) →
      ∀ (b : A) (B : Finset (Σ a : A, Quiver.Hom a b)),
        (∀ x : (F.obj b).left, ∃ e ∈ B, ∃ y : (F.obj e.1).left,
          (F.map ((Paths.of A).map e.2)).left y = x) →
        ∃ (i₁ : Iᵒᵖ) (h₁ : i₁ ⟶ i), ∀ (j : Iᵒᵖ) (h : j ⟶ i₁),
          (∀ e ∈ B,
            Etale (((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left)) ∧
          (∀ x : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj b).left,
            ∃ e ∈ B, ∃ y : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj e.1).left,
              ((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left y = x)) := by
  sorry

end AlgebraicGeometry
