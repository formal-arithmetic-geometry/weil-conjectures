/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization

/-! # Normalized section models for affine upper-tail charts

Source: Stacks Project, Tags 01ZR and 01I6.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Object reconstruction and full faithfulness in normalized section coordinates.
Source: Stacks Project, Tag 01ZR (affine proof), and Tag 01I6.
(blueprint: lem-pc-affine-chart-normalized-section-models).

Proof: The representative of the starting class is equivalent to j in the
preorder, so its spectrum map is an isomorphism. The second projection of its
pullback chart to U(a) is therefore an isomorphism. Its inverse pullback unit on
global sections gives the additive equivalences δM and δN. The upper-tail chart
cone is limiting by upperTailChartCone_isLimit. Reindex it along the equivalence
from the antisymmetrization to the tail. All charts, including its vertex, are
affine by affine base change. Affine spectrum/global-sections duality turns this
limiting cone into a colimit of F. Identify its vertex with the direct chart by
pullback pasting. This gives ρ₀; stage pullback pasting gives ρₓ. Their equation on
the iterated chart follows from the colimit cocone equation after applying global
sections and comparing the two projections of each pasting isomorphism. Apply
quasi-coherent affine reconstruction at the starting chart, then the affine
pullback/scalar-extension identification at every stage and at the vertex.
Transport through these ring and chart isomorphisms to get e₀M,e₀N,eₓM,eₓN.
The identification is linear along ρ₀ or ρₓ, giving the four scalar equations.
The tensor-to-pullback identification sends 1 ⊗ m to the pullback unit applied to
m, giving all four normalizations with the same δM,δN. Finally the affine
quasi-coherent equivalence is fully faithful: conjugating its Hom equivalence by
these object identifications yields α and β, with the displayed coordinate
formulas. No compatibility of α and β with scalar extension of morphisms is
asserted here. This construction also covers zero modules, zero rings and empty
charts, and uses no finite-presentation assumption. -/
theorem affine_chart_normalized_section_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    (M N : (U.X a).Modules)
    (hMq : M.IsQuasicoherent)
    (hNq : N.IsQuasicoherent)
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let B : (U.X a).Modules → ModuleCat.{u} (F.obj t) := fun L ↦ by
      let k := rep.obj t
      let r := Spec.map (R.map (homOfLE k.property))
      change ModuleCat.{u} Γ(pullback r g, ⊤)
      exact ModuleCat.of _ Γ((Scheme.Modules.pullback (pullback.snd r g)).obj L, ⊤)
    let P : ModuleCat.{u} (F.obj t) := B M
    let Q : ModuleCat.{u} (F.obj t) := B N
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    ∃ (δM : (P : Type u) ≃ Γ(M, ⊤)) (δN : (Q : Type u) ≃ Γ(N, ⊤))
      (ρ₀ : ↑(colimit F) →+* Γ((U.pullback₁ q₀).X a, ⊤))
      (e₀M : (ModuleCat.extendScalars r₀).obj P ≃+
        Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M, ⊤))
      (e₀N : (ModuleCat.extendScalars r₀).obj Q ≃+
        Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N, ⊤))
      (α : ((ModuleCat.extendScalars r₀).obj P ⟶
          (ModuleCat.extendScalars r₀).obj Q) ≃
        ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N)),
      (∀ b z, e₀M (b • z) = ρ₀ b • e₀M z) ∧
      (∀ b z, e₀N (b • z) = ρ₀ b • e₀N z) ∧
      (∀ m, e₀M ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
        pullbackΓ (U.pullbackHom q₀ a) M (δM m)) ∧
      (∀ m, e₀N ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
        pullbackΓ (U.pullbackHom q₀ a) N (δN m)) ∧
      (∀ s z, (α s).app ⊤ (e₀M z) = e₀N (s z)) ∧
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        let Uk : (pullback f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := U.pullback₁ q
        let V : (pullback f (c.π.app (op i))).OpenCover.{u} := Uk.pullback₁ p
        let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
          (Uk.pullbackHom p a ≫ U.pullbackHom q a)
          (by
            dsimp only [V]
            rw [Category.assoc, U.pullbackHom_map,
              ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
        ∃ (ρₓ : ↑(F.obj x) →+* Γ((U.pullback₁ q).X a, ⊤))
          (eₓM : (ModuleCat.extendScalars r).obj P ≃+
            Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M, ⊤))
          (eₓN : (ModuleCat.extendScalars r).obj Q ≃+
            Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj N, ⊤))
          (β : ((ModuleCat.extendScalars r).obj P ⟶
              (ModuleCat.extendScalars r).obj Q) ≃
            ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
              (Scheme.Modules.pullback (U.pullbackHom q a)).obj N)),
          (∀ b z, eₓM (b • z) = ρₓ b • eₓM z) ∧
          (∀ b z, eₓN (b • z) = ρₓ b • eₓN z) ∧
          (∀ m, eₓM ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m) =
            pullbackΓ (U.pullbackHom q a) M (δM m)) ∧
          (∀ m, eₓN ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m) =
            pullbackΓ (U.pullbackHom q a) N (δN m)) ∧
          (∀ s z, (β s).app ⊤ (eₓM z) = eₓN (s z)) ∧
          IsAffine (Uk.X a) ∧
          (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) := by sorry

end AlgebraicGeometry
