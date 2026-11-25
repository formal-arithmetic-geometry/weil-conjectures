/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleDiagonalEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective

/-!
# Propagation of diagonal formulas

A linear formula for a morphism of equivariant module presheaves, known on diagonal values over
the torsor, holds on all étale objects.

## Implementation details

Given `W`, a section `s` and a point `x` of `W ×_V c.P`, surjectivity of diagonal evaluation
provides a section `q` over the torsor with matching diagonal value. On an open neighbourhood of
`x` where `s` and the pulled-back diagonal values of `q` are constant, injectivity of diagonal
evaluation identifies the restrictions of `s` and `q`, and naturality transfers the formula.
Connectedness is not needed.

## References

* [Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- A uniform linear formula on diagonal values over the torsor propagates to
all étale objects: if `η` acts by `f` on diagonal values over the torsor, then it acts by `f`
pointwise on equivariant sections over every étale `W`. -/
theorem equivariantModulePresheaf_pointwise_of_diagonal
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N')
    (f : N.V →ₗ[ZMod ℓ] N'.V)
    (hf : letI := c.etale
      ∀ (s : c.equivariantSections ℓ N (Etale.mk c.π)) (x : c.P),
        (η.app (op (Etale.mk c.π)) s).val
            ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x) =
          f (s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x))) :
    ∀ (W : V.Etale) (s : c.equivariantSections ℓ N W) (x : c.sectionSpace W),
      (η.app (op W) s).val x = f (s.val x) := by
  classical
  let := c.etale
  intro W s x
  let Y : V.Etale := Etale.mk c.π
  let δ : c.P ⟶ c.sectionSpace Y :=
    pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl
  let a₀ : c.sectionSpace W ⟶ W.left := pullback.fst W.hom c.π
  let b₀ : c.sectionSpace W ⟶ c.P := pullback.snd W.hom c.π
  obtain ⟨q, hq⟩ := c.equivariantSections_diagonalEvaluation_surjective ℓ N (b₀ x) (s.val x)
  change q.val (δ (b₀ x)) = s.val x at hq
  let t : LocallyConstant (c.sectionSpace W) N.V :=
    LocallyConstant.comap ⟨b₀ ≫ δ, (b₀ ≫ δ).continuous⟩ q.val
  let O : (c.sectionSpace W).Opens :=
    ⟨{y | s.val y = s.val x} ∩ {y | t y = s.val x},
      (s.val.isLocallyConstant.isOpen_fiber _).inter
        (t.isLocallyConstant.isOpen_fiber _)⟩
  have hx : x ∈ O := ⟨rfl, hq⟩
  let B : c.P.Etale := Etale.mk (O.ι ≫ b₀)
  let U : V.Etale := (MorphismProperty.Over.map ⊤ c.etale).obj B
  let a : U ⟶ W := MorphismProperty.Over.homMk (O.ι ≫ a₀) (by
    change (O.ι ≫ a₀) ≫ W.hom = (O.ι ≫ b₀) ≫ c.π
    simp only [Category.assoc, a₀, b₀, pullback.condition])
  let b : U ⟶ Y := MorphismProperty.Over.homMk (O.ι ≫ b₀) (by
    rfl)
  let k : U.left ⟶ c.sectionSpace U :=
    pullback.lift (𝟙 U.left) b.left (by
      change U.hom = b.left ≫ Y.hom
      exact (MorphismProperty.Over.w b).symm)
  have ha : k ≫ c.sectionRestriction a = O.ι := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sectionRestriction, pullback.map,
        pullback.lift_fst, pullback.lift_fst_assoc, k]
      change 𝟙 O.toScheme ≫ (O.ι ≫ a₀) = O.ι ≫ a₀
      exact Category.id_comp _
    · simp [k, sectionRestriction, b, b₀]
  have hb : k ≫ c.sectionRestriction b = b.left ≫ δ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sectionRestriction, pullback.map,
        pullback.lift_fst, pullback.lift_fst_assoc, k]
      change 𝟙 U.left ≫ b.left = b.left ≫ δ ≫ pullback.fst c.π c.π
      simp only [δ, pullback.lift_fst, Category.id_comp]
      exact (Category.comp_id b.left).symm
    · simp only [Category.assoc, sectionRestriction, pullback.map,
        pullback.lift_snd, k, Category.comp_id]
      change b.left = b.left ≫ δ ≫ pullback.snd c.π c.π
      simp only [δ, pullback.lift_snd]
      exact (Category.comp_id b.left).symm
  have hs : c.equivariantRestriction ℓ N a s = c.equivariantRestriction ℓ N b q := by
    apply (c.diagonalEvaluation_bijective ℓ N B).injective
    apply LocallyConstant.ext
    intro y
    change s.val (c.sectionRestriction a (k y)) = q.val (c.sectionRestriction b (k y))
    rw [← Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, hb]
    exact y.property.1.trans y.property.2.symm
  let z : c.sectionSpace U := k ⟨x, hx⟩
  have hax : c.sectionRestriction a z = x := by
    change c.sectionRestriction a (k ⟨x, hx⟩) = x
    rw [← Scheme.Hom.comp_apply, ha]
    rfl
  have hbx : c.sectionRestriction b z = δ (b₀ x) := by
    change c.sectionRestriction b (k ⟨x, hx⟩) = δ (b₀ x)
    rw [← Scheme.Hom.comp_apply, hb]
    rfl
  have hnat {A B : V.Etale} (j : A ⟶ B) (r : c.equivariantSections ℓ N B) :
      c.equivariantRestriction ℓ N' j (η.app (op B) r) =
        η.app (op A) (c.equivariantRestriction ℓ N j r) := by
    exact (ConcreteCategory.congr_hom (η.naturality j.op) r).symm
  have he : (η.app (op W) s).val x = (η.app (op Y) q).val (δ (b₀ x)) := by
    have h := congrArg (fun r : c.equivariantSections ℓ N' U ↦ r.val z)
      ((hnat a s).trans ((congrArg (η.app (op U)) hs).trans (hnat b q).symm))
    change (η.app (op W) s).val (c.sectionRestriction a z) =
      (η.app (op Y) q).val (c.sectionRestriction b z) at h
    rwa [hax, hbx] at h
  exact he.trans ((hf q (b₀ x)).trans (congrArg f hq))

end AlgebraicGeometry.Scheme.GaloisCover
