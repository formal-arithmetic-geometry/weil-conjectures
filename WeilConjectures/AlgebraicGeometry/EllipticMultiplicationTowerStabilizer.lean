/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WeaklyContractibleFiniteEtaleLift
import WeilConjectures.AlgebraicGeometry.EllipticDivisionFibreTranslation

/-! # Stabilizers of the elliptic multiplication tower -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry

/-- The stabilizer of a map into an affine weakly contractible object is killed by
any translation character supplied by the multiplication tower.

For each m, base change the finite etale surjection [r^m] along W to obtain a
covering object over W. Subcanonicity makes its representable map locally
surjective; weak contractibility gives a section. Composing with t gives a
point y_m of the generic multiplication fibre fixed by sigma. The difference
between y_m and x_m is an r^m-torsion point. This point is constant because the
kernel is finite etale over the algebraically closed ground field. Thus sigma
fixes that difference. The equivariance identity for x_m and cancellation give
zero for coordinate m of rho sigma. This holds for every m, so rho sigma is one.

Source: the counterexample paragraph, final lifting argument, in
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-elliptic-multiplication-tower-stabilizer) -/
theorem ellipticMultiplicationTowerStabilizer
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (r : ℕ) [Fact r.Prime]
    (hcovers : ∀ m : ℕ, IsFinite (𝟙 E ^ (r ^ m)).left ∧
      Etale (𝟙 E ^ (r ^ m)).left ∧ Surjective (𝟙 E ^ (r ^ m)).left)
    (ρ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
      SeparableClosure E.left.functionField) →*
        Multiplicative (IsAbelianVariety.tateModule r E))
    (x : ℕ → ((Over.map E.hom).obj
              ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E))
    (hx : (∀ m, x m ≫ (𝟙 E ^ (r ^ m)) =
              Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl))
    (heq : ∀ σ m,
              ((Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
                (Scheme.ProEt.genericPointSepAut E.left σ))) ≫ x m =
                x m * (toUnit ((Over.map E.hom).obj
                    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))) ≫
                  inv (toUnit (Scheme.specAlgebraicClosure k)) ≫
                  (((ρ σ).toAdd : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E))
                    m).toMul))
    (W : E.left.ProEt) (_hWa : IsAffine W.left)
    (hW : (Scheme.ProEt.topology E.left).IsWeaklyContractible.{u + 1} W)
    (σ : SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
      SeparableClosure E.left.functionField)
    (t : Scheme.ProEt.genericPointSep E.left ⟶ W)
    (ht : Scheme.ProEt.genericPointSepAut E.left σ ≫ t = t) : ρ σ = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext m
  have := (hcovers m).1
  have := (hcovers m).2.1
  have := (hcovers m).2.2
  obtain ⟨s, hs⟩ := weaklyContractibleFiniteEtaleLift (𝟙 E ^ (r ^ m)).left W hW
  let F := Scheme.ProEt.forget E.left ⋙ Over.map E.hom
  let yw : F.obj W ⟶ E := Over.homMk s (by
    change s ≫ E.hom = W.hom ≫ E.hom
    calc
      s ≫ E.hom = s ≫ (𝟙 E ^ (r ^ m)).left ≫ E.hom := by rw [Over.w]
      _ = W.hom ≫ E.hom := by rw [← Category.assoc, hs])
  let y := F.map t ≫ yw
  have hy : y ≫ (𝟙 E ^ (r ^ m)) =
      Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl := by
    apply Over.OverMorphism.ext
    change (t.left ≫ s) ≫ (𝟙 E ^ (r ^ m)).left = _
    rw [Category.assoc, hs]
    exact MorphismProperty.Over.w t
  have hσy : F.map (Scheme.ProEt.genericPointSepAut E.left σ) ≫ y = y := by
    change F.map (Scheme.ProEt.genericPointSepAut E.left σ) ≫ F.map t ≫ yw = _
    rw [← F.map_comp_assoc, ht]
  have ha := ellipticDivisionFibreTranslation k E (r ^ m) (x m) y (hx m) hy σ
    ((((ρ σ).toAdd : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E)) m).toMul)
    (heq σ m) hσy
  exact Additive.toMul.injective ha

end AlgebraicGeometry
