/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Triviality on two slices and one fibre is open in a product family

Source: Stacks Project, More on Morphisms, Lemma pic-of-product, Tag 0BF3
(blueprint: lem-sc-picard-product-open).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Triviality on the two section slices and the fibre at `s` extends to an open
neighbourhood of `s`. Source: Stacks Project, More on Morphisms, Lemma pic-of-product,
Tag 0BF3 (blueprint: lem-sc-picard-product-open).

Proof:
1. Universal pushforward applied to `Spec κ(s)` gives `H⁰(X_s, O) = κ(s)` and
   `H⁰(Y_s, O) = κ(s)`. The sections give rational points on these fibres.
   Apply the degree-one Kunneth lemma `lem-sc-picard-h1-product-injective` to obtain
   injectivity of the H¹ map induced by the two section slices.
2. The product family is flat, proper and of finite presentation by base change and
   composition. For every `T → S`, flat base change in degree zero
   (`lem-pc-flat-base-change-cohom`) gives `(pr₁)_* O = f_T^*(g_T)_* O = O`, and hence
   the product has universal structure-sheaf pushforward too. Apply
   `lem-sc-picard-h1-multiple-locus` to this family and the two slices. Their triviality
   loci are all of `S`; fibre triviality puts `s` in the product triviality locus.
   The injectivity in step 1 gives a neighbourhood on which `L` is pulled back from an
   invertible module on the base. Shrink that neighbourhood to trivialize this module.

`hO`, `hO'` say that the canonical maps `O_T → (f_T)_* O` and `O_T → (g_T)_* O` are
isomorphisms for every `T → S`, in the form of the landed Picard family
(`picard_diagonal_locally_closed`, `picard_h1_multiple_locus`): the unit of the
`tensorPullback` adjunction at the structure module. The fibre `(X ×_S Y)_s` is Mathlib's
`Scheme.Hom.fiber` of the composite `X ×_S Y → S`. -/
theorem picard_product_open
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [Flat g] [IsProper g] [LocallyOfFinitePresentation g]
    (σ : S ⟶ X) (τ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ g = 𝟙 S)
    (s : S) (L : (pullback f g).Modules) [L.IsInvertible]
    (hO : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hO' : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (h₁ :
      Nonempty ((Scheme.Modules.tensorPullback (pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ]))).obj L ≅
        SheafOfModules.unit X.ringCatSheaf))
    (h₂ :
      Nonempty ((Scheme.Modules.tensorPullback (pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ]))).obj L ≅
        SheafOfModules.unit Y.ringCatSheaf))
    (hs :
      Nonempty ((Scheme.Modules.tensorPullback ((pullback.fst f g ≫ f).fiberι s)).obj L ≅
        SheafOfModules.unit _)) :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.tensorPullback
        (pullback.fst (pullback.fst f g ≫ f) U.ι)).obj L ≅
          SheafOfModules.unit (pullback (pullback.fst f g ≫ f) U.ι).ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme
