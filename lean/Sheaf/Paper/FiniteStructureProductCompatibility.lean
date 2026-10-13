/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.FiniteStructureProductCore

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
set_option autoImplicit false
/-- The lifted product is multiplicative after every finite reduction.

Source: Stacks Project, Tags 09ZT, 088E and 088F. The proof follows the
compatibility of the finite direct-image products with base change and the
tensor comparison, then evaluates the resulting morphism identity on sections.
(blueprint: lem-weil-pbc-finite-structure-product-compatibility). -/
theorem finite_structure_product_compatibility
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) (μ : G ⊗ G ⟶ G) :
    ∀ (n : ℕ) (U : X.Opens),
      let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
        fun x ↦ (Scheme.Modules.finiteStructureAdjoint
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
      ∀ (x y : Γ(G, U)),
        a (μ.app U (tmulSection x y)) = a x * a y
 := by sorry
end AlgebraicGeometry
