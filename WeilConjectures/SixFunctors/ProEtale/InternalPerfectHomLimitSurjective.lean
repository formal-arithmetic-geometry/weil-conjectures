/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectScalarChangeModel

import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp

/-! # Surjectivity onto compatible finite reduction morphisms

Source: Stacks Project, Tag 09C6, lemma-connected-adic-lisse; current blueprint
`sk-prop-integral-local-structure`, the displayed Milnor surjection.
(blueprint: lem-pe-internal-perfect-hom-limit-surjective)

The source complex `T = B ⊗_A P` is the existing termwise scalar model
`sfbScalarModelComplex` (the constant-sheaf scalar extension of
`det-def-sfb-constructible-local-model`, applied termwise), at the integral coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

private theorem restricted_compatible
    {C D A : Type*} [Category C] [Category D] [Category A]
    {U : D ⥤ C} {V : D ⥤ A} {J : A ⥤ D} {R : A ⥤ C}
    (b : V ⊣ J) (e : J ⋙ U ≅ R)
    {M M' : D} {N N' : A} (f : M ⟶ M') (g : N ⟶ N')
    (α : V.obj M ⟶ N) (β : V.obj M' ⟶ N')
    (h : V.map f ≫ β = α ≫ g) :
    U.map f ≫ (U.map (b.unit.app M' ≫ J.map β) ≫ e.hom.app N') =
      (U.map (b.unit.app M ≫ J.map α) ≫ e.hom.app N) ≫ R.map g := by
  have hu : f ≫ b.unit.app M' ≫ J.map β =
      b.unit.app M ≫ J.map α ≫ J.map g := by
    rw [← b.unit_naturality_assoc, ← J.map_comp, h, J.map_comp]
  calc
    _ = U.map (f ≫ b.unit.app M' ≫ J.map β) ≫ e.hom.app N' := by
      simp only [Functor.map_comp, Category.assoc]
    _ = U.map (b.unit.app M ≫ J.map α ≫ J.map g) ≫ e.hom.app N' := by rw [hu]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      have he : U.map (J.map g) ≫ e.hom.app N' = e.hom.app N ≫ R.map g := by
        simpa only [Functor.comp_map] using e.hom.naturality g
      rw [he]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1000000 in
-- Allow normalization of the continuous coefficient category and its derived adjunctions.
/--
Let `P` be a bounded complex of finite free `A`-modules, `A = O_E`, and let `T` be its
termwise canonical scalar extension `B ⊗_A P` to internal modules over `B = p_W^* A` on
an affine pro-etale object `W`. For a derived-complete `K`, every family of morphisms
`T_n → K_n` of finite reductions compatible with the quotient-associativity transitions
is the family of reductions of one morphism `T → K`.

Source: Stacks Project, Tag 09C6, lemma-connected-adic-lisse; blueprint
`sk-prop-integral-local-structure`, the displayed Milnor surjection; Stacks 0919.
(blueprint: lem-pe-internal-perfect-hom-limit-surjective)
Proof: write R_n for derived extension to A_{n,W}, U_n for restriction, and η_n
for the scalar-adjunction unit; h_n(f)=U_n(f)∘η_{T,n} is a bijection
Hom(R_nT,R_nK) ≃ Hom(T,U_nR_nK). The native scalar-tower realization identifies the
restricted transitions t_{L,n} with the canonical derived-completion transitions, so
t_{L,n}∘η_{L,n+1}=η_{L,n}. Naturality of the unit then gives t_{K,n}h_{n+1}(f) =
h_n(α_{K,n}∘(f⊗A_{n,W})∘α_{T,n}⁻¹), so a compatible family (φ_n) gives maps
a_n=h_n(φ_n) with t_{K,n}a_{n+1}=a_n. Derived completeness supplies the canonical Roos
triangle K → ∏U_nK_n → ∏U_nK_n → K[1] with projections η_{K,n}; (1-s)a=0 for the
product map a, and `Triangle.coyoneda_exact₂` gives g:T→K with η_{K,n}∘g=a_n.
Naturality and injectivity of every h_n then give R_n(g)=φ_n.
No weak-contractibility, local-constancy, or Mittag--Leffler hypothesis is used.
-/
theorem hom_limit_surjective
    (X : Scheme.{u}) (W : X.ProEt) [_hW : IsAffine W.left]
    (P : CochainComplex
      (Mod Ab.{u + 1} (scalarRingObj (DerivedNakayama.integerRing l E))) ℤ)
    (hPge : ∃ a : ℤ, P.IsStrictlyGE a)
    (hPle : ∃ b : ℤ, P.IsStrictlyLE b)
    (hPfree : ∀ i : ℤ, ∃ n : ℕ,
      Nonempty (P.X i ≅ Mod.finiteFree (scalarRingObj (DerivedNakayama.integerRing l E)) n))
    (K : DerivedCategory (Modules l E W.left))
    (hK : IsDerivedComplete l E W.left K) :
    ∀ (φ : ∀ n : ℕ,
        (derivedReduction l E W.left n).obj
            (DerivedCategory.Q.obj
              (sfbScalarModelComplex (Λ := DerivedNakayama.integerRing l E) W.left P)) ⟶
        (derivedReduction l E W.left n).obj K)
      (_hφ : ∀ n : ℕ,
        (reductionComp l E W.left n).inv.app
            (DerivedCategory.Q.obj
              (sfbScalarModelComplex (Λ := DerivedNakayama.integerRing l E) W.left P)) ≫
          (finiteExtend l E W.left n).map (φ (n + 1)) ≫
          (reductionComp l E W.left n).hom.app K = φ n),
      ∃ g : DerivedCategory.Q.obj
          (sfbScalarModelComplex (Λ := DerivedNakayama.integerRing l E) W.left P) ⟶ K,
        ∀ n : ℕ, (derivedReduction l E W.left n).map g = φ n := by
  classical
  -- Retain the original source hypotheses; the lifting works for every source object.
  have _ := hPge
  have _ := hPle
  have _ := hPfree
  intro φ hφ
  let S := W.left
  let T := DerivedCategory.Q.obj
    (sfbScalarModelComplex (Λ := DerivedNakayama.integerRing l E) S P)
  let adj (n : ℕ) := Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E S n)
  let a (n : ℕ) : T ⟶ integralLevel l E S K n := (adj n).homEquiv T _ (φ n)
  have ha (n : ℕ) : a (n + 1) ≫ integralStep l E S K n = a n := by
    let U := restrict l E S (n + 1)
    let J := finiteRestrict l E S n
    let V := finiteExtend l E S n
    let b := Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E S n)
    let e := restrictComp l E S n
    let α := reductionComp l E S n
    have hc : V.map (φ (n + 1)) ≫ α.hom.app K = α.hom.app T ≫ φ n := by
      calc
        _ = α.hom.app T ≫
            (α.inv.app T ≫ V.map (φ (n + 1)) ≫ α.hom.app K) := by simp
        _ = _ := by rw [hφ n]
    have hs : U.map (φ (n + 1)) ≫ integralStep l E S K n =
        integralStep l E S T n ≫ (restrict l E S n).map (φ n) := by
      exact restricted_compatible b e (φ (n + 1)) (φ n)
        (α.hom.app T) (α.hom.app K) hc
    change ((adj (n + 1)).unit.app T ≫ (restrict l E S (n + 1)).map (φ (n + 1))) ≫
      integralStep l E S K n = (adj n).unit.app T ≫ (restrict l E S n).map (φ n)
    rw [Category.assoc, hs, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ (restrict l E S n).map (φ n))
      (reductionUnit_compatible l E S T n)
  let : CountableAB4Star (Modules l E S) := .of_epi_π_app_zero
    (Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  let : HasCountableProducts (DerivedCategory (Modules l E S)) :=
    derivedCategory_hasCountableProducts (Modules l E S)
  obtain ⟨Q, hQ, ⟨eQ⟩, hη⟩ := hK
  obtain ⟨p, δ, htriangle, hp⟩ := roos_isDerivedLimit l E S K Q hQ eQ
  let A : T ⟶ ∏ᶜ (integralLevel l E S K) := Pi.lift a
  have hA : A ≫ towerTransitionEndomorphism (integralStep l E S K) = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [A, towerTransitionEndomorphism, towerProductShift, Category.assoc,
      Preadditive.comp_sub, Preadditive.sub_comp, Pi.lift_π,
      Pi.lift_π_assoc, Category.comp_id, ha, sub_self, zero_comp]
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ htriangle A hA
  change A = g ≫ p at hg
  let : IsIso (DerivedCategory.Q.map (augmentation l E S Q)) := hη
  let v : K ≅ DerivedCategory.Q.obj (roos l E S Q) :=
    eQ.symm ≪≫ asIso (DerivedCategory.Q.map (augmentation l E S Q))
  refine ⟨g ≫ v.inv, ?_⟩
  intro n
  apply ((adj n).homEquiv T _).injective
  rw [Adjunction.homEquiv_unit]
  have hunit : v.hom ≫ p ≫ Pi.π (integralLevel l E S K) n = (adj n).unit.app K := by
    change completionMap l E S K Q eQ ≫ p ≫ _ = _
    rw [← Category.assoc, hp, Pi.lift_π]
  rw [(adj n).unit_naturality]
  change (g ≫ v.inv) ≫ (adj n).unit.app K = a n
  rw [← hunit]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← hg]
  exact Pi.lift_π a n

end AlgebraicGeometry.ProEtale.AdicCompletion
