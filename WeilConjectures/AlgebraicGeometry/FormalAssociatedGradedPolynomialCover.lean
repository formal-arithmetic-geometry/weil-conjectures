/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.FormalPolynomialQuotientSpan

/-! # A local polynomial cover of the associated graded ideal algebra

## References

* Stacks Project, Tag 0884
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Homogeneous polynomials in finite generators locally span the graded ideal algebra
(Stacks, Tag 0884 and Tag 087Z). -/
theorem formalAssociatedGraded_polynomial_cover
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {r : ℕ} (generators : Fin r → A) (hgenerators : Ideal.span (Set.range generators) = I)
    (G : GradedSheafAlgebra (formalAssociatedGradedPiece
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)))
    (hunit : G.unit = formalAssociatedGradedπ _ 0)
    (hmul : ∀ (m n : ℕ) (U : X.Opens)
      (a : (Scheme.idealSheafPower
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).toModulesι m).1.val.obj
          (op U))
      (b : (Scheme.idealSheafPower
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).toModulesι n).1.val.obj
          (op U)),
      ∃ c : (Scheme.idealSheafPower
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).toModulesι
          (m + n)).1.val.obj (op U),
        (Scheme.idealSheafPower _ (m + n)).2.val.app (op U) c =
          (@id Γ(X, U) ((Scheme.idealSheafPower _ m).2.val.app (op U) a)) *
            (@id Γ(X, U) ((Scheme.idealSheafPower _ n).2.val.app (op U) b)) ∧
        G.mul m n U ((formalAssociatedGradedπ _ m).val.app (op U) a)
          ((formalAssociatedGradedπ _ n).val.app (op U) b) =
            (formalAssociatedGradedπ _ (m + n)).val.app (op U) c) :
    ∃ e : ∀ (k : ℕ) (U : X.Opens),
      MvPolynomial.homogeneousSubmodule (Fin r) A k →
        (formalAssociatedGradedPiece
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) k).val.obj (op U),
      (∀ k U V (h : V ≤ U) b,
        (formalAssociatedGradedPiece _ k).val.map (homOfLE h).op (e k U b) = e k V b) ∧
      (∀ k U b b', e k U (b + b') = e k U b + e k U b') ∧
      (∀ k l U b b', G.mul k l U (e k U b) (e l U b') =
        e (k + l) U ⟨b.val * b'.val, b.property.mul b'.property⟩) ∧
      (∀ U a, e 0 U ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩ =
        G.unit.val.app (op U)
          ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a))) ∧
      (∀ (k : ℕ) (U : X.Opens) (s : ℕ)
        (a : Fin s → (formalAssociatedGradedPiece _ k).val.obj (op U))
        (y : X), y ∈ U → ∃ (W : X.Opens) (hWU : W ≤ U), y ∈ W ∧
          ∀ i, (formalAssociatedGradedPiece _ k).val.map (homOfLE hWU).op (a i) ∈
            Submodule.span Γ(X, W) (Set.range (e k W))) := by
  classical
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let ρ (U : X.Opens) : A →+* Γ(X, U) :=
    ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom).comp
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)
  let ev (U : X.Opens) : MvPolynomial (Fin r) A →+* Γ(X, U) :=
    MvPolynomial.eval₂Hom (ρ U) (fun i => ρ U (generators i))
  obtain ⟨l, hl⟩ := formalPolynomial_power_lifts I f generators hgenerators
  change ∀ k U b, (Scheme.idealSheafPower J.toModulesι k).2.val.app (op U)
    (l k U b) = ev U b.val at hl
  have hladd (k : ℕ) (U : X.Opens) (b b' :
      MvPolynomial.homogeneousSubmodule (Fin r) A k) :
      l k U (b + b') = l k U b + l k U b' := by
    apply formalPolynomial_power_injective J.toModulesι k U
    rw [map_add, hl, hl, hl]
    exact map_add (ev U) b.val b'.val
  have hev (U V : X.Opens) (h : V ≤ U) (b : MvPolynomial (Fin r) A) :
      (X.presheaf.map (homOfLE h).op).hom (ev U b) = ev V b := by
    have hρ : ((X.presheaf.map (homOfLE h).op).hom).comp (ρ U) = ρ V := by
      ext a
      change (X.presheaf.map (homOfLE h).op).hom
        ((X.presheaf.map (homOfLE le_top).op).hom _) = _
      change ((X.presheaf.map (homOfLE le_top).op ≫
        X.presheaf.map (homOfLE h).op).hom) _ = _
      rw [← X.presheaf.map_comp]
      rfl
    change (X.presheaf.map (homOfLE h).op).hom
      (MvPolynomial.eval₂Hom (ρ U) (fun i => ρ U (generators i)) b) = _
    rw [MvPolynomial.map_eval₂Hom, hρ]
    have hg : (fun i => (X.presheaf.map (homOfLE h).op).hom
        (ρ U (generators i))) = (fun i => ρ V (generators i)) := by
      funext i
      exact congrArg (fun q : A →+* Γ(X, V) => q (generators i)) hρ
    rw [hg]
  have hlnat (k : ℕ) (U V : X.Opens) (h : V ≤ U)
      (b : MvPolynomial.homogeneousSubmodule (Fin r) A k) :
      (Scheme.idealSheafPower J.toModulesι k).1.val.map (homOfLE h).op
        (l k U b) = l k V b := by
    apply formalPolynomial_power_injective J.toModulesι k V
    rw [PresheafOfModules.naturality_apply]
    change (X.presheaf.map (homOfLE h).op).hom
      ((Scheme.idealSheafPower J.toModulesι k).2.val.app (op U) (l k U b)) = _
    rw [hl, hl]
    exact hev U V h b.val
  let e := fun k U b => (formalAssociatedGradedπ J k).val.app (op U) (l k U b)
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro k U V h b
    change (formalAssociatedGradedPiece J k).val.map (homOfLE h).op
      ((formalAssociatedGradedπ J k).val.app (op U) (l k U b)) = _
    rw [← PresheafOfModules.naturality_apply]
    rw [hlnat]
  · intro k U b b'
    change (formalAssociatedGradedπ J k).val.app (op U) (l k U (b + b')) = _
    rw [hladd, map_add]
  · intro k n U b b'
    obtain ⟨c, hc, hprod⟩ := hmul k n U (l k U b) (l n U b')
    have heq : c = l (k + n) U ⟨b.val * b'.val, b.property.mul b'.property⟩ := by
      apply formalPolynomial_power_injective J.toModulesι (k + n) U
      rw [hc, hl, hl, hl]
      exact (map_mul (ev U) b.val b'.val).symm
    change G.mul k n U _ _ = _
    rw [hprod, heq]
  · intro U a
    rw [hunit]
    change (formalAssociatedGradedπ J 0).val.app (op U)
      (l 0 U ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩) = _
    congr 1
    have hc := hl 0 U ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩
    change l 0 U ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩ = _ at hc
    exact hc.trans (MvPolynomial.eval₂Hom_C (ρ U) (fun i => ρ U (generators i)) a)
  · exact formalPolynomial_quotient_span I f generators hgenerators l hl

end AlgebraicGeometry
