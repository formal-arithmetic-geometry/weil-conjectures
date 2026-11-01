/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedCore
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Localization.Opposite

/-! # Exactness of the localized integral dual

Source: blueprint thm-coef-rational-verdier, paragraph 2
(blueprint: lem-coef-rational-verdier-localized-exact). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

private theorem square_of_heq {C : Type*} [Category* C]
    {X X' Y Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f ≫ eqToHom hy = eqToHom hx ≫ g := by
  cases hx; cases hy; cases h
  simp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Exactness of the fixed rational internal Hom from exactness of its integral
restriction. This is only the shift-and-triangle descent step; no biduality,
completion comparison, symmetry, or evaluation is included.
Source: blueprint thm-coef-rational-verdier, paragraph 2, and the image-triangle
construction of def-weil-rationalization-karoubi
(blueprint: lem-coef-rational-verdier-localized-exact).

Proof: restrict the given ambient shift comparison to the integral constructible
subcategory, using preservation for the dual and shift stability of that subcategory.
Its naturality is inherited from the ambient comparison. Localize both the comparison
and its inverse; on pure tensors the comparison square is its integral square times
the scalar, and additivity extends it to every arrow. Conjugate with the recorded
localization shift comparisons, including the opposite shift convention, to obtain
the rational dual's CommShift. Every distinguished triangle in the specified rational
category is isomorphic to the image of an integral distinguished triangle. The same
holds for the opposite category using its signed reversed-triangle construction.
For an integral triangle, the hypothesis makes its dual triangle distinguished in
the ambient category, and preservation puts all its vertices in the full integral
constructible subcategory. Its inherited triangulation detects distinguishedness.
Apply the exact localization functor. The pure-tensor and object equations of
localizedDual identify this with the displayed rational dual triangle. Transport
along the original triangle isomorphism and use closure under isomorphism. This also
handles zero objects and triangles killed by scalar localization. -/
theorem localizedDual_exact (w : sfIntegralConstructibleCategory l E X)
    (hp : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.obj).obj (op K.obj)))
    (hex : ∃ s : (IntegralVerdier.dual l E X w.obj).CommShift ℤ,
      ∀ T : Triangle (IntegralVerdier.Ambient l E X)ᵒᵖ,
        sfIntegralConstructible l E X T.obj₁.unop →
        sfIntegralConstructible l E X T.obj₂.unop →
        sfIntegralConstructible l E X T.obj₃.unop →
        T ∈ distTriang (IntegralVerdier.Ambient l E X)ᵒᵖ →
        Triangle.mk ((IntegralVerdier.dual l E X w.obj).map T.mor₁)
          ((IntegralVerdier.dual l E X w.obj).map T.mor₂)
          ((IntegralVerdier.dual l E X w.obj).map T.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (IntegralVerdier.Ambient l E X)) :
    ∃ s : (localizedDual l E X w hp).CommShift ℤ,
      ∀ T : Triangle (sfRationalConstructibleCategory l E X)ᵒᵖ,
        T ∈ distTriang (sfRationalConstructibleCategory l E X)ᵒᵖ →
        Triangle.mk ((localizedDual l E X w hp).map T.mor₁)
          ((localizedDual l E X w hp).map T.mor₂)
          ((localizedDual l E X w hp).map T.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (sfRationalConstructibleCategory l E X)  := by
  classical
  let I := (sfIntegralConstructible l E X).ι
  let U := IntegralVerdier.restrictedDual l E X w.obj hp
  let V := IntegralVerdier.dual l E X w.obj
  obtain ⟨s, hs⟩ := hex
  let : V.CommShift ℤ := s
  let ei : U ⋙ I ≅ I.op ⋙ V := Iso.refl _
  let : U.CommShift ℤ := Functor.CommShift.ofComp ei ℤ
  have : NatTrans.CommShift ei.hom ℤ := Functor.CommShift.ofComp_compatibility ei ℤ
  have hU : U.IsTriangulated := by
    constructor
    intro T hT
    apply (I.map_distinguished_iff _).mp
    have ht := hs (I.op.mapTriangle.obj T) T.obj₁.unop.property
      T.obj₂.unop.property T.obj₃.unop.property (I.op.map_distinguished T hT)
    have ht' : (I.op ⋙ V).mapTriangle.obj T ∈ distTriang (IntegralVerdier.Ambient l E X) :=
      isomorphic_distinguished _ ht _ ((Functor.mapTriangleCompIso I.op V).app T)
    have ht'' := isomorphic_distinguished _ ht' _ ((Functor.mapTriangleIso ei).app T)
    exact isomorphic_distinguished _ ht'' _ ((Functor.mapTriangleCompIso U I).symm.app T)
  let Q := sfRationalConstructibleLocalization l E X
  let F := localizedDual l E X w hp
  obtain ⟨ho, ha, _, hm⟩ := localizedDual_spec l E X w hp
  let : F.Additive := ha
  let e : Q.op ⋙ F ≅ U ⋙ Q := NatIso.ofComponents
    (fun K ↦ eqToIso (ho (Q.obj K.unop))) (by
      intro K M f
      apply square_of_heq (ho (Q.obj K.unop)) (ho (Q.obj M.unop))
      exact hm M.unop K.unop f.unop 1)
  let W := Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E X)
  have : Q.IsLocalization W := ScalarLocalization.semilinear_localization_isLocalization
    (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E X)
    (Padic.coefficientExtensionUniformizer l E)
  let : Localization.Lifting Q.op W.op (U ⋙ Q) F := ⟨e⟩
  let cs : F.CommShift ℤ := Functor.commShiftOfLocalization Q.op W.op ℤ (U ⋙ Q) F
  let : F.CommShift ℤ := cs
  have : NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q.op W.op ℤ (U ⋙ Q) F
  have : Q.op.mapArrow.EssSurj := Localization.essSurj_mapArrow Q.op W.op
  have : F.IsTriangulated := Functor.isTriangulated_of_precomp_iso e
  exact ⟨cs, fun T hT ↦ F.map_distinguished T hT⟩

end WeilConjectures.RationalVerdier
