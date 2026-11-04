/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.CoefficientClosedStructureNaturality

/-!
# The tensor–hom adjunction of Weil complexes, natural in both variables

For a Weil complex `ω` on `X`, the bijections `Hom(P ⊗ T, ω) ≅ Hom(T, RHom(P, ω))` form an
isomorphism of functors in `(P, T)`; naturality in `P` is
`WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_comp_naturality`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensorYonedaIso`: the two-variable
  tensor–hom isomorphism on the derived category of pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilComplex.nativeConstructibleTensorYonedaIso`: the same on Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction for the derived internal hom, natural in both variables**
(blueprint: `def-weil-derived-pullback-tensor-hom`): `Hom(P ⊗ T, Q) ≅ Hom(T, RHom(P, Q))`,
naturally in `P` and `T`, the tensor product being the native derived tensor product. -/
noncomputable def nativeDerivedTensorYonedaIso (Q : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (prodOpEquiv _).inverse ⋙ (nativeDerivedTensor k₀ l X).op ⋙ yoneda.obj Q ≅
      Functor.uncurry.obj (derivedHom k₀ l X Q ⋙ yoneda) :=
  letI := (nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  letI := (nativeDerivedClosedComparison k₀ l X).weilSymmetry
  NatIso.ofComponents
    (fun A ↦ Equiv.toIso
      ((Iso.homCongr (β_ A.2.unop A.1.unop).symm (Iso.refl Q)).trans
        ((((nativeDerivedClosedComparison k₀ l X).weilClosed.adjunction A.1.unop).homEquiv
          A.2.unop Q).trans
          (Iso.homCongr (Iso.refl _)
            ((((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q).app A.1))))))
    (by
      rintro ⟨P, T⟩ ⟨P', T'⟩ ⟨g, h⟩
      ext φ
      let C := nativeDerivedClosedComparison k₀ l X
      change 𝟙 _ ≫ (C.weilClosed.adjunction P'.unop).homEquiv T'.unop Q
          ((β_ T'.unop P'.unop).hom ≫ ((g.unop ⊗ₘ h.unop) ≫ φ) ≫ 𝟙 Q) ≫
            (C.homModels.nativeModel Q).hom.app P' =
        h.unop ≫ (𝟙 _ ≫ (C.weilClosed.adjunction P.unop).homEquiv T.unop Q
          ((β_ T.unop P.unop).hom ≫ φ ≫ 𝟙 Q) ≫ (C.homModels.nativeModel Q).hom.app P) ≫
            (derivedHom k₀ l X Q).map g
      simp only [Category.id_comp, Category.comp_id]
      refine (congrArg (· ≫ (C.homModels.nativeModel Q).hom.app P')
        (WeilConjectures.CoefficientClosedStructure.homEquiv_braiding_comp_naturality C.weilClosed
          C.weilSymmetry.toBraidedCategory g.unop h.unop φ)).trans ?_
      simp only [Category.assoc]
      congr 2
      exact (C.homModels.nativeModel Q).hom.naturality g)

end ProEtaleWeilSheaf

namespace WeilComplex

variable {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction on Weil complexes, natural in both variables**: if the derived
internal hom `RHom(-, ω)` into a Weil complex `ω` lands in Weil complexes, then
`Hom(P ⊗ T, ω) ≅ Hom(T, RHom(P, ω))`, naturally in the Weil complexes `P` and `T`. -/
noncomputable def nativeConstructibleTensorYonedaIso (ω : WeilComplex k₀ l Z)
    (hω : ∀ K : WeilComplex k₀ l Z, objectProperty k₀ l Z
      ((ProEtaleWeilSheaf.derivedHom k₀ l Z ω.obj).obj (op K.obj))) :
    (prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l Z).op ⋙ yoneda.obj ω ≅
      Functor.uncurry.obj (ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
        ProEtaleWeilSheaf.derivedHom k₀ l Z ω.obj) (fun K ↦ hω K.unop) ⋙ yoneda) :=
  Functor.isoWhiskerLeft (prodOpEquiv _).inverse (Functor.isoWhiskerLeft
      (nativeConstructibleTensor k₀ l Z).op
        ((objectProperty k₀ l Z).fullyFaithfulι.opCompYonedaObjIso ω).symm) ≪≫
    (Iso.refl _ : _ ≅ ((objectProperty k₀ l Z).ι.op.prod (objectProperty k₀ l Z).ι.op) ⋙
      (prodOpEquiv _).inverse ⋙ (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l Z).op ⋙
        yoneda.obj ω.obj) ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.nativeDerivedTensorYonedaIso ω.obj) ≪≫
    NatIso.ofComponents
      (fun A ↦ ((objectProperty k₀ l Z).fullyFaithfulι.homEquiv (X := A.2.unop)
        (Y := ⟨_, hω A.1.unop⟩)).symm.toIso)
      (by
        rintro ⟨P, T⟩ ⟨P', T'⟩ ⟨g, h⟩
        ext φ
        apply (objectProperty k₀ l Z).ι.map_injective
        rfl)

end WeilComplex

end AlgebraicGeometry
