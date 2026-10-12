/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteEtaleAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# The Tor amplitude of the Verdier dual

This file proves the auxiliary statements used for the Tor bound of the Verdier dual
(`lem-weil-verdier-preservation-strata`):

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompDerivedHomIso`: the internal hom into a
  direct image, `RHom(K, Rf_* M) ≅ Rf_* RHom(Lf^* K, M)`;
- `AlgebraicGeometry.Etale.torAmplitudeIn_obj₂_of_distTriang`: Tor amplitude in a given interval
  is closed under extensions;
- `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_obj₂_of_distTriang`: the same for the
  internal hom out of a fixed complex, which is triangulated in its second variable;
- `AlgebraicGeometry.Etale.torAmplitudeIn_of_leftDerivedUpperStar_of_surjective`: Tor amplitude
  descends along a surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The internal hom into a direct image -/

/-- **The internal hom into a direct image**: for `f : Z ⟶ X` and `K` on `X`,
`RHom_X(K, Rf_* M) ≅ Rf_* RHom_Z(Lf^* K, M)`, naturally in `M`. Both sides are right adjoint to
functors of `T ∈ D(X_ét)`: the left one to `T ↦ Lf^*(K ⊗ᴸ T)`, the right one to
`T ↦ Lf^* K ⊗ᴸ Lf^* T`, and these agree since `Lf^*` is monoidal. -/
noncomputable def rightDerivedLowerStarCompDerivedHomIso {Z X : Scheme.{u}} (f : Z ⟶ X)
    (K : DerivedCategoryModule Λ X) :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K) ≅
      (RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ]) :=
  ((((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)).ofNatIsoLeft
      ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) f).app K)).rightAdjointUniq
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))))

/-! ### Extensions -/

/-- **Tor amplitude is closed under extensions**: in a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` whose outer terms have Tor amplitude in `[a, b]`, so does `X₂`, the
derived tensor product with a sheaf being triangulated. -/
lemma torAmplitudeIn_obj₂_of_distTriang {X : Scheme.{u}}
    (T : Triangle (DerivedCategoryModule Λ X)) (hT : T ∈ distTriang _) {a b : ℤ}
    (h₁ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₁)
    (h₃ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₃) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b T.obj₂ := fun F ↦ by
  let G := (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  let := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) 0).obj F)
  have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) 0).obj F)
  have hT' := G.map_distinguished _ hT
  obtain ⟨g₁, l₁⟩ := h₁ F
  obtain ⟨g₃, l₃⟩ := h₃ F
  have : _root_.DerivedCategory.TStructure.t.IsGE (G.mapTriangle.obj T).obj₁ a := g₁
  have : _root_.DerivedCategory.TStructure.t.IsGE (G.mapTriangle.obj T).obj₃ a := g₃
  have : _root_.DerivedCategory.TStructure.t.IsLE (G.mapTriangle.obj T).obj₁ b := l₁
  have : _root_.DerivedCategory.TStructure.t.IsLE (G.mapTriangle.obj T).obj₃ b := l₃
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT' a,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT' b⟩

/-- The internal hom `RHom(K, -)` out of a fixed complex `K` sends distinguished triangles to
distinguished triangles, being right adjoint to the triangulated `K ⊗ᴸ -`; hence if `RHom(K, -)`
of the outer terms of a distinguished triangle has Tor amplitude in `[a, b]`, so does
`RHom(K, -)` of the middle term. -/
lemma torAmplitudeIn_derivedHom_obj₂_of_distTriang {X : Scheme.{u}}
    (K : DerivedCategoryModule Λ X) (T : Triangle (DerivedCategoryModule Λ X))
    (hT : T ∈ distTriang _) {a b : ℤ}
    (h₁ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₁))
    (h₃ : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₃)) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj T.obj₂) := by
  let adj := derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K
  let := _root_.DerivedCategory.commShiftTensorLeft (K := K)
  have : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorLeft (K := K)
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  exact torAmplitudeIn_obj₂_of_distTriang Λ _
    (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).map_distinguished _ hT) h₁ h₃

/-! ### Descent along a surjection -/

/-- **Tor amplitude descends along a surjective morphism**: if `p : U' ⟶ U` is surjective and
`Lp^* N` has Tor amplitude in `[a, b]`, so does `N`. The homology sheaves of `N ⊗ᴸ G` vanish as
soon as their pullbacks along `p` do, and `p^*(N ⊗ᴸ G) ≅ Lp^* N ⊗ᴸ p^* G`. -/
lemma torAmplitudeIn_of_leftDerivedUpperStar_of_surjective {U' U : Scheme.{u}} (p : U' ⟶ U)
    (hp : Function.Surjective p.base) {N : DerivedCategoryModule Λ U} {a b : ℤ}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) U' a b ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N)) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b N := fun G ↦ by
  let M := N ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj G
  let e : D((p)^*[ModuleCat.{u + 1} Λ]).obj M ≅ ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N) ⊗
      (_root_.DerivedCategory.singleFunctor _ 0).obj ((p)^*[ModuleCat.{u + 1} Λ].obj G) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory _ p).app _).symm ≪≫
      leftDerivedUpperStarTensorIso _ p _ _ ≪≫
      tensorIso (Iso.refl _) ((singleFunctorCompLeftDerivedUpperStarIso _ p).app G)
  have hz (q : ℤ) (hq : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D((p)^*[ModuleCat.{u + 1} Λ]).obj M))) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj M) := by
    have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
      (ι := PUnit.{u + 1}) (fun _ ↦ p) (fun x ↦ by
        obtain ⟨y, rfl⟩ := hp x
        exact ⟨⟨⟩, y, rfl⟩)
      (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj M ⟶ 0) (fun _ ↦
        isIso_of_source_target_iso_zero _ (hq.of_iso
          ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app M)).isoZero
          (Functor.map_isZero _ (isZero_zero _)).isoZero)
    exact (isZero_zero _).of_iso
      (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj M ⟶ 0))
  obtain ⟨h₁, h₂⟩ := h ((p)^*[ModuleCat.{u + 1} Λ].obj G)
  refine ⟨(_root_.DerivedCategory.isGE_iff M a).2 fun q hq ↦ hz q ?_,
    (_root_.DerivedCategory.isLE_iff M b).2 fun q hq ↦ hz q ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ a).1
      (_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a) q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1
      (_root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b) q hq

end Etale

end AlgebraicGeometry
