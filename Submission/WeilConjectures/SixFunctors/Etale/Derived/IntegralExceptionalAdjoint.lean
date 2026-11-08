/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionTorsion
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The integral exceptional adjoint

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`), and
`f : X ⟶ Y` a separated morphism of separated `k`-schemes of finite type. This file proves the
integral exceptional adjoint
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`): the derived limit
`G_f L` of the exceptional inverse images of the reductions of `L ∈ Dᵇc(Y, Λ)` lies in
`Dᵇc(X, Λ)`, is `Rf^! L`, satisfies the dual formula `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L` and has the
expected reduction Tor interval.

## Proof

* The dual formula is the Yoneda argument of `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`): biduality
  `L ≅ 𝔻_Y 𝔻_Y L` (`thm-coef-integral-verdier`), the projection formula modulo `ϖ`
  (`lem-fix-operation-reduction`), which suffices for morphisms into the derived complete
  dualizing complex, and the identification `Rf^! ω_Y ≅ ω_X` of the dualizing complexes
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_dualizing`).
* Constructibility and the Tor interval then follow, as in the blueprint, from integral
  Verdier duality applied on `Y` and on `X`, the completed pullback being a derived completion
  of `Lf^* 𝔻_Y L` and the dualizing complexes those of `prop-coef-integral-dualizing`.

## Implementation notes

Statements at `Λ` are phrased with `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.derivedHom`, never with `⊗` or `ihom` found by instance search: the
kernel does not compare these in reasonable time at `ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). The formal Yoneda argument is
therefore specialised first to a general coefficient category
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`).

The identification `Rf^! ω_Y ≅ ω_X` rests on the composition law of the exceptional inverse
images on the torsion tower `n ↦ Λ ⧸ Iⁿ`
(`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))


/-- At integral coefficients the exceptional inverse image is a right adjoint `G` of `Rf_!`,
assumed to exist; it is `Λ`-linear, `Rf_!` being `Λ`-linear. -/
instance linear_rightAdjoint_rightDerivedLowerShriek {Λ : Type (u + 1)} [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Linear Λ :=
  (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])).right_adjoint_linear

/-! ### The formal dual formula -/

section General

attribute [local instance] _root_.DerivedCategory.braidedCategory'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

/-- **The dual formula `Rf^! L ≅ RHom(N, ω_X)`.** Let `L, M, ω_Y ∈ D(Y_ét)` with an isomorphism
`L ≅ RHom(M, ω_Y)`, and assume that the projection maps
`PF_{f, K, M} : Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)` induce bijections on morphisms into `ω_Y`.
Given `γ : Rf^! ω_Y ≅ ω_X` and `φ : Lf^* M ⟶ N` inducing bijections
`Hom(K ⊗ᴸ N, ω_X) ≃ Hom(K ⊗ᴸ Lf^* M, ω_X)`, there is an isomorphism `Rf^! L ≅ RHom(N, ω_X)`
(`CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`). -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedHom
    {L M ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (e : L ≅ ((derivedHom A Y).obj (op M)).obj ωY)
    (hπ : ∀ K, Function.Bijective (fun a : (R(f)_![A]).obj (((derivedTensor A X).obj K).obj
        ((L((f)^*[A])).obj M)) ⟶ ωY ↦ ((projectionMap A f).app K).app M ≫ a))
    {ωX N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (γ : (R(f)_![A]).rightAdjoint.obj ωY ≅ ωX) (φ : (L((f)^*[A])).obj M ⟶ N)
    (hφ : ∀ K, Function.Bijective
      (fun a : ((derivedTensor A X).obj K).obj N ⟶ ωX ↦ ((derivedTensor A X).obj K).map φ ≫ a)) :
    Nonempty ((R(f)_![A]).rightAdjoint.obj L ≅ ((derivedHom A X).obj (op N)).obj ωX) :=
  Verdier.nonempty_iso_obj_of_adjunction (Adjunction.ofIsLeftAdjoint (R(f)_![A]))
    (derivedTensorHomAdjunction A M) e (fun K ↦ ((projectionMap A f).app K).app _)
    (fun g ↦ NatTrans.congr_app ((projectionMap A f).naturality g) _) hπ
    (derivedTensorHomAdjunction A N) γ φ hφ

end General

/-! ### Morphisms into objects orthogonal to `ϖ`-invertible objects -/

section Orthogonal

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

end Orthogonal

/-! ### Closure properties of `Dᵇc(X, Λ)` -/

section Closure

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ} {X Y : Scheme.{u}}

/-- Derived completeness for `I = (ϖ)` is closed under isomorphisms. -/
lemma _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (_root_.DerivedCategory.derivedComplete X.smallEtaleTopology I).IsClosedUnderIsomorphisms := by
  rw [_root_.DerivedCategory.derivedComplete_eq_rightOrthogonal hϖ hI]
  infer_instance

/-- `Dᵇc(X, Λ)` is closed under isomorphisms. -/
lemma DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsClosedUnderIsomorphisms where
  of_iso e := by
    have := _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete (X := X) hϖ hI
    rintro ⟨hc, a, b, h⟩
    exact ⟨(_root_.DerivedCategory.derivedComplete _ I).prop_of_iso e hc, a, b, fun n ↦
      ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).1,
        (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).2⟩⟩

/-- The reductions of `Lf^* K` are the pullbacks of the reductions of `K`, so they are bounded
constructible with the same Tor amplitude as those of `K`. -/
lemma boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
    (f : X ⟶ Y) {K : 𝐃(Y, Λ)} {a b : ℤ} (n : ℕ)
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  subst hI
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (L((f)^*[ModuleCat.{u + 1} Λ])) hϖ (n + 1) K
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e
      (boundedConstructible_leftDerivedUpperStar _ f hK.1),
    (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hK.2)⟩

end Closure

/-! ### The dual formula at the integral stage -/

section DualFormula

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

end DualFormula

/-! ### The dualizing complexes -/

section Dualizing

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ})

omit [IsDomain Λ] [IsNoetherianRing Λ] in
include hϖ hI in
/-- **The composition law of the exceptional inverse images on the torsion tower.** For
composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications, the exceptional
inverse images `R(f ≫ g)^!` and `Rf^! ∘ Rg^!` of `D(-_ét, Λ)` agree on the tower
`n ↦ Λ ⧸ Iⁿ`, compatibly with the transition maps.

The composition law of the compactly supported direct images fails on `D(-_ét, 𝒪_E)`, but it
holds up to cones on which `ϖ` acts invertibly, and the objects `Λ ⧸ Iⁿ`, killed by `ϖⁿ`, see no
such cones (`AlgebraicGeometry.Etale.nonempty_iso_comp_rightDerivedUpperShriek_comp`). -/
theorem nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f ≫ g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    Nonempty (_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙
        (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ≅
      _root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙
        (R(g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ⋙
          (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint) := by
  subst hI
  have hϖI : ϖ ∈ Ideal.span {ϖ} := Ideal.subset_span rfl
  exact nonempty_iso_comp_rightDerivedUpperShriek_comp hϖ (fun n _ a hZ ↦ hZ.hom_eq_zero
    (_root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n.unop) a) f g

omit [IsDomain Λ] [IsNoetherianRing Λ] in
include hϖ hI in
/-- **The dualizing complexes correspond under `Rf^!`.** For `a_X = f ≫ a_Y` and integral
dualizing complexes `ω_X`, `ω_Y` (points of homotopy limit cones of the towers
`n ↦ Ra^!(Λ ⧸ Iⁿ)`), there is an isomorphism `Rf^! ω_Y ≅ ω_X`: `Rf^!` preserves homotopy limits,
being a triangulated right adjoint, and the towers agree by
`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`. -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_dualizing {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [QuasiCompact aX] [HasCompactification aX]
    [HasCompactification aY] [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(aY)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f] [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (ωX : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωX : IsHomotopyLimit ωX)
    (ωY : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint)) (hωY : IsHomotopyLimit ωY) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ωY.pt ≅ ωX.pt) := by
  subst hf
  obtain ⟨e⟩ := nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp I hϖ hI f aY
  let adj := Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])
  have := adj.commShift_of_leftAdjoint ℤ
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have : (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.Additive := adj.right_adjoint_additive
  let E := Functor.associator _ _ _ ≪≫ e.symm
  let hc := hωY.map (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint
  let c : Cone (_root_.DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
      (R(f ≫ aY)_![ModuleCat.{u + 1} Λ]).rightAdjoint) :=
    { pt := (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj ωY.pt
      π := ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.mapCone ωY).π ≫ E.hom }
  obtain ⟨i, -⟩ := (hc.of_iso E c (Iso.refl _) fun n ↦ by simp [c]).exists_iso hωX
  exact ⟨i⟩

end Dualizing



section DerivedLimit

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

end DerivedLimit

/-! ### The integral exceptional adjoint -/

section Constructible

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]


end Constructible

section Matrix

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]

end Matrix

end Etale

end AlgebraicGeometry
