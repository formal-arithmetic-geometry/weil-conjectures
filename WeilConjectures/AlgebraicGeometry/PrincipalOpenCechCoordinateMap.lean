/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSignedComplex
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSingletonAugmentation
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechCoefficientMap

/-!
# Functorial subset Čech coordinate construction

## References

* Stacks Project, Tag 08C1, <https://stacks.math.columbia.edu/tag/08C1>
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Subset Čech coordinates extend any coefficient chain map to a total chain map.
The target section complex is supplied as an input. No injectivity,
K-injectivity, quasi-isomorphism or homotopy assumption is required (Stacks, Tag 08C1). -/
theorem principalOpenCech_coordinate_map_exists
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (g : J ⟶ I) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (T : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ))
      (K₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ₁ : ∀ n : ℤ, K₁.X n ≅ (modulesSpecToSheaf.obj (I.X n)).obj.obj (op V)),
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K₁.X n),
        (σ₁ (n + 1)).hom (K₁.d n (n + 1) s) =
          (modulesSpecToSheaf.map (I.d n (n + 1))).hom.app (op V) ((σ₁ n).hom s)) →
      ∃ (T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
        (α₁ : K₁ ⟶ T₁) (b : T ⟶ T₁),
      (∀ (n : ℤ) (s : T₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ (n + 1)).hom (T₁.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (I.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ₁ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ₁ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) ∧
      (∀ (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ n).hom (α₁.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
              (op V) ((σ₁ n).hom s)) else 0) ∧
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ n).hom (b.f n s) S =
          (modulesSpecToSheaf.map (g.f (n + 1 - (S.val.card : ℤ)))).hom.app
            (op (D S.val)) ((τ n).hom s S)) := by
  intro V D T τ hle hls he hes K₁ σ₁ hT hK
  obtain ⟨T₁, τ₁, hT₁⟩ := principalOpenCech_signed_complex_exists A r f I hle he
  obtain ⟨α₁, hα₁⟩ := principalOpenCech_singleton_augmentation_exists
    A r f I hle hls he hes K₁ σ₁ T₁ τ₁ hT₁ hK
  obtain ⟨b, hb⟩ := principalOpenCech_coefficient_map_exists
    A r f J I g T τ hle he T₁ τ₁ hT hT₁
  exact ⟨T₁, τ₁, α₁, b, hT₁, hα₁, hb⟩

end AlgebraicGeometry
