/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Coefficients
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Sheaves killed by the Jacobson radical and finite direct images

Let `Λ` be a finite ring with Jacobson radical `J`. For a sheaf `F` of `Λ`-modules, the quotient
`F / J F` is the cokernel of `AlgebraicGeometry.Etale.smulDesc J F : ⨁_{x ∈ J} F ⟶ F`.

- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_smul_eq_zero`: a constructible
  sheaf killed by `J` on a scheme of finite type over a field embeds into a finite sum of direct
  images along finite morphisms of constant sheaves with finite values killed by `J`.
- `AlgebraicGeometry.Etale.exists_retract_lowerStar_constantSheaf_of_smul_eq_zero`: for a finite
  morphism `π` and a finite module `M` killed by `J`, the sheaf `π_* M` is a retract of a finite
  sum of copies of `π_* Λ / J π_* Λ`.

These are the finite-pushforward steps of the proof of blueprint `lem-kun-0f1j`, for sheaves
killed by `J` (blueprint `lemma-weil-pbc-constructible-finite-pushforward`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The map `⨁_{x ∈ I} F ⟶ F` given by the multiplications by the elements of a finite ideal; its
cokernel is `F / I F`. -/
noncomputable def smulDesc {C : Type*} [Category C] [Preadditive C] [Linear Λ C]
    [HasFiniteBiproducts C] (I : Ideal Λ) [Finite I] (F : C) :
    (⨁ fun _ : I ↦ F) ⟶ F :=
  biproduct.desc fun x ↦ (x : Λ) • 𝟙 F

variable (Λ) [Finite Λ]

/-- A constructible sheaf killed by the Jacobson radical `J` of `Λ`, on a scheme of finite type
over a field, embeds into a finite sum of direct images along finite morphisms of constant
sheaves with finite values killed by `J` (blueprint `lemma-weil-pbc-constructible-finite-pushforward`
for sheaves killed by `J`, used in the proof of blueprint `lem-kun-0f1j`). -/
theorem exists_mono_biproduct_lowerStar_of_smul_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 F = 0) :
    ∃ (r : ℕ) (Y : Fin r → Scheme.{u}) (h : ∀ i, Y i ⟶ X) (_ : ∀ i, IsFinite (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Finite (M i))
      (_ : ∀ i, ∀ x ∈ Ring.jacobson Λ, x • 𝟙 (M i) = 0)
      (φ : F ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ :=
  sorry

/-- For a finite morphism `π` and a finite `Λ`-module `M` killed by the Jacobson radical `J`, the
sheaf `π_* M` is a retract of a finite sum of copies of `π_* Λ / J π_* Λ`
(used in the proof of blueprint `lem-kun-0f1j`). -/
theorem exists_retract_lowerStar_constantSheaf_of_smul_eq_zero {X Y : Scheme.{u}} (π : Y ⟶ X)
    [IsFinite π] (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hM : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0) :
    ∃ m : ℕ, Nonempty (Retract
      ((π)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
      (⨁ fun _ : Fin m ↦ cokernel
        (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))) :=
  sorry

end Etale

end AlgebraicGeometry
