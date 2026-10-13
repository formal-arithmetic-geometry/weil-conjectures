/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # comparison to injective terms for principal-open Čech coordinates

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-injective-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A K-injective coefficient complex admits a comparison square to the subset Čech
augmentation of a complex with injective terms. The section comparison is a
quasi-isomorphism; no homology assertion about either augmentation is assumed.

Source: Stacks Project, Cohomology, Tag 08C1, finite Čech comparison, and Tag 079P,
functorial K-injective resolutions.
(blueprint: lem-sc-principal-open-cech-injective-comparison).

Proof: Choose a functorial K-injective resolution J → I with injective terms.
Since J and I are K-injective, its quasi-isomorphism is a homotopy equivalence.
Construct K₁ by applying section evaluation on V to I and changing scalars to A.
Construct T₁ as the finite product in each displayed degree, with the stated signed
vertical and deletion differential; d squared is zero by restriction naturality,
anticommutation of the signed vertical and horizontal terms, and cancellation of
pairs of deletions. The singleton restrictions define α₁. Its chain-map equation
is restriction naturality in degree zero and the cancellation of the two singleton
restrictions in degree one. Use the components of J → I in the σ and τ coordinates
to define a and b; naturality and the displayed differentials make them chain maps.
Singleton naturality gives α ≫ b = a ≫ α₁, and all other components vanish.
Section evaluation preserves the inverse comparison and its homotopies, so a is a
homotopy equivalence and a quasi-isomorphism. The analogous total homotopy uses
(-1) to the Čech degree; it is not needed for the asserted one-sided transfer.
For an empty family V is empty and both section complexes and subset products
vanish. Repetitions and empty members leave the coordinate construction valid. -/
theorem principalOpenCech_injective_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
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
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∃ (I : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        (K₁ T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ₁ : ∀ n : ℤ, K₁.X n ≅ (modulesSpecToSheaf.obj (I.X n)).obj.obj (op V))
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
        (α₁ : K₁ ⟶ T₁) (a : K ⟶ K₁) (b : T ⟶ T₁),
        (∀ n : ℤ, Injective (I.X n)) ∧
      (∀ (n : ℤ) (s : K₁.X n),
        (σ₁ (n + 1)).hom (K₁.d n (n + 1) s) =
          (modulesSpecToSheaf.map (I.d n (n + 1))).hom.app (op V) ((σ₁ n).hom s)) ∧
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
        QuasiIso a ∧ α ≫ b = a ≫ α₁ := by sorry

end AlgebraicGeometry
