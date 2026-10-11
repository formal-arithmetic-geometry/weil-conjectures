/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Sheaf.RingTheory.FormalGlueingData

/-!
# Canonical maps for formal glueing

Source: Stacks Project, More on Algebra, Remark 05EL; Algebra, Lemmas 07K0 and 00DK
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).

## Main statements
* `LocalizedModule.away_map_functorial`: localization preserves composition, addition and identity.
* `FormalGlueing.localizedSModule_properties`: properties of the induced scalar action.
* `FormalGlueing.swap_properties`: interchange of iterated localizations.
* `FormalGlueing.compare_properties`: localization commutes with extension of scalars.
-/

@[expose] public section

universe u v w v₁ v₂ v₃

open scoped TensorProduct

namespace LocalizedModule

/-- Localization preserves composition, addition and identity (clause (1)).
Source: Stacks Project, Algebra, Definition 07JZ and Lemma 07K0
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, step 1: both composites take q/e^n to h(k(q))/e^n; both sums take it to
(h(q)+h'(q))/e^n; the localized identity fixes every fraction. Fractions exhaust the module. -/
theorem away_map_functorial {R : Type u} [CommRing R]
    {Q : Type v₁} {Q' : Type v₂} {Q'' : Type v₃}
    [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']
    [AddCommGroup Q''] [Module R Q''] (e : R)
    (k : Q →ₗ[R] Q') (h h' : Q' →ₗ[R] Q'') :
    let T := Submonoid.powers e
    let lQ := mkLinearMap T Q
    let lQ' := mkLinearMap T Q'
    let lQ'' := mkLinearMap T Q''
    IsLocalizedModule.map T lQ lQ'' (h.comp k) =
      (IsLocalizedModule.map T lQ' lQ'' h).comp (IsLocalizedModule.map T lQ lQ' k) ∧
    IsLocalizedModule.map T lQ' lQ'' (h + h') =
      IsLocalizedModule.map T lQ' lQ'' h + IsLocalizedModule.map T lQ' lQ'' h' ∧
    IsLocalizedModule.map T lQ lQ LinearMap.id = LinearMap.id := by
  sorry

end LocalizedModule

namespace FormalGlueing

open CategoryTheory

/-- The induced S-action has the given restricted R-action, the localization map is
S-linear, and localizing an S-linear map gives an S-linear map (clause (1)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Definition 07JZ
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, step 2: localize the R-linear endomorphisms q ↦ s • q. Step 1 preserves
m₁ = id, mₛ₊ₜ = mₛ + mₜ and mₛₜ = mₛ ∘ mₜ, giving the module laws.
The formula on fractions identifies the restricted R-action and makes the localization
map S-linear. For an S-linear h, h(sq)/e^n = s h(q)/e^n, proving its S-linearity.
The action is the existing `localizedSModule`, defined by exactly this fraction formula. -/
theorem localizedSModule_properties {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S) (e : R)
    (Q : ModuleCat.{v₁} S) (Q' : ModuleCat.{v₂} S) (h : Q →ₗ[S] Q') :
    let m := localizedSModule φ e Q
    let m' := localizedSModule φ e Q'
    (∀ (s : S) (q : Q) (n : ℕ),
      m.smul s (LocalizedModule.mk (show restrict φ Q from q)
        ⟨e ^ n, ⟨n, rfl⟩⟩) =
        LocalizedModule.mk (S := Submonoid.powers e)
          (show restrict φ Q from s • q) ⟨e ^ n, ⟨n, rfl⟩⟩) ∧
    (∀ (r : R) (x : localize e (restrict φ Q)), m.smul (φ r) x = r • x) ∧
    (∀ (s : S) (q : Q),
      LocalizedModule.mk (show restrict φ Q from s • q) 1 =
        m.smul s (LocalizedModule.mk (show restrict φ Q from q) 1)) ∧
    (∀ (s : S) (x : localize e (restrict φ Q)),
      localMap e (restrictMap φ h) (m.smul s x) =
        m'.smul s (localMap e (restrictMap φ h) x)) := by
  sorry

/-- Both f and g act bijectively on (P_g)_f. The existing canonical swap is the unique
map specified on P; it has the fraction formula and inverse the reverse swap (clause (2)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Lemma 07K0
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, steps 3–5: f is invertible by the outer localization; localizing the inverse of
multiplication by g on P_g proves g is invertible too, by step 1. Apply the universal
property first at f and then at g to the composite P → P_g → (P_g)_f. Its values on
fractions are (p/f^a)/g^b ↦ (p/g^b)/f^a. Two applications of uniqueness show that the
values on ((p/1)/1) determine the map. Reversing f and g gives the inverse: both composites
fix every fraction. This also applies to zero denominators and zero localizations. -/
theorem swap_properties {R : Type u} [CommRing R]
    (P : ModuleCat.{v} R) (f g : R) :
    Function.Bijective (fun x : localize f (localize g P) ↦ f • x) ∧
    Function.Bijective (fun x : localize f (localize g P) ↦ g • x) ∧
    (∀ (p : P) (a b : ℕ),
      swap f g P (LocalizedModule.mk
        (LocalizedModule.mk p ⟨f ^ a, ⟨a, rfl⟩⟩) ⟨g ^ b, ⟨b, rfl⟩⟩) =
        LocalizedModule.mk (S := Submonoid.powers f)
          (LocalizedModule.mk (S := Submonoid.powers g) p ⟨g ^ b, ⟨b, rfl⟩⟩)
          ⟨f ^ a, ⟨a, rfl⟩⟩) ∧
    (∀ t : localize g (localize f P) →ₗ[R] localize f (localize g P),
      (∀ p : P, t (LocalizedModule.mk (LocalizedModule.mk p 1) 1) =
        LocalizedModule.mk (LocalizedModule.mk p 1) 1) ↔ t = swap f g P) ∧
    (swap g f P).comp (swap f g P) = LinearMap.id ∧
    (swap f g P).comp (swap g f P) = LinearMap.id := by
  sorry

/-- The canonical comparison has the pure-tensor fraction formula, is the unique R-linear
map with its specified values, and is an S-linear isomorphism (clause (3)).
Source: Stacks Project, More on Algebra, Remark 05EL and Algebra, Lemmas 07K0, 00DK, 00D2
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps).
Proof, steps 6–7: tensor P → P_f with S. The inverse of multiplication by f on P_f,
tensored with S, proves invertibility on S ⊗ P_f. The universal property extends the
tensored map uniquely, with (s ⊗ p)/f^n ↦ s ⊗ (p/f^n). Pure tensors generate the
source, and fractions generate its localization, giving uniqueness. The induced S-action
from step 2 makes this formula S-linear. The localization-after-tensor theorem
[lem-weil-pbc-localization-tensor-over-base] identifies it with an R-linear isomorphism;
its inverse is S-linear by applying the forward map to s times an inverse image.
The tensor factors are in Mathlib's extension-of-scalars order S ⊗ P. -/
theorem compare_properties {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (φ : R →+* S) (P : ModuleCat.{v} R) (f : R) :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective (fun x : restrict φ (extend φ (localize f P)) ↦ f • x) ∧
    (∀ (p : P) (s : S) (n : ℕ),
      compare φ f P (LocalizedModule.mk
        (show restrict φ (extend φ P) from s ⊗ₜ[R] p) ⟨f ^ n, ⟨n, rfl⟩⟩) =
        (show restrict φ (extend φ (localize f P)) from
          s ⊗ₜ[R] LocalizedModule.mk p ⟨f ^ n, ⟨n, rfl⟩⟩)) ∧
    (∀ t : localize f (restrict φ (extend φ P)) →ₗ[R]
        restrict φ (extend φ (localize f P)),
      (∀ (p : P) (s : S),
        t (LocalizedModule.mk (show restrict φ (extend φ P) from s ⊗ₜ[R] p) 1) =
          (show restrict φ (extend φ (localize f P)) from
            s ⊗ₜ[R] LocalizedModule.mk p 1)) ↔ t = compare φ f P) ∧
    (∀ (s : S) (x : localize f (restrict φ (extend φ P))),
      compare φ f P ((localizedSModule φ f (extend φ P)).smul s x) =
        (s • (compare φ f P x : extend φ (localize f P)))) ∧
    Function.Bijective (compare φ f P) := by
  sorry

end FormalGlueing
