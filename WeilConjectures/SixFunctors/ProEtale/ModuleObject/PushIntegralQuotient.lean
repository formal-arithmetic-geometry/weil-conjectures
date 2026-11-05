/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal

/-!
# The derived (Push) comparison along a quotient `𝒪_E ⟶ 𝒪_E ⧸ (ϖ)`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`,
`a : 𝒪̲_E ⟶ Λ'` a morphism of commutative condensed rings and `ϖ ∈ 𝒪_E` a nonzero element such
that, on every scheme `X`, the sequence
```
0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ Λ'_X ⟶ 0
```
is short exact (e.g. `Λ' = 𝔽_E` with `ϖ` a uniformizer, or `Λ' = 𝒪_E ⧸ ℓⁿ` with `ϖ = ℓⁿ`).
This file generalises the residue-field results of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal` and the files it uses to
this setting:

* `ProEtale.CondensedRing.rightAcyclic_lowerStar_of_comap_of_shortExact`: a `Λ'_X`-module is
  `f_*`-acyclic as soon as its restriction of scalars to `𝒪_{E,X}` is;
* `ProEtale.CondensedRing.isIso_pushHom_app_of_rightAcyclic_of_shortExact`: the underived
  (Push) comparison `Λ'_Y ⊗ f_* M ⟶ f_*(Λ'_X ⊗ M)` is an isomorphism at every `f_*`-acyclic
  `𝒪_{E,X}`-module `M` on which `ϖ` acts injectively;
* `ProEtale.CondensedRing.exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_of_ne_zero`:
  torsion-free `f_*`-acyclic resolutions for a nonzero `ϖ`;
* `ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact`:
  **the derived (Push) comparison** `Λ' ⊗ᴸ Rf_* K ⟶ Rf_*(Λ' ⊗ᴸ K)` is an isomorphism for every
  bounded below `K ∈ D(𝒪_{E,X})`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] Bimod.monoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  (a : Profinite.padicIntegersRingObj ℓ E ⟶ Λ') [IsMonHom a] (ϖ : PadicAlgCl.integers ℓ E)
  (w : ∀ X : Scheme.{u}, (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom ≫ coefficientMap a X = 0)
  (hφ : ∀ X : Scheme.{u}, (ShortComplex.mk _ _ (w X)).ShortExact)

end AlgebraicGeometry.ProEtale.CondensedRing
