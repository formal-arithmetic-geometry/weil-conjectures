/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Integral pushforward maps detecting a prescribed point

Source: Stacks Project, Tag 09Z6, the generic trivialization and normalization argument.
(blueprint: lem-weil-pbc-constructible-module-integral-stalk-embedding).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A constructible module sheaf has a map to an integral pushforward of a finite constant
module which is injective at every geometric point above a prescribed point.

Source: Stacks Project, Tag 09Z6, proof of (1), the paragraph starting with the reduced
closure of `x`, transferred to (3).
(blueprint: lem-weil-pbc-constructible-module-integral-stalk-embedding).

Proof: Pull back to Spec of the residue field of x. The constructible stratification pulls
back, so the resulting sheaf becomes a constant finite module M after a finite separable
extension K. Normalize the reduced closure of x in K. This gives a normal integral scheme
Y and an integral morphism nu : Y -> X with generic point Spec K. On Y the unit from the
constant module sheaf to the pushforward of its generic restriction is an isomorphism
(09Z5). First use the generic-point adjunction, then the nu adjunction, to obtain a map
phi : F -> nu_* M. These adjunctions and the constant-sheaf comparison are module-linear.
Every geometric point above x lifts to Spec K, since its algebraically closed residue field
contains a copy of the finite extension K. The pullback of the first adjoint map at this
lift is the chosen constant-sheaf isomorphism: the two triangle identities and naturality
of the counit give this equality. At the resulting point of Y, its stalk is therefore an
isomorphism. The stalk map of phi followed by restriction to this stalk of M is that
isomorphism, under the inverse-image stalk comparison. Hence the stalk map of phi is
injective. This works for every geometric point above x. There is no point to choose when
X is empty; for the zero sheaf the same construction uses the zero module. -/
theorem exists_integral_lowerStar_stalk_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (x : X) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X), IsIntegralHom ν ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        ∃ (φ : F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
            ((Scheme.SpecToEquivOfField Ω X) s).1 = x →
              Function.Injective
                (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map φ) := by
  sorry

end AlgebraicGeometry.Etale
