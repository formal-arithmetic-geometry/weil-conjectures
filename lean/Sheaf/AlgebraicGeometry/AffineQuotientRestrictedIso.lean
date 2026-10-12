/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# The sheaf associated with an affine quotient

The affine quotient presentation identifies the associated quotient module sheaf
with the restricted pushforward of the closed subscheme's structure sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Basic-open calculation identifies the associated quotient sheaf with the restricted
pushforward of the closed subscheme structure sheaf.
Source: Stacks Project, Lemma 26.7.3(2), Tag 01I9, with the affine chart
and quotient presentation of Tag 068C.
(blueprint: lem-sc-affine-quotient-restricted-iso).

Proof: Write A = Γ(Y,U). Under the affine chart hU.isoSpec and the given
presentation e, the compatibility he identifies the restricted immersion with
Spec(A/I) → Spec A. For every basic open D(g) in Spec A, its inverse image is
D(g mod I). Sections of the pushforward structure sheaf on D(g) are therefore
(A/I)[1/g], as a module over A[1/g]. The associated sheaf of the A-module A/I
has exactly these sections, with the same localized A-action. These identifications
commute with restrictions between basic opens because both restrictions are the
canonical localization maps. Basic opens form a basis stable under intersection,
so the identifications glue uniquely to an isomorphism of module sheaves on Spec A.
Transport this isomorphism along hU.isoSpec to obtain the asserted isomorphism on U.
The argument also covers I = ⊤ (both sheaves are zero), I = ⊥, and empty U. -/
theorem affine_quotient_restricted_iso {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.Opens) (hU : IsAffineOpen U) (I : Ideal (Γ(Y, U)))
    (e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
      Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)))
    (he : i ∣_ U ≫ U.toSpecΓ =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    Nonempty (((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj
        (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I))) ≅
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))) := by sorry

end AlgebraicGeometry
