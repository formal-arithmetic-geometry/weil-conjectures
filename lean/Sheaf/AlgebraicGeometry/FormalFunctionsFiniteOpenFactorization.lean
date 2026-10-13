/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback

/-! # Finite pullback on the inverse-image opens

Source: Stacks Project, Tag 02OD, factorization through the local spectrum;
Tags 01F7 and 01FB, composition and restriction of cohomology maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-factorization)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- A single additive map on open cohomology intertwines global finite pullback
with restriction and the two restricted pullbacks. No germ or stalk comparison
occurs in this statement.
Source: Stacks Project, Tag 02OD, the finite maps factor through the local spectrum;
Tags 01F7 and 01FB, functoriality of cohomology.
(blueprint: lem-weil-pbc-formal-functions-finite-open-factorization)

Proof: write g' for the projection from the local base change to X and i' for
formalFunctionsFiniteι. Put U=f inverse V, U'=g' inverse U and W=i_n inverse U.
The projection identity i' followed by g'=i_n gives W=i' inverse U'. Restrict the
h-map formalFunctionsFiniteFMap to U' using moduleCohomologyFMap_restriction.
Transport its target along the equality of opens, using the canonical restricted
module identification, and take its cohomology map as t. The restriction square
in that theorem gives the first equality for every global class z.
For the second equality, transpose the defining formalFunctionsFiniteFMap across
its tensor-pullback adjunction. Its image is the i_n unit with the pushforward
composition and equality identifications. Restrict this equation to W. Substitute
E.unit_square and D.unit_square. Naturality of pushforwardComp and pushforwardCongr
identifies the composite of E.psi with the restricted finite h-map with D.psi:
both transpose under restriction to the same restricted i_n unit. Applying
moduleCohomologyFMap_comp and its congruence for the projection identity yields
the second equality. Arbitrary resolution choices affect neither equality, since
these h-maps are fixed by their unit squares. The construction applies to every
open V, even one not containing y, and to arbitrary F: no flatness, properness,
coherence, Noetherianity, surjectivity, or completion comparison is required.
At p=0 these are ordinary section pullbacks; for zero coefficients or empty opens
all maps are zero. The intermediate map is used only to prove a proposition. -/
theorem formalFunctions_finite_open_factorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (F : X.Modules) (p n : ℕ) (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (J : InjectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))
    (V : Y.Opens)
    (E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (formalFibreBaseMap Y y n) F I J V) :
    ∃ t : (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
          ((Scheme.Modules.restrictFunctor
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))) →+
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology
          ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
          ((Scheme.Modules.restrictFunctor ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))),
      (∀ z : formalFunctionsLocalCohomology f y F p,
        t (Scheme.Modules.moduleCohomologyRestriction
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V))
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F) p z) =
        Scheme.Modules.moduleCohomologyRestriction ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) p
          (formalFunctionsFinitePullback f y F p n z)) ∧
      (∀ xi : (forget₂ _ AddCommGrpCat.{u}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)),
        t (Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) E.psi p xi) =
        Scheme.Modules.moduleCohomologyFMap ((formalFibreι f y n).resLE (f ⁻¹ᵁ V)
          ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi) := by sorry

end AlgebraicGeometry
