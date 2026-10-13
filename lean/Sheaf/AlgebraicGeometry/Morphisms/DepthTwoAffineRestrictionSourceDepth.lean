/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-! # Affine comparison for the restriction source

Source: Stacks Project, Tags 0AV8, 0AVN and 0E9I.
(blueprint: lem-sbc-affine-restriction-source-depth)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Affine comparison for the restriction source.

Source: Stacks Project, Tags 0AV8, 0AVN, 0E9I, 01LC, 05AM and 00LL.
(blueprint: lem-sbc-affine-restriction-source-depth)

Proof: Write a for the injective restriction unit on V and K for its range pulled
back to S. The inclusion a(M) ≤ S and injectivity identify K with M = N(V)
by the actual map m ↦ ⟨a(m), hMS ⟨m, rfl⟩⟩. Thus K is finite, as is its
localization. Let y be the point of V corresponding to p. Quasi-coherence
identifies the localization of M at p with N_y, and the affine stalk
comparison identifies R_p with the local ring at y. These identifications
respect the module actions, so regular sequences and their lengths are
preserved; at y outside U the assumed depth-two bound transfers to K_p.
At y in U, the restriction unit on stalks is an isomorphism. Localizing the
inclusions a(M) ⊆ S ⊆ P gives M_p ⊆ S_p ⊆ P_p with the outer map an
isomorphism. Hence K_p → S_p is surjective, and exactness of localization
makes (S/K)_p zero. This comparison uses no assertion about the depth of the
quotient at boundary points. Empty U and zero M are included; a zero stalk
has infinite depth. -/
theorem affine_restriction_source_depth_comparison
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) 
    (hinj : ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V))
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (hMS : LinearMap.range
      (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom ≤ S)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime] :
    ∃ hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p
        ((LinearMap.range
          (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
            S.subtype)),
      letI := hfinite
      (hV.fromSpec ⟨p, inferInstance⟩ ∈ U →
        Subsingleton (LocalizedModule.AtPrime p
          (S ⧸ (LinearMap.range
            (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
              S.subtype))) ∧
      (hV.fromSpec ⟨p, inferInstance⟩ ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
          (LocalizedModule.AtPrime p
            ((LinearMap.range
              (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
                S.subtype))) := by sorry

end AlgebraicGeometry.Scheme
