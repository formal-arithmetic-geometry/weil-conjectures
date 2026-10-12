/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Evaluation on the diagonal section of a torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-diagonal-evaluation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- The equivariant presheaf restricted upstairs is the presheaf underlying the
constant module sheaf, naturally in the representation.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-diagonal-evaluation)

Proof: For W etale over c.P, evaluate an equivariant function on the graph of
W.hom in W times_V c.P. The torsor isomorphism identifies this latter scheme
with the disjoint union of copies of W indexed by P. The inverse extends a
locally constant function t on W by the formula rho(g)(t(w)) on the translate
of the graph by g. These copies are open, so the extension is locally constant;
the action law proves equivariance. Evaluation and extension are inverse and
linear, including after scalar restriction. Composition of W with an etale
map and postcomposition with an intertwiner commute with both formulas.
Locally constant functions on W are the sections of the constant module sheaf:
the map from the constant presheaf sends a coefficient to its constant function,
is locally surjective on its open fibers, and is locally injective (on an empty
object use the empty covering). Sheafification gives this identification.
This establishes the stated natural presheaf isomorphism, without sheafifying
the equivariant presheaf or invoking inverse image. -/
theorem equivariantModulePresheaf_diagonal {V : Scheme.{u}} (ℓ : ℕ)
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    Nonempty (
      c.equivariantModulePresheafFunctor ℓ ⋙
        (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)) ⋙
        (Functor.whiskeringLeft c.P.Etaleᵒᵖ V.Etaleᵒᵖ _).obj
          (MorphismProperty.Over.map ⊤ c.etale).op ≅
      forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
        constantSheaf c.P.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
        sheafToPresheaf c.P.smallEtaleTopology _) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
