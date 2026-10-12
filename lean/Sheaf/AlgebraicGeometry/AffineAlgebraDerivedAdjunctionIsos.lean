/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Unit and counit of the affine algebra derived adjunction

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-isos).
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- The ambient derived adjunction has invertible unit and counit at objects with
quasi-coherent cohomology; it need not be an equivalence on the entire derived categories.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-isos).

Proof: Use the exact localization description of g-star on affine stalks.
For each degree i, exact pullback computes H^i(Lg-star M) as g^* H^i(M).
The affine cohomology formula computes H^i(Rg-star K) as g_* H^i(K).
The underived tensor associativity identification sends the derived adjunction
unit and counit on cohomology to the beta and alpha maps of
affine_module_correspondence: H^i(M) to g_*g^*H^i(M), and
 g^*g_*H^i(K) to H^i(K). Their components are isomorphisms by that theorem.
A map in a derived category is invertible when it induces isomorphisms in all
degrees, giving the asserted unit and counit. For an arbitrary left adjoint L
and adjunction adj to this fixed Rg-star, the unique adjunction-compatible
isomorphism to the derived tensor pullback carries its unit and counit to these
maps, so invertibility holds for adj as well. The comparison with direct image
uses exact scalar restriction and the same K-injective complex as Rf-star;
thus the unbounded cohomology calculation is the affine formula, not a claim
that direct image is exact on arbitrary complexes. -/
theorem affine_algebra_derived_adjunction_isos
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) :
    (∀ M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))),
      directImageAlgebraDerivedQCohProperty f M → IsIso (adj.unit.app M)) ∧
    (∀ K : schemeDerivedCategory X, schemeDerivedQCohProperty X K →
      IsIso (adj.counit.app K)) := by sorry

end AlgebraicGeometry
