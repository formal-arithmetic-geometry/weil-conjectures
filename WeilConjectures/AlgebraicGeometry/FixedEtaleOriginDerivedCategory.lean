/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness

/-! # Retained etale origins in fixed-scalar coordinates

Source: blueprint main-20261015, def-weil-compact-support-candidate, order 1472,
and def-weil-pbc-etale-origin-witness (blueprint: def-sf-etale-origin-subcategory).
The original ring-sheaf presentation remains available. These are its triples in
fixed-scalar module-sheaf coordinates, with all underlying derived arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The same witnessed D+ category in fixed-scalar coordinates: an underlying
bounded-below pro-etale object, a bounded-below etale antecedent, and its specified
comparison isomorphism. The induced category imposes no condition on arrows.
Source: blueprint order 1472 and the retained witness definition
(blueprint: def-sf-etale-origin-subcategory). -/
abbrev FixedEtaleOriginDerivedCategory (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  InducedCategory
    (DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (fun P : Σ K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)),
      Scheme.FixedEtaleOriginWitness T A K ↦ P.1)

/-- Forget the retained witness. This is the canonical fully faithful induced
functor, followed by the bounded-below inclusion, with its original action on arrows.
Source: blueprint order 1472 (blueprint: def-sf-etale-origin-subcategory). -/
def fixedEtaleOriginForgetful (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    FixedEtaleOriginDerivedCategory T A ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  inducedFunctor (fun P : Σ K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)),
      Scheme.FixedEtaleOriginWitness T A K ↦ P.1) ⋙ DerivedCategory.Plus.ι

end AlgebraicGeometry.ProEtale
