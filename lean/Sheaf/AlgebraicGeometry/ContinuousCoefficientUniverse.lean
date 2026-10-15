/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap

/-!
# Continuous coefficient rings in the scheme universe

Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category).
The upstream coefficient API fixes the coefficient carrier in Type 0. This interface
uses the same sectionwise construction for any coefficient ring in the scheme universe.
The other internal-module and derived constructions are the imported framework's.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite

variable (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- Continuous functions with pointwise ring operations and precomposition.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category). -/
noncomputable def continuousCoefficientRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} C(S.unop, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl


/-- Continuous functions descend along coherent profinite covers.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category).
Proof: a surjective map of profinite spaces is a quotient map; compatible functions
therefore descend uniquely and continuously. Finite coproducts give the other sheaf axiom. -/
theorem isSheaf_continuousCoefficientRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousCoefficientRingPresheaf T) := sorry

/-- The condensed ring with sections C(S,T), with no Type 0 restriction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category). -/
noncomputable def continuousCoefficientRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨continuousCoefficientRingPresheaf T, isSheaf_continuousCoefficientRingPresheaf T⟩

/-- The underlying internal ring of the continuous condensed coefficient sheaf.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category). -/
noncomputable abbrev continuousCoefficientRingObj :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf T)

end Profinite

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type u)
  [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- Continuous functions on pro-etale objects, with their Zariski topology.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category). -/
noncomputable def continuousCoefficientRingPresheaf : X.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl


/-- Continuous functions are a pro-etale sheaf.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category).
Proof: compatible functions glue uniquely along fpqc covers, since these detect openness
and their fibre products enforce equality of values in each fibre; restrict to pro-etale covers. -/
theorem isSheaf_continuousCoefficientRingPresheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (continuousCoefficientRingPresheaf X T) := sorry

/-- The ring sheaf V ↦ C(|V|,T) in the scheme universe.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-e-module-category). -/
noncomputable def continuousCoefficientRingSheaf :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  ⟨continuousCoefficientRingPresheaf X T, isSheaf_continuousCoefficientRingPresheaf X T⟩

end AlgebraicGeometry.ProEtale
