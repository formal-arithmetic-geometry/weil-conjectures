/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Specialization of geometric module stalks

Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The specialization map is characterized on affine pointed neighbourhood germs by
restricting the limit projection along `t`. The quantified lift `v` is the composite
of `t` with the specified projection, not an arbitrary lift of its image in the base.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization). -/
def IsEtaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G) : Prop :=
  ∀ (j : SmallModel.{u} (strictHenselizationNeighbourhoods s))
    (v : (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).fiber.obj
      ((AffineEtale.Spec S).obj
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)),
    v.left = t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
      Spec.map (ΓSpecIso
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
          j).1.left.unop).inv →
    (pointSmallEtale s).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2
        G.obj ≫ r =
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).toPresheafFiber
        ((AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        v G.obj

/-- There is a unique map with the specified germ formula.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization).

Proof: the structural-map identity for each limit leg makes its composite with `t`
a lift of the image geometric point. Naturality of the cone makes the resulting
maps from neighbourhood sections to the target stalk compatible with every pointed
neighbourhood map. Affine pointed neighbourhoods are initial among all pointed
neighbourhoods, so the stalk colimit gives a map with these components. The colimit
universal property also gives uniqueness, since all affine germs are specified. -/
theorem existsUnique_etaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃! r : (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G,
      IsEtaleModuleStalkSpecialization s t G r := by
  sorry

/-- Specialization of geometric module stalks, the unique map carrying each affine
pointed-neighbourhood germ to its germ along the strict-localization projection.
Only the proof of its unique characterization is postponed; the object is determined.
Source: Stacks Project, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-module-stalk-specialization). -/
noncomputable def etaleModuleStalkSpecialization
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale s).sheafFiber.obj G ⟶
      (pointSmallEtale (t ≫ strictHenselizationStructuralMap s)).sheafFiber.obj G :=
  Classical.choose (existsUnique_etaleModuleStalkSpecialization s t G)

end AlgebraicGeometry.Scheme
