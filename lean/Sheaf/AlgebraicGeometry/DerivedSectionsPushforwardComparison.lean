/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.Topology.OpenModuleDerivedSections
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Derived sections of a derived direct image

Source: Stacks Project, Derived Categories of Schemes, Tag 08D5, proof of (2), and
Cohomology, Tag 0D5T (blueprint: lem-pc-derived-sections-pushforward-comparison).
-/

@[expose] public section

universe u wX wV wU wAb

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- For an open `U` of the target of `f`, derived global sections of the derived
pushforward of `E` restricted to `f⁻¹(U)` agree naturally with derived global sections
on that inverse image. The isomorphism is in the unbounded derived category of abelian
 groups, so it compares complexes up to quasi-isomorphism, not strict complexes.
Source: Stacks, Tag 08D5, proof of (2), displayed derived-sections identity, with the
composition mechanism of Tag 0D5T
(blueprint: lem-pc-derived-sections-pushforward-comparison).

Proof: (1) Put `V = f⁻¹(U)`. The definition of module direct image gives the natural
identity Γ(U, (f_U)_*G) = Γ(V, G) on module sheaves.
(2) Map the ringed spaces U and V to the one-point ringed space with ring ℤ.
Uniqueness of ring maps out of ℤ makes the map from V the composite of f_U and the
map from U. Direct image along these maps is global sections, and its K-injective
computation is therefore RΓ. This uses def-weil-locally-ringed-space-morphism and
 def-pc-ringed-spaces-derived-direct-image; the point is a ringed space, not Spec ℤ.
(3) Apply lem-pc-ringed-spaces-derived-direct-image-composition to V → U → (pt, ℤ).
The composition isomorphism identifies RΓ(U,-) after R(f_U)_* with RΓ(V,-).
Whisker by exact restriction from X to V (def-pc-derived-open-restriction-maps).
This yields a natural isomorphism in E; the construction also commutes with restriction
 to smaller opens. No quasi-coherence or boundedness hypothesis is used. -/
theorem derivedSectionsPushforwardComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wAb} AddCommGrpCat.{u}] :
    Nonempty
      (((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory ⋙
          schemeDerivedDirectImage (morphismRestrict f U) ⋙
          RingedSpace.openModuleDerivedSections U.toScheme.toRingedSpace ⊤) ≅
        ((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory ⋙
          RingedSpace.openModuleDerivedSections (f ⁻¹ᵁ U).toScheme.toRingedSpace ⊤)) := by
  sorry

end AlgebraicGeometry
