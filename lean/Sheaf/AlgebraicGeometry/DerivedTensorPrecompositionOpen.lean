/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # A tensor precomposition map invertible over a pulled-back open

Source: Stacks Project, Tags 08DW, 08DX and 0E4G, Lemma 48.4.4.
(blueprint: lem-sc-derived-tensor-precomposition-open).
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Pull back a perfect map to the tensor unit and tensor it with P.
Source: Stacks Project, Tags 08DW(1), 08DX(1), and Tag 0E4G, Lemma 48.4.4,
last paragraph.
(blueprint: lem-sc-derived-tensor-precomposition-open).

Proof: Work first in the standard derived localizations. The tensor unit is the
structure sheaf in degree zero, and its pullback is the tensor unit on X; the
K-flat pullback of the structure sheaf gives this isomorphism e. Perfect I has
quasi-coherent cohomology. Pullback preserves quasi-coherent cohomology by 08DW,
and tensor preserves it by 08DX, giving the assertion about Lf*I tensor P.
Restriction to U = f inverse image V commutes with derived pullback and derived
tensor. Thus restriction of Lf*i is pullback of i restricted to V, and is invertible.
Its tensor with P restricted to U is invertible, as are the restrictions of e
and the left unitor. Their composite is therefore invertible. Transport the
pullback and these identifications through the unique localization equivalences
in derivedPullbackAcrossUniverses to the specified independent universes and
through exact restriction to the specified open categories. Naturality of those
comparisons identifies the transported composite with the displayed map.
No adjunction, direct image, annihilation hypothesis or support of P is used.
For empty V, zero P or I equal to the unit the same isomorphism computations apply.
The existential e is not used to define chosen data. -/
theorem exists_derivedTensor_precomposition_open
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i)) :
    ∃ e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
        𝟙_ (schemeDerivedCategory X),
      schemeDerivedQCohProperty X ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj) ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map
          ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
            e.hom ▷ P.obj ≫ (λ_ P.obj).hom)) := by sorry

end AlgebraicGeometry
