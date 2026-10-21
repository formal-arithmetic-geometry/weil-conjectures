/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport

/-! # Restriction of the specified open scalar conjugate

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md (2), alternative
open-adjunction argument; def-sfb-derived-open-immersion-shriek-iso; Stacks Tag 0B65
(blueprint: lem-sfb-open-scalar-conjugate-normalization).

The displayed isomorphisms have their forward maps fixed to the scalar-adjunction mate
and the actual open adjunction units. Thus their inverses cannot be independently
renormalized. All categories and scalar extensions are ordinary and unbounded.
The inline projection of the left functor from its specified adjunction is definitionally
L(extendScalars); it avoids repeatedly synthesizing the K-flat tensor instances.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified scalar/open conjugate restricts to inverse theta under the actual units.

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md (2), alternative
open-adjunction argument; Stacks Tag 0B65
(blueprint: lem-sfb-open-scalar-conjugate-normalization).

Proof:
1. Write J_A, J_B for open extension, R_A, R_B for restriction, and r for scalar
restriction. The published beta is the conjugate of c : R_B ⋙ r_U ≅ r_X ⋙ R_A
under the two composite adjunctions (def-weil-pbc-composite-adjunction).
2. Since alpha is invertible (lem-sfb-alpha-iso), extension along alpha collapses by
x tensor n ↦ alpha inverse(x)n, with inverse n ↦ 1 tensor n. The coefficient-change
square identifies both restricted actions, using sk-def-sfb-change-of-scalars,
sk-def-sfb-transport and sk-def-sfb-module-pushforward-pullback.
3. Unfold comapUpperStarIso and extendScalarsComapIsoOfIsIso: c and its inverse
become identity maps on the same inverse-image module. Localize degreewise.
4. Transpose beta under T_X J_A ⊣ R_A r_X. The composite-unit formula identifies
its transpose with c followed by the transpose of the identity under J_B T_U ⊣ r_U R_B.
5. Transport to sectionwise modules via lem-sfb-internal-module-operations-transport
and lem-sfb-internal-section-scalar-adjunction. Apply
lem-sfb-kflat-scalar-comparison-normalization: the mate of c inverse is the balanced
K-flat comparison theta on every unbounded object, and is invertible without flatness.
6. Transpose R_B(beta_M) theta_(J_A M) T_U(u_A,M) under T_U ⊣ r_U.
Naturality of the scalar unit, the mate equation, naturality of c inverse and step 4
identify this transpose with the transpose of u_B,T_U M. The Hom bijection is injective.
7. The actual open units are invertible. Cancel these units and theta in step 6.
Functoriality gives the displayed equality, naturally for all M. -/
theorem open_scalar_conjugate_normalization
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (θ : D((j)^*⟦Λ⟧) ⋙ ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
            (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))) ≅
          ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
            (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))) ⋙ D((j)^*⟦Λ'⟧))
      (uA : 𝟭 (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) ≅
        D((j)_!open⟦Λ⟧) ⋙ D((j)^*⟦Λ⟧))
      (uB : 𝟭 (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ' U))) ≅
        D((j)_!open⟦Λ'⟧) ⋙ D((j)^*⟦Λ'⟧)),
      θ.hom = SheafOfModules.ScalarPullback.mate
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
        (derivedComapUpperStarIso a j).inv ∧
      uA.hom = (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit ∧
      uB.hom = (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j).unit ∧
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
        D((j)^*⟦Λ'⟧).map ((derivedOpenImmersionShriekIso a j).hom.app M) ≫
            uB.inv.app (((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
              (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))).obj M) =
          θ.inv.app (D((j)_!open⟦Λ⟧).obj M) ≫
            ((fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
              (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))).map
                (uA.inv.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
