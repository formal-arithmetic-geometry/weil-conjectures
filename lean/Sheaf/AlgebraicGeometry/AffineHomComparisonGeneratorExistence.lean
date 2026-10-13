/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Existence part of the affine Hom comparison

The chart functor and its rank-one identification are parameters with equations
fixing them to the standard constructions, so this module does not depend on the
unique-existence theorem it supports. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Global linear maps extend to a morphism into the internal Hom sheaf.
Source: Stacks Project, Tag 01I7 (mapping property) and Tag 01HV (4)-(5).
(blueprint: new-affine-hom-generator-extension-existence).

Proof: On Spec A, associate to h : M -> N the global internal-Hom section
represented by tilde(h). First substitute the two chart-identification hypotheses.
This assignment is A-linear: on each principal open,
tilde(h) sends m/s to h(m)/s, so addition and scalar multiplication of h become
addition and scalar multiplication of these local morphisms. The section
identifications for internal Hom and the unit sheaf preserve those operations.
Apply the tilde/global-sections adjunction to this linear map with target the
internal Hom sheaf, obtaining a morphism from tilde(Hom_A(M,N)). The adjunction
formula gives its composite with tilde(a |-> a*h) as the section tilde(h).
Transport along the scheme isomorphism U -> Spec A. Its restriction functor
preserves the rank-one identification tildeSelf followed by restrictUnitIso;
hence the transported formula is exactly the displayed equation. This argument
needs neither finite presentation of M nor quasi-coherence of internal Hom.
For the zero ring the chart is empty and all the sheaves and maps are zero; if
M or N is zero the Hom module is zero and the displayed map is the zero map.
Only existence is asserted here; uniqueness is proved separately by adjunction. -/
theorem exists_affineHom_generator_extension {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) :
    ∀ (T : ModuleCat.{u} Γ(Y, U.1) ⥤ U.1.toScheme.Modules)
      (e : T.obj (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) ≅
        SheafOfModules.unit U.1.toScheme.ringCatSheaf),
      T = tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom →
      HEq e ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso tildeSelf ≪≫
        Scheme.Modules.restrictUnitIso U.2.isoSpec.hom) →
    ∃ c : T.obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf) (T.obj M) (T.obj N),
      ∀ h : M ⟶ N,
        (e.inv ≫ T.map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton Γ(Y, U.1) (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) h))) ≫ c =
          (SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
            (T.obj M) (T.obj N)).unitHomEquiv.symm
              ((SheafOfModules.homObjSectionsEquiv (T.obj M) (T.obj N)).symm (T.map h)) := by
  sorry

end AlgebraicGeometry
