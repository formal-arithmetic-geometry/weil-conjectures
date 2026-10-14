/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # The exterior sheafification unit on an affine open

Source: Stacks Project, Tag 01I6, Lemmas 26.7.2(2) and 26.7.4.
(blueprint: new-q1-exterior-sheaf-affine-unit-bijective). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical exterior sheafification unit is bijective on affine sections of a
quasi-coherent module.
Source: Stacks Project, Tag 01I6, Lemmas 26.7.2(2) and 26.7.4.
(blueprint: new-q1-exterior-sheaf-affine-unit-bijective).
Proof: Set A = Gamma(X,U) and P = Gamma(M,U). Quasi-coherence identifies M on
U = Spec A with the associated module P, compatibly with restrictions to D(f).
The exterior presheaf on D(f) is therefore the localization of the exterior
A-module of P: extend the alternating wedge map through localization, and use
its universal property to obtain inverse maps, agreeing on pure wedges. These
maps commute with restriction because they agree on pure wedges. Hence on the
principal-open basis its sheafification is the associated exterior module.
Under this identification the sheafification unit on U is the constant-section
map of the associated module, which is bijective. For n=0 the empty wedge
corresponds to 1 in A, and for an empty affine U all modules are zero. -/
theorem exteriorSheaf_affine_unit_bijective {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (U : X.affineOpens) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
        (exteriorSheafPresheaf M n)).app (op U.1)) := by sorry

end AlgebraicGeometry.Scheme.Modules
