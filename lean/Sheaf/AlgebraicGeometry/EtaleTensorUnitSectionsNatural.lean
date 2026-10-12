/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Natural structure-sheaf coordinates for tensor sections

Source: Stacks Project, Tags 0096, 01CA and 03DR.
(blueprint: lem-sc-etale-tensor-unit-sections-natural)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules


local instance (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unit module's tensor sections have their usual structure-sheaf coordinates,
compatibly with restrictions and multiplication by global functions.
Source: Stacks Project, Tags 0096 and 01CA (pullback of the unit), and Tag 03DR,
equation (35.8.1) (normalized restrictions).
(blueprint: lem-sc-etale-tensor-unit-sections-natural)

Proof: For u:U -> X take the section map of the adjoint structure-sheaf morphism
u^* O_X -> O_U. It is an isomorphism by tensorPullbackObjUnitToUnit_isIso.
Its adjunction-unit equation identifies the image of a section r with u^*(r).
The unit equation for normalized composition then identifies restriction along
v:V -> U with the structure-sheaf restriction v^*. Hence the section isomorphisms
are natural. For multiplication by r, naturality of the adjunction gives the
commuting square between u^*(r times -) and multiplication by u^*(r) after the
unit isomorphism. Equivalently, evaluate the square on the unit generator and use
O_U-linearity: a section x maps to u^*(r) times its coordinate. Commutativity of
O_U gives the displayed order of factors. These arguments also hold on the empty
scheme and for r=0 or r=1; they impose no field or dimension hypothesis. -/
theorem exists_etaleTensorUnit_sections_natural (X : Scheme.{u}) :
    ∃ b : ∀ U : X.Etaleᵒᵖ,
        (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U ≃+
          Γ(U.unop.left, ⊤),
      (∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V)
          (x : (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U),
        b V ((etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.map g x) =
          g.unop.left.appTop (b U x)) ∧
      (∀ (r : Γ(X, ⊤))
          (θ : etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf) ⟶
            etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)),
        (∀ U : X.Etale, θ.hom.app (Opposite.op U) =
          ((tensorPullback U.hom).map (smulHom (SheafOfModules.unit X.ringCatSheaf) r)).app ⊤) →
        ∀ (U : X.Etaleᵒᵖ)
          (x : (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U),
          b U (θ.hom.app U x) =
            b U x * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) := by sorry

end AlgebraicGeometry.Scheme.Modules
