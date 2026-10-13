/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Extending a balanced action to the direct-image algebra

Source: Stacks Project, Tags 01LX, 01SB and the relative-spectrum paragraph of 0897.
(blueprint: lem-weil-pbc-balanced-action-direct-image-module).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- Extend the balanced action to the direct-image structure algebra, without realizing
its module on the base-changed scheme.

Source: Stacks Project, Tags 01LX and 01SB; Tag 0897, relative-spectrum paragraph.
(blueprint: lem-weil-pbc-balanced-action-direct-image-module).

Proof: On an affine open U = Spec C, the section module N = M(U) has the given
commuting C- and B-actions. The scalar hypothesis balances their A-actions.
Consequently (c tensor b)n = c rho(b)n defines a C tensor_A B-module structure on N.
The ring of the inverse image of U in Y is canonically C tensor_A B, by affine
base change (01LX). On a basic open D(c) in U, quasi-coherence identifies M(D(c))
with N localized at c. Naturality of rho makes this identification B-linear.
Thus the extended actions commute with restriction to basic affine opens.
Refine affine overlaps by basic affine opens; these compatible actions uniquely
glue to a pi_* O_Y-module sheaf G. Its underlying abelian sheaf is the abelian
sheaf of M, with its original O_X-action because the construction sends c tensor 1
to multiplication by c. This supplies the restriction-of-scalars isomorphism e.
The section fB-sharp(b), restricted to the inverse image of U, corresponds to
1 tensor b. Its action is therefore rho(b) on U. The same equality on arbitrary
opens follows by the sheaf axiom from an affine cover. All module and restriction
maps are the constructed ones, not arbitrary witnesses of existence.
For the zero module the actions are zero, and on an empty scheme the sectionwise
construction uses the unique maps; neither case needs a finiteness assumption. -/
theorem balancedAction_directImage_module
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (M : X.Modules) (hM : M.IsQuasicoherent)
    (rho : B →+* End M)
    (hscalar : ∀ a : A, rho (algebraMap A B a) =
      M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
    let R := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
    let S := SheafOfModules.restrictScalars.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
        (show X.sheaf ⟶ C from ⟨pi.c⟩))
    ∃ (G : SheafOfModules.{u} R) (e : M ≅ S.obj G),
      ∀ (b : B) (U : X.Opens) (x : M.val.obj (op U)),
        (e.hom.val.app (op U)).hom ((rho b).val.app (op U) x) =
          Y.presheaf.map (homOfLE (le_top (a := pi ⁻¹ᵁ U))).op
            (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b) •
              (show G.val.obj (op U) from (e.hom.val.app (op U)).hom x) := by sorry

end AlgebraicGeometry
