/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.FieldScalarStrictLimitData

/-! # Finite-basis coordinates and balanced ordinary scalar composition -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RingedTensor
namespace SheafOfModules
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The ordinary finite-basis tensor presentation and balanced scalar structure maps.
Source: blueprint field-extension-towers proof (1), and the coordinate calculations
in lem-sp-field-scalar-strict-limit, steps 1, 3 and 5.
(blueprint: lem-sp-field-scalar-ordinary-coordinates).

Proof: For a basis theta of S over R, expand the S factor in a pure tensor using
its coordinate maps theta.inv followed by the product projections. This gives phi;
its inverse is the finite sum of basis vectors tensored with the coordinates of M.
Both composites are identities by the basis equations and the balancing relation.
The formulas commute with restrictions, so descend through module sheafification.
For R to S to U, pair the two finite bases to obtain a basis of U over R, including
an empty basis when either rank is zero. The balanced associator is induced by
z tensor (s tensor x) mapping to b(s)z tensor x, and its inverse inserts one.
The balancing relations give its inverse equations; apply it termwise for AT.
For the identity ring map, use the one-element basis of R. Multiplication r tensor x
mapping to rx is the unitor, with inverse x mapping to one tensor x; apply it termwise.
These constructions and formulas apply to arbitrary module sheaves on any small site.
No derived functor or Roos comparison is asserted here. -/
theorem fieldScalarOrdinaryCoordinates :
    (∀ {R S : Sheaf J CommRingCat.{u}} (a : FiniteFreeScalarArrow J R S)
          (d : ℕ) (theta : (∏ᶜ fun _ : Fin d ↦ unit (ringSheaf R)) ≅
            (restriction a.val).obj (unit (ringSheaf S))),
          ∃ phi : tensorFunctor a.val ⋙ restriction a.val ≅
              Functor.const (Discrete (Fin d)) ⋙ lim,
            (∀ (M : SheafOfModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d),
              (phi.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
                  (scalarPure a.val M V s m) =
                (theta.inv ≫ Pi.π (fun _ : Fin d ↦ unit (ringSheaf R)) i).val.app V s
                  • m) ∧
            (∀ (M : SheafOfModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (x : ((Functor.const (Discrete (Fin d)) ⋙ lim).obj M).val.obj V),
              (phi.inv.app M).val.app V x =
                ∑ i : Fin d, scalarPure a.val M V
                  ((Pi.lift (fun j : Fin d ↦ if i = j then 𝟙 _ else 0) ≫ theta.hom).val.app V
                    (@id ((unit (ringSheaf R)).val.obj V) (1 : R.obj.obj V)))
                  ((Pi.π (fun _ : Fin d ↦ M) i).val.app V x))) ∧
    (∀ {R S U : Sheaf J CommRingCat.{u}}
          (a : FiniteFreeScalarArrow J R S) (b : FiniteFreeScalarArrow J S U),
          ∃ (ab : FiniteFreeScalarArrow J R U) (_hab : ab.val = a.val ≫ b.val)
            (A : tensorFunctor a.val ⋙ tensorFunctor b.val ≅ tensorFunctor ab.val)
            (AT : projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val) ⋙
                projectionPost (I := ℕᵒᵖ) (tensorFunctor b.val) ≅
                  projectionPost (I := ℕᵒᵖ) (tensorFunctor ab.val)),
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (s : S.obj.obj V) (z : U.obj.obj V) (x : M.val.obj V),
              (A.hom.app M).val.app V
                  (scalarPure b.val ((tensorFunctor a.val).obj M) V z
                    (scalarPure a.val M V s x)) =
                scalarPure ab.val M V (b.val.hom.app V s * z) x) ∧
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (z : U.obj.obj V) (x : M.val.obj V),
              (A.inv.app M).val.app V (scalarPure ab.val M V z x) =
                scalarPure b.val ((tensorFunctor a.val).obj M) V z
                  (scalarPure a.val M V 1 x)) ∧
            (∀ (X : ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) (n : ℕᵒᵖ),
              (AT.hom.app X).app n = A.hom.app (X.obj n))) ∧
    (∀ R : Sheaf J CommRingCat.{u},
          ∃ (a : FiniteFreeScalarArrow J R R) (_ha : a.val = 𝟙 R)
            (U : tensorFunctor a.val ≅ 𝟭 (ringedSiteModules.{u} (ringSheaf R)))
            (UT : projectionPost (I := ℕᵒᵖ) (tensorFunctor a.val) ≅
              𝟭 (ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R))),
            (∀ (M : ringedSiteModules.{u} (ringSheaf R)) (V : Cᵒᵖ)
              (r : R.obj.obj V) (x : M.val.obj V),
              (U.hom.app M).val.app V (scalarPure a.val M V r x) = r • x) ∧
            (∀ (X : ℕᵒᵖ ⥤ ringedSiteModules.{u} (ringSheaf R)) (n : ℕᵒᵖ),
              (UT.hom.app X).app n = U.hom.app (X.obj n))) := by sorry

end SheafOfModules
