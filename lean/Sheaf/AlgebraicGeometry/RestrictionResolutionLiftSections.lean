/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Sections of a restriction-adjunction lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-restriction-resolution-lift-sections).
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Evaluate a restriction-adjunction lift on sections, with arbitrary resolutions
and their prescribed restriction comparisons. This calculation involves one scheme
map only, and no base-change square or equality between composite inverse images.
Source: Stacks Project, Tags 01FB and 01E4, the resolution and open-section
calculation; Mathlib AlgebraicGeometry.Modules.Sheaf, restriction unit/counit.
(blueprint: lem-weil-restriction-resolution-lift-sections).
Proof: Work in each degree. Expand the adjoint as restriction of b followed by
its counit. The counit is restriction along the equality U.ι⁻¹(U.ι(top))=top.
The unit on J restricts from p⁻¹(U.ι(top)) to W.ι(W.ι⁻¹(p⁻¹(U.ι(top)))).
The two pushforward composition comparisons are identity on sections and the
congruence comparison restricts along the equality p ∘ W.ι = U.ι ∘ h.
Use naturality to move the inverse target comparison past the counit and the
specified a.inv restriction. Use B.components to expand the final section
comparison and cancel B.comparison.inv against B.comparison.hom. Compose all
remaining restrictions by presheaf functoriality. The resulting restriction
is the equality W.ι(top)=W. Expand A.components and use naturality of t to
obtain A.sections.hom followed by evaluation of t on U. The calculation uses
neither injectivity nor the augmentations. For U empty all section groups are
zero; for p an identity it is the cancellation of the restriction comparisons. -/
theorem restrictionResolutionLift_sections {X Y : Scheme.{uBC}}
    (p : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (t : I.cocomplex ⟶ ((pushforward p).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (U : X.Opens) (A : RestrictedResolutionSections I U)
    (B : RestrictedResolutionSections J (p ⁻¹ᵁ U)) :
  let W := p ⁻¹ᵁ U
  letI : (restrictFunctor U.ι).Additive :=
    (restrictAdjunction U.ι).left_adjoint_additive
  let h := p.resLE U W le_rfl
  let C := B.resolution.cocomplex
  let P := (pushforward U.ι).mapHomologicalComplex (ComplexShape.up ℕ)
  let H := (pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let G := (pushforward p).mapHomologicalComplex (ComplexShape.up ℕ)
  let e₁ := NatIso.mapHomologicalComplex (pushforwardComp W.ι p)
    (ComplexShape.up ℕ)
  let e₂ := NatIso.mapHomologicalComplex
    (pushforwardCongr (p.resLE_comp_ι (U := U) (V := W) le_rfl))
    (ComplexShape.up ℕ)
  let e₃ := NatIso.mapHomologicalComplex (pushforwardComp h U.ι) (ComplexShape.up ℕ)
  let w := ((restrictAdjunction W.ι).unit.mapHomologicalComplex
    (ComplexShape.up ℕ)).app J.cocomplex
  let b : I.cocomplex ⟶ P.obj (H.obj C) :=
    t ≫ G.map w ≫ e₁.hom.app (((restrictFunctor W.ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₂.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₃.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      P.map (H.map B.comparison.inv)
  let k := A.comparison.hom ≫
    (((restrictAdjunction U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv
      I.cocomplex (H.obj C)).symm b
  let ΓS := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
  let ΓT := (RingedSpace.globalSectionsFunctor (p ⁻¹ᵁ U).toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)
  ∀ (a : ΓT.obj B.resolution.cocomplex ≅ ΓS.obj (H.obj B.resolution.cocomplex)),
    (∀ n : ℕ, a.inv.f n = (B.resolution.cocomplex.X n).presheaf.map
      (eqToHom (by simp) : (⊤ : (p ⁻¹ᵁ U).toScheme.Opens) ⟶
        h ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op) →
    ΓS.map k ≫ a.inv ≫ B.sections.hom =
      A.sections.hom ≫
        ((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℕ)).map t := by sorry

end AlgebraicGeometry.Scheme.Modules
