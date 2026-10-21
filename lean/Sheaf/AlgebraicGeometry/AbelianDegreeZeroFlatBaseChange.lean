/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange

/-!
# Degree-zero flat base change for abelian étale sheaves

Source: Stacks Project, Étale Cohomology, Tag 0EYS, and blueprint
sec-smooth-purity/sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0eys).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Flat, locally finitely presented inverse image with geometrically reduced fibres
commutes with direct image for every abelian étale sheaf, under arbitrary base change.
The arrow is the recorded underived exchange for the transposed square: its transpose
under `upperStar h ⊣ lowerStar h` is the square inverse-image comparison followed by
`upperStar e` applied to the counit for `g`.
Source: Stacks Project, Tag 0EYS; blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary
(blueprint: lem-kun-0eys).

Proof:
1. Forget abelian sheaves to sets. The comparison and adjunction bijections of
   lem-weil-pbc-etale-inverse-image-algebraic-structures preserve units and counits
   (a counit is the transpose of an identity). By the unit characterization in
   lem-weil-pbc-inverse-image-composition and uniqueness in
   lem-weil-pbc-sets-etale-inverse-image-composition-units, they preserve composition
   comparisons. The formula in lem-weil-pbc-square-iso-pasting then identifies the
   forgotten square comparison with the set square comparison. Consequently the
   forgotten exchange has transpose h⁻¹f⁻¹g_*F → e⁻¹g⁻¹g_*F → e⁻¹F, as required.
2. Write L and R for set inverse and direct images, A = R_g F, B = L_e F, and
   α : L_h L_f ≅ L_e L_g. Exchange is m = R_h(L_e ε_g ∘ α_A) ∘ η_h.
   The composite-unit equation of
   lem-weil-pbc-sets-etale-inverse-image-composition-units says
   R_f R_h(α_A) ∘ R_f(η_h) ∘ η_f = R_g(η_e) ∘ η_g.
   Thus R_f(m) ∘ η_f = R_g R_e(L_e ε_g) ∘ R_g(η_e) ∘ η_g
   = R_g(η_e) ∘ R_g(ε_g) ∘ η_g = R_g(η_e), by naturality and the triangle
   identity. This is the defining transpose of the set exchange in
   sbc-lem-degree-zero-flat-base-change. That theorem makes the forgotten arrow
   invertible, with exactly the given flatness, presentation and fibre hypotheses.
3. Each component of exchange is therefore a bijective group homomorphism. Its
   inverse preserves zero and addition by injectivity of that homomorphism.
   Naturality of the inverses follows by composing the desired equation with the
   bijective component and using naturality of exchange. The inverses give a
   morphism of abelian sheaves (def-weil-pbc-abelian-etale-sheaves), with both
   composites equal to identities. Hence the specified abelian exchange is an
   isomorphism. No restriction on g and no torsion assumption is used. -/
theorem isIso_abelianBaseChangeMap_of_flat
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq.flip).app F) := by
  let U (Z : Scheme.{u}) :=
    sheafForget (D := AddCommGrpCat.{u + 1}) Z.smallEtaleTopology
  let La {Z W : Scheme.{u}} (k : Z ⟶ W) := upperStar AddCommGrpCat.{u + 1} k
  let Ra {Z W : Scheme.{u}} (k : Z ⟶ W) := lowerStar AddCommGrpCat.{u + 1} k
  let Rs {Z W : Scheme.{u}} (k : Z ⟶ W) := lowerStar (Type (u + 1)) k
  let aa {Z W : Scheme.{u}} (k : Z ⟶ W) :=
    upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} k
  obtain ⟨ef, hfadj⟩ := etaleInverseImageAbelianLift_hom X S f
    (etaleInverseImageAlgebraicStructures X S f).1
  obtain ⟨ee, headj⟩ := etaleInverseImageAbelianLift_hom Y T e
    (etaleInverseImageAlgebraicStructures Y T e).1
  let β := (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq.flip).app F
  -- The hom-set comparison sends the abelian unit to the set unit.
  have heunit : (U T).map ((aa e).unit.app F) ≫
      (Rs e).map (ee.hom.app F) = (setUpperLowerAdjunction e).unit.app ((U T).obj F) := by
    have he := headj F _ (𝟙 _)
    rw [Adjunction.homEquiv_id, CategoryTheory.Functor.map_id] at he
    erw [Category.comp_id] at he
    erw [he, ← Adjunction.homEquiv_naturality_right]
    rw [ee.inv_hom_id_app]
    exact (setUpperLowerAdjunction e).homEquiv_id _
  -- Compare exchange by its adjunct under inverse image along f.
  have hcomp :
      (ef.inv.app ((Ra g).obj F) ≫ (U X).map β) ≫
        (Rs h).map (ee.hom.app F) = setBaseChangeArrow sq ((U T).obj F) := by
    apply ((setUpperLowerAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    erw [← hfadj]
    rw [Adjunction.homEquiv_unit, unit_map_baseChangeMap_app]
    rw [show setBaseChangeArrow sq ((U T).obj F) =
      ((setUpperLowerAdjunction f).homEquiv _ _).symm
        ((Rs g).map ((setUpperLowerAdjunction e).unit.app ((U T).obj F)) ≫
          (lowerStarComp (Type (u + 1)) e g).hom.app _ ≫
          (lowerStarComp (Type (u + 1)) h f (e ≫ g) sq.w.symm).inv.app _) from rfl]
    erw [Equiv.apply_symm_apply]
    -- Direct-image composition uses the same restriction maps after forgetting.
    have hsq : (U S).map
        ((squareLowerStarIso AddCommGrpCat.{u + 1} sq.toCommSq.flip).hom.app
          ((La e).obj F)) =
        (lowerStarComp (Type (u + 1)) e g).hom.app ((U Y).obj ((La e).obj F)) ≫
          (lowerStarComp (Type (u + 1)) h f (e ≫ g) sq.w.symm).inv.app
            ((U Y).obj ((La e).obj F)) := by
      ext V x
      rfl
    rw [(U S).map_comp, hsq]
    let cs := lowerStarComp (Type (u + 1)) e g ≪≫
      (lowerStarComp (Type (u + 1)) h f (e ≫ g) sq.w.symm).symm
    change ((Rs g).map ((U T).map ((aa e).unit.app F)) ≫
        cs.hom.app ((U Y).obj ((La e).obj F))) ≫
        (Rs h ⋙ Rs f).map (ee.hom.app F) =
      (Rs g).map ((setUpperLowerAdjunction e).unit.app ((U T).obj F)) ≫
        cs.hom.app ((Scheme.etaleSetPullback e).obj ((U T).obj F))
    rw [Category.assoc, ← cs.hom.naturality, ← Category.assoc]
    dsimp only [CategoryTheory.Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, heunit]
    rfl
  -- The forgetful functor reflects isomorphisms of abelian sheaves.
  have := isIso_etaleSetDegreeZeroBaseChange_of_flat sq hf ((U T).obj F)
  have : IsIso ((U X).map β) := by
    have : IsIso ((ef.inv.app ((Ra g).obj F) ≫ (U X).map β) ≫
        (Rs h).map (ee.hom.app F)) := hcomp ▸ inferInstance
    simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using this
  exact isIso_of_reflects_iso β (U X)

end AlgebraicGeometry.Etale
