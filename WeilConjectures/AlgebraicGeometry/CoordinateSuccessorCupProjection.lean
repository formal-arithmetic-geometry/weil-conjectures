/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSuccessorCup
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionArrows

/-! # Binary supported cup and the last-section projection

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, projection formula sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

attribute [local irreducible] projectionMap

private theorem tensor_section_unit_naturality {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (F : C ⥤ C) (E : F ≅ 𝟭 C) {M K L : C}
    (e : M ≅ 𝟙_ C) (α : K ⟶ L) :
    (𝟙 M ⊗ₘ F.map α) ≫ (e.hom ⊗ₘ E.hom.app L) ≫ (λ_ L).hom =
      (e.hom ⊗ₘ E.hom.app K) ≫ (λ_ K).hom ≫ α := by
  have hn := E.hom.naturality α
  change F.map α ≫ E.hom.app L = E.hom.app K ≫ α at hn
  calc
    _ = (e.hom ⊗ₘ F.map α ≫ E.hom.app L) ≫ (λ_ L).hom := by
      rw [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (e.hom ⊗ₘ E.hom.app K ≫ α) ≫ (λ_ L).hom := by rw [hn]
    _ = (e.hom ⊗ₘ E.hom.app K) ≫ (𝟙_ C ◁ α) ≫ (λ_ L).hom := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = _ := by
      rw [leftUnitor_naturality]
      simp only [Functor.id_obj]

/-- The section endpoint identification is natural in its coefficient input.
Source: naturality of the projection formula in the zero-section product.
(blueprint: lem-pur-coordinate-successor-cup-projection).
Proof: the pullback compositor and section equation form a natural isomorphism
from the double inverse image to identity. Its naturality moves the input map
through the second tensor factor. Tensor bifunctoriality moves it past the
coefficient-unit comparison, and naturality of the left unitor finishes. -/
theorem sectionTensorRaw_naturality (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) (α : K ⟶ L) :
    ((tensor A Y).obj M).map
        ((inverseImage A s).map ((inverseImage A q).map α)) ≫
      (sectionTensorRaw A s q h M L e).hom =
        (sectionTensorRaw A s q h M K e).hom ≫ α := by
  let F := inverseImage A q ⋙ inverseImage A s
  let E : F ≅ 𝟭 _ := (inverseImageComp A s q).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h ≪≫ inverseImageId A Y
  have hn := tensor_section_unit_naturality F E e α
  unfold sectionTensorRaw AffineSpacePurity.tensorIso tensorUnitLeftIso
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp, AffineSpacePurity.tensor, derivedTensor,
    curriedTensor_obj_map, curriedTensor_map_app, MonoidalCategory.tensorHom_def, Category.assoc,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, id_whiskerRight,
    Category.id_comp, F, E] using hn

/-- The chosen section arrow satisfies its precise projection equation.
Source: the inverse projection definition in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-cup-projection).
Proof: project the characterizing equality of the uniquely chosen section arrow.
Convert its heterogeneous equality to equality; the endpoints are the specified
section projection and tensor target normalization. -/
theorem coordinate_sectionArrow_projection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    sectionProjection P n B r ≫ sectionArrow P n B aB r =
      tensorArrow (tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1)))
        (lastProduct P n B aB r)
        ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
          (target P n (iteratedAffineLine B r) r)) (sectionTargetIso P n B aB r) := by
  unfold sectionArrow
  exact eq_of_heq (sectionArrow_existsUnique P n B aB r).exists.choose_spec

/-- Cupping an arbitrary supported input with the last boundary is the section
arrow after direct image of that input. No coordinate product is assumed for α.
Source: the coefficient multiplication and projection formula sentence of the
affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-cup-projection).

Proof: identify each closed compact-support source with exact direct image of
its coefficient in degree zero, using closedSingleIso. The complement is
quasi-compact by Noetherian geometry. The old-support square is
successorTailSquare. The proved successorLastCoordinateIso identifies the newest
divisor with the last section, and successorLastIntersection_isPullback identifies
its intersection with the old support with B over the total zero section. On
underived closed coefficients, both the binary cup multiplication and the
proper projection followed by the section unitor multiply the two restricted
constant sections on this intersection. The normalized restriction maps are
epic, and tensoring preserves epimorphisms, so they determine the same map.
Apply the degree-zero tensor comparison to this equality. Exactness of closed
direct image identifies its derived single comparison with closedSingleIso;
transposing the projection map through the ordinary pullback/direct-image
adjunction shows that its single component is that same underived projection:
the tensor pullback comparison is followed by the tensor of the counit with the
identity. Proper compact-support comparison transports this equation to the
specified compactification, and its composition coherence gives precisely
coordinateComposition. Naturality in the arbitrary map α then moves α through
the projection component. At the last factor the singleton product is the
boundary followed by the canonical coefficient unitor; the binary cup unit law
cancels its empty factor. The target symmetry interchanges the pulled-back old
power and the last line; with oneTargetIso and targetPullbackIso this is exactly
sectionTargetIso. The twists are even, so no sign remains. Finally the defining
equation sectionProjection followed by sectionArrow equals tensorArrow, and
invertibility of sectionProjection on the finite Tate target, give the displayed
equation. Only a single binary cup and an arbitrary input occur in this
calculation. It uses neither Cartier pullback naturality nor a recurrence for
the old coordinate product; the zero-rank and empty-base cases use the same
unit and counit identities. -/
theorem coordinate_successor_cup_projection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B r)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B r) r) :
    let := zero_exact P n B aB r
    let := zero_exact P n B aB (r + 1)
    (closedSingleIso (setting P n).Coefficient (zero B (r + 1))
      ((setting P n).constant B)).hom ≫
        successorCup P n B aB r
          ((successorTailSourcePullback P n B r).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map α ≫
              (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map
            ((closedSingleIso (setting P n).Coefficient (zero B r)
              ((setting P n).constant B)).hom ≫ α) ≫ sectionArrow P n B aB r := by
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
