/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# The zero-section map of a rational point

Let `x` be a rational point of a `k`-scheme `X`, with ideal `I = ker x` and centre
`Z = V(I) ≅ Spec k`. The pullback exchange of the section `ẽ : S ⟶ 𝒳` of the deformation to the
normal cone of `x` (`ProEtale.CondensedRing.zeroSectionModelHom`) is the special case `Z = {x}` of
the zero-section map `ε_{X,Z}` of blueprint `det-sp-defect-definition`
(`ProEtale.CondensedRing.zeroSectionMap`): the constant family `Z × S` of the centre is isomorphic
to the trait `S` as a model, by the deformation `D_⊥ Z ≅ 𝔸¹_Z ≅ 𝔸¹_k` of the zero ideal of `Z`
(`ProEtale.CondensedRing.centreModelHom`), and `ẽ` factors through this isomorphism.

## Main results

- `ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isIso`: a morphism of
  models whose morphisms of total spaces and of geometric generic fibres are isomorphisms has an
  invertible pullback exchange.
- `ProEtale.CondensedRing.isIso_pullbackExchange_zeroSectionModelHom_app_of_isIso_zeroSectionMap`:
  if the zero-section map `ε_{X,Z}(K)` of the centre `Z = V(ker x)` is an isomorphism, then so is
  the pullback exchange of `ẽ` at `K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### The extended Rees algebra of the zero ideal -/

namespace Ideal

/-- The inclusion `R[t] ⟶ R[t, I t⁻¹]` is bijective for the zero ideal. -/
lemma bijective_toExtendedReesAlgebra_of_eq_bot {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I = ⊥) : Function.Bijective I.toExtendedReesAlgebra := by
  refine ⟨fun p q h ↦ Polynomial.toLaurent_injective (congrArg Subtype.val h), fun x ↦ ?_⟩
  obtain ⟨p, hp⟩ := mapRingHom_mem_range_toLaurent (RingHom.id R)
    (by rw [hI]; exact bot_le) x.2
  refine ⟨p, Subtype.ext ?_⟩
  rw [coe_toExtendedReesAlgebra, hp, LaurentPolynomial.mapRingHom_id]

end Ideal

namespace AlgebraicGeometry

/-- The morphism of affine spaces induced by an isomorphism is an isomorphism. -/
instance AffineSpace.isIso_map (n : Type*) {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f] :
    IsIso (AffineSpace.map n f) :=
  ⟨⟨AffineSpace.map n (inv f), by rw [← AffineSpace.map_comp, IsIso.hom_inv_id,
    AffineSpace.map_id], by rw [← AffineSpace.map_comp, IsIso.inv_hom_id, AffineSpace.map_id]⟩⟩

namespace Scheme.IdealSheafData

open AffineZariskiSite Opposite

variable {X : Scheme.{u}}

/-- The deformation space `D_⊥ X` of the zero ideal is the relative affine line `𝔸¹_X`. -/
instance isIso_deformationSpaceToPolynomialSpec_bot :
    IsIso (⊥ : X.IdealSheafData).deformationSpaceToPolynomialSpec :=
  relativeGluingMap_of_forall _ (MorphismProperty.isomorphisms _) _ _
    (⊥ : X.IdealSheafData).toPolynomialPresheaf_comp_polynomialToRees fun U ↦ by
      have : IsIso ((⊥ : X.IdealSheafData).polynomialToRees.app (op U)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          (Ideal.bijective_toExtendedReesAlgebra_of_eq_bot rfl)
      exact (inferInstance : IsIso (Spec.map _))

/-- The relative affine line `Spec_X (𝒪_X / ⊥)[t]` of the zero ideal is `𝔸¹_X`. -/
instance isIso_relativeGluingMap_polynomialToQuotientPolynomial_bot :
    IsIso (relativeGluingMap X.coequifibered_toPolynomialPresheaf
      (⊥ : X.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : X.IdealSheafData).polynomialToQuotientPolynomial) :=
  relativeGluingMap_of_forall _ (MorphismProperty.isomorphisms _) _ _
    (⊥ : X.IdealSheafData).toPolynomialPresheaf_comp_polynomialToQuotientPolynomial fun U ↦ by
      have : IsIso ((⊥ : X.IdealSheafData).polynomialToQuotientPolynomial.app (op U)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨Polynomial.map_injective _ ((RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker),
            Polynomial.map_surjective _ Ideal.Quotient.mk_surjective⟩
      exact (inferInstance : IsIso (Spec.map _))

end Scheme.IdealSheafData

namespace ProEtale.CondensedRing

open Scheme

/-! ### Morphisms of models with invertible total spaces -/

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}}

/-- The identity morphism of a model, over the identities. -/
@[simps]
def Hom.id (M : NearbyCyclesModel X X') : M.Hom M (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by rw [Category.id_comp, Category.comp_id]
  comm_i := by rw [Category.id_comp, Category.comp_id]
  comm_ε := by rw [Category.id_comp, Category.comp_id]

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- If the morphisms of total spaces and of geometric generic fibres of a morphism of models are
isomorphisms, its pullback exchange `α : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism: the base change
morphism of the square of geometric generic fibres is invertible by weakly étale base change. -/
lemma Hom.isIso_pullbackExchange_of_isIso (φ : M.Hom N f f') [IsIso φ.total] [IsIso φ.generic] :
    IsIso (φ.pullbackExchange Λ) := by
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom).natTrans := by
    have := isIso_baseChangeMap_of_weaklyEtale Λ (IsPullback.of_horiz_isIso φ.commSq_j)
    rwa [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv] at this
  unfold pullbackExchange
  infer_instance

end NearbyCyclesModel

/-! ### The constant family of the centre of a rational point -/

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (x : RationalPoint X)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The rational point `x`, as a point of the centre `Z = V(ker x)`. -/
noncomputable def centrePoint : (point k).left ⟶ (centre X x.left.ker).left :=
  x.left.toImage

@[reassoc (attr := simp)]
lemma centrePoint_centreι : centrePoint X x ≫ (centreι X x.left.ker).left = x.left :=
  x.left.toImage_imageι

instance : IsIso (centrePoint X x) := by
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  exact inferInstanceAs (IsIso x.left.toImage)

@[reassoc (attr := simp)]
lemma centrePoint_hom : centrePoint X x ≫ (centre X x.left.ker).hom = 𝟙 _ := by
  rw [← centrePoint_centreι_assoc, Over.w (centreι X x.left.ker)]
  exact Over.w x

instance : IsIso (centre X x.left.ker).hom := by
  have : IsIso (centrePoint X x ≫ (centre X x.left.ker).hom) := by
    rw [centrePoint_hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (centrePoint X x) _

/-- The deformation space of the zero ideal of the centre `Z = V(ker x) ≅ Spec k` is the affine
line `𝔸¹_k`. -/
instance : IsIso (deformationSpaceToAffineLine (centre X x.left.ker) ⊥) := by
  unfold deformationSpaceToAffineLine
  infer_instance

/-- The section `𝔸¹_k ≅ 𝔸¹_Z ⟶ Spec_Z (𝒪_Z / ⊥)[t]` of the relative affine line of the zero ideal
of the centre. -/
noncomputable def centreQuotientPolynomialSection :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶
      (⊥ : (centre X x.left.ker).left.IdealSheafData).quotientPolynomialSpec :=
  AffineSpace.map _ (centrePoint X x) ≫ inv (centre X x.left.ker).left.polynomialSpecToAffineSpace ≫
    inv (relativeGluingMap (centre X x.left.ker).left.coequifibered_toPolynomialPresheaf
      (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : (centre X x.left.ker).left.IdealSheafData).polynomialToQuotientPolynomial)

/-- The section `𝔸¹_k ⟶ D_⊥ Z` of the deformation space of the zero ideal of the centre. -/
noncomputable def centreDeformationSection :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶
      (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpace :=
  centreQuotientPolynomialSection X x ≫
    relativeGluingMap (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toReesPresheaf
      (⊥ : (centre X x.left.ker).left.IdealSheafData).coequifibered_toQuotientPolynomialAlgebra
      (⊥ : (centre X x.left.ker).left.IdealSheafData).reesToQuotientPolynomial

@[reassoc]
lemma centreDeformationSection_toPolynomialSpec :
    centreDeformationSection X x ≫
        (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpaceToPolynomialSpec =
      AffineSpace.map _ (centrePoint X x) ≫
        inv (centre X x.left.ker).left.polynomialSpecToAffineSpace := by
  rw [centreDeformationSection, IdealSheafData.deformationSpaceToPolynomialSpec, Category.assoc,
    ← relativeGluingMap_comp, IdealSheafData.polynomialToRees_comp_reesToQuotientPolynomial,
    centreQuotientPolynomialSection, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

@[reassoc (attr := simp)]
lemma centreDeformationSection_toAffineLine :
    centreDeformationSection X x ≫ deformationSpaceToAffineLine (centre X x.left.ker) ⊥ = 𝟙 _ := by
  rw [deformationSpaceToAffineLine, centreDeformationSection_toPolynomialSpec_assoc,
    IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp, centrePoint_hom, AffineSpace.map_id]

@[reassoc (attr := simp)]
lemma centreDeformationSection_toBase :
    centreDeformationSection X x ≫
        (⊥ : (centre X x.left.ker).left.IdealSheafData).deformationSpaceProj =
      (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) ≫ centrePoint X x := by
  sorry

/-- The section `𝔸¹_k ⟶ D_⊥ Z` maps to the section `𝔸¹_k ⟶ D_x X` given by `x`. -/
@[reassoc]
lemma centreDeformationSection_deformationSpaceMap :
    centreDeformationSection X x ≫ IdealSheafData.deformationSpaceMap (centreι X x.left.ker).left
        x.left.ker ⊥ (siteIdeal_map_appLE_le_bot X x.left.ker) =
      x.left.deformationSpaceSection := by
  sorry

end ProEtale.CondensedRing

end AlgebraicGeometry
