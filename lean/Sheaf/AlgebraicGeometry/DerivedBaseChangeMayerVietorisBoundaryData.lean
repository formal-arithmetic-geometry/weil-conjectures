module

public import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh

/-! Intermediate existence data for the relative Mayer--Vietoris boundary.
Source: Stacks Project, Tags 08BV and 0DJ9.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Existence of both canonical boundary morphisms and shift structures, together
with distinguishedness of the two cover triangles and their images.  The
compatibility equation is deliberately omitted; it is the separate remaining
part of the connecting-square argument.
Source: Stacks Project, Tags 08BV and 0DJ9.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data).
Proof: choose K-injective representatives with injective terms, apply the
short-exact Mayer--Vietoris presentation to each cover, and transport the
connecting morphism from `triangleOfSES` across the comparison isomorphisms.
The triangulated structures on derived pullback and direct image send the
resulting distinguished triangles to distinguished triangles. -/
theorem mvBoundary_data
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K') :
    ∃ (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
      (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶
          K'⟦(1 : ℤ)⟧)
      (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
      (csG : (schemeDerivedDirectImage f').CommShift ℤ),
      let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
        (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K δ
      let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V)
        (g' ⁻¹ᵁ (U ⊓ V)) ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' δ'
      T ∈ distTriang (schemeDerivedCategory X) ∧
      T' ∈ distTriang (schemeDerivedCategory X') ∧
      (@Functor.mapTriangle _ _ _ _ _ _
        (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj T ∈
        distTriang (schemeDerivedCategory S') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj T' ∈
        distTriang (schemeDerivedCategory S') := by
  sorry

/-- Remaining compatibility equation for boundaries carrying the distinguished
cover data. Its proof is the chain-level naturality and mate calculation.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-equation). -/
theorem mvBoundary_equation
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
      ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
    (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
      ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶ K'⟦(1 : ℤ)⟧)
    (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
    (csG : (schemeDerivedDirectImage f').CommShift ℤ)
    (hT : mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
      (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
      (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K δ ∈
      distTriang (schemeDerivedCategory X))
    (hT' : mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' δ' ∈
      distTriang (schemeDerivedCategory X')) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
        (letI := csF;
          (schemeDerivedDirectImage f ⋙ derivedPullback g).commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ)⟦(1 : ℤ)⟧' =
      mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V) ≫
        (schemeDerivedDirectImage f').map δ' ≫
        (letI := csG; (schemeDerivedDirectImage f').commShiftIso (1 : ℤ)).hom.app K' := by
  sorry

end AlgebraicGeometry
