module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.CategoryTheory.ExactDerivedComposition
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normal form of the specified cocone derived comparison

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/
def-sfb-derived-extend-comp-iso.proof.md, exact-derived-composition paragraph and final
underived-composition sentence; the fixed construction `derivedExtendScalarsCompIso`.
(blueprint: lem-sfb-cocone-derived-comparison-normal-form)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits MonoidalCategory MonObj Abelian
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

/-- The normal-form composite: inverse exact-derived composition, followed by the
left derivation of the unit-compatible underived comparison and the specified equal-map
comparison. This helper shares the generic module-category structures before specializing
at the coefficient objects; it does not choose new comparison data.

Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit/
def-sfb-derived-extend-comp-iso.proof.md, exact-derived-composition paragraph;
`Adjunction.leftAdjointUniq` and `Mod.extendScalarsIsoOfEq`.
(blueprint: lem-sfb-cocone-derived-comparison-normal-form) -/
noncomputable def unitNormalizedDerivedScalarCompIso
    {V : Type u} [Category.{v} V] [Abelian V] [IsGrothendieckAbelian.{v} V]
    [MonoidalCategory V] [MonoidalPreadditive V] [SymmetricCategory V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V]
    {R S T : V} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
    (κ : R ⟶ T) [IsMonHom κ] (h : φ ≫ ψ = κ)
    [PreservesFiniteLimits (extendScalars φ)]
    [PreservesFiniteLimits (extendScalars ψ)]
    [PreservesFiniteLimits (extendScalars κ)] :
    (extendScalars φ).leftDerivedFunctor ⋙ (extendScalars ψ).leftDerivedFunctor ≅
      (extendScalars κ).leftDerivedFunctor :=
  haveI : PreservesFiniteLimits (extendScalars φ ⋙ extendScalars ψ) :=
    comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (extendScalars φ ⋙ extendScalars ψ) :=
    comp_preservesFiniteColimits _ _
  (Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
    Functor.leftDerivedFunctorNatIso (extendScalars φ ⋙ extendScalars ψ)
      (((((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
          (comapComp φ ψ).symm).leftAdjointUniq (extendRestrictAdjunction (φ ≫ ψ))) ≪≫
        extendScalarsIsoOfEq h)

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- The fixed cocone comparison is the inverse exact-derived composition comparison
followed by derivation of the unit-compatible underived adjunction comparison and the
specified coefficient-map equality comparison. All functors here are the specified total
left derived functors on the full unbounded derived categories of internal modules.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/
def-sfb-derived-extend-comp-iso.proof.md, entire paragraph; TwoColimit.lean, definition of
`derivedExtendScalarsCompIso`.
(blueprint: lem-sfb-cocone-derived-comparison-normal-form)

Proof:
1. Change of scalars preserves finite colimits. The subfield-flat and qlbar-flat lemmas
   give finite-limit preservation for the three coefficient extensions. The composite
   coefficient map equals the direct one by `padicSubfieldRingObjMap_comp_toPadicAlgCl`.
   The equality comparison transports exactness to extension along the composite map;
   the composite of the two extension functors is exact as well.
2. Compose the two extension/restriction adjunctions, identifying their right adjoint
   with restriction along the composite by `(Mod.comapComp _ _).symm`. The unit equation
   and uniqueness of `Adjunction.leftAdjointUniq` identify the inverse of the fixed
   `Mod.extendScalarsComp` with the left-adjoint comparison in the opposite order, namely
   the `leftAdjointUniq` displayed below. The second underived factor is exactly
   `Mod.extendScalarsIsoOfEq`, so their composite is the specified `e ∘ u`.
3. Expand `leftDerivedFunctorCompIso` through the exact-functor identifications with
   `mapDerivedCategory`. Cancelling these identifications gives the localization equation
   of `existsUnique_mapDerivedCategoryCompIso`, hence the fixed first factor is `c⁻¹`.
4. Expand `leftDerivedFunctorNatIso` through the same identifications. Its localized
   termwise components are those of `e ∘ u`, by `Localization.liftNatIso`. The localization
   equation and `Localization.natTrans_ext` uniquely identify this factor with `L(e ∘ u)`.
5. Substitute these two factors in the fixed `derivedExtendScalarsCompIso` construction.
   Its endpoints are definitionally the recorded `derivedExtendScalarsSubfield` and
   `derivedExtendScalarsToPadicAlgCl`, on objects and arrows. Equality of these natural
   isomorphisms specifies the comparison itself and inserts no derived automorphism.
-/
theorem derivedExtendScalarsCompIso_normalForm
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E H : FiniteIntermediateField ℓ} (h : E ≤ H) :
    derivedExtendScalarsCompIso X ℓ h =
      Mod.unitNormalizedDerivedScalarCompIso
        (padicSubfieldRingObjMap X ℓ h) (padicSubfieldRingObjToPadicAlgCl X ℓ H)
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h) :=
  sorry

end AlgebraicGeometry.ProEtale
