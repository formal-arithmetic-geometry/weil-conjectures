/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement

/-!
# The specified finite constant-scalar comparison

Source: the finite coefficient interpretation of the etale-origin witness in the
proper-base-change blueprint; Bhatt--Scholze, Lemma 4.2.12.
(blueprint: lem-route-finite-origin-constant-comparison-is-iso).

Ring sheaves are expressed as ring objects of tensor abelian sheaves. All scalar
maps below are constructed from constant functions and sheafification adjunctions.
The auxiliary coefficient sheaf is the published connected-component presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteOriginCoefficients

variable (T : Scheme.{u}) (Λ : Type u) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Constants into the actual continuous-map condensed ring presheaf.
Source: blueprint finite coefficient interpretation, proof step 1
(blueprint: lem-route-finite-origin-constant-comparison-is-iso). -/
def pointConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} Λ)) ⟶
      Profinite.continuousCoefficientRingPresheaf Λ where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- Sheafifying constant functions gives the specified point comparison.
Source: blueprint finite coefficient interpretation, proof step 1
(blueprint: lem-route-finite-origin-constant-comparison-is-iso). -/
def pointComparison :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} Λ))) ⟶
      Profinite.continuousCoefficientRingObj Λ :=
  (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (Functor.whiskerRight (pointConstants Λ) (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
    (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
      (Profinite.continuousCoefficientRingSheaf Λ)).hom

/-- The canonical constant-scalar map to the condensed coefficient pullback.
The first arrow is the fixed comparison obtained by conjugating terminal sections
under the constant-sheaf and inverse-image adjunctions; the second is inverse image
of the constant-function comparison. Thus the transpose is pullback of scalars.
Source: blueprint finite coefficient interpretation, proof step 2
(blueprint: lem-route-finite-origin-constant-comparison-is-iso). -/
def constantComparison :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} Λ))) ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj Λ) T :=
  (constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} Λ)) ≫
    (upperStarFromPoint T).map (pointComparison Λ)

/-- The abelian sheaf of the published finite coefficient ring G^#.
This is the existing ring sheaf, with its existing sectionwise multiplication.
Source: blueprint finite coefficient interpretation, second paragraph
(blueprint: lem-route-finite-origin-constant-comparison-is-iso). -/
abbrev functionRing : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (finiteCoefficientRingSheaf T (ULift.{u + 1} Λ))

/-- The unique extension of the published constant scalars to G^#.
Source: blueprint finite coefficient interpretation, proof step 3
(blueprint: lem-route-finite-origin-constant-comparison-is-iso). -/
def functionComparison :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} Λ))) ⟶
      functionRing T Λ :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerRight (finiteCoefficientScalarMap T (ULift.{u + 1} Λ))
      (forget₂ RingCat.{u + 1} Ab.{u + 1}))

end AlgebraicGeometry.ProEtale.FiniteOriginCoefficients
