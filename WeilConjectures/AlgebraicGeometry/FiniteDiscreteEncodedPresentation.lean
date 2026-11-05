/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Finite presentations under finite discrete encoding -/

@[expose] public section

universe u v w v₁ v₂ u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace CategoryTheory.ConstantInternalModuleSheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]
  (G : Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = Mod.forget (AddCommGrpCat.of R))
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasSheafify J (ModuleCat.{w} R)]

local instance : HasWeakSheafify J Ab.{w} := HasSheafify.isRightAdjoint
local instance : HasWeakSheafify J (ModuleCat.{w} R) := HasSheafify.isRightAdjoint

noncomputable local instance : MonoidalCategory (Sheaf J Ab.{w}) :=
  Sheaf.monoidalCategory J Ab.{w}
noncomputable local instance : BraidedCategory (Sheaf J Ab.{w}) :=
  Sheaf.braidedCategory J Ab.{w}

@[irreducible] private noncomputable def encSheafifyIso :
    (presheafToSheaf J Ab.{w}).mapMod (A (C := Cᵒᵖ) R) ⋙ sheafEncoding J R G hG ≅
      modulePresheafEncoding (C := C) R G ⋙ presheafToSheaf J (ModuleCat.{w} R) := by
  let H := sheafEncoding J R G hG
  let P := modulePresheafEncoding (C := C) R G
  let Q := moduleLocalizationRight J (A (C := Cᵒᵖ) R)
  let U := sheafToPresheaf J (ModuleCat.{w} R)
  let e : Q ⋙ P ≅ H ⋙ U := Iso.refl _
  let i : (H.inv ⋙ Q) ⋙ P ≅ U :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H.inv e ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight H.asEquivalence.counitIso U ≪≫ Functor.leftUnitor U
  let j : H.inv ⋙ Q ≅ U ⋙ P.inv := Iso.isoCompInverse (H := P.asEquivalence) i
  exact ((moduleLocalizationAdjunction J (A (C := Cᵒᵖ) R)).comp
    H.asEquivalence.toAdjunction).ofNatIsoRight j |>.leftAdjointUniq
      (P.asEquivalence.toAdjunction.comp (sheafificationAdjunction J (ModuleCat.{w} R)))

@[irreducible] private noncomputable def encPresheafRegularIso :
    (modulePresheafEncoding (C := C) R G).obj (Mod.regular (A (C := Cᵒᵖ) R)) ≅
      (Functor.const Cᵒᵖ).obj (G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  refine NatIso.ofComponents (fun U ↦ ?_) (fun f ↦ ?_)
  · exact G.mapIso (Mod.isoMk (Iso.refl _) (by simp))
  · change G.map _ ≫ G.map _ = G.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← G.map_comp]
    congr 1

@[irreducible] private noncomputable def encRegularIso :
    (sheafEncoding J R G hG).obj
      (Mod.regular ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R))) ≅
      (constantSheaf J (ModuleCat.{w} R)).obj (G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  let e : ((presheafToSheaf J Ab.{w}).mapMod (A (C := Cᵒᵖ) R)).obj
      (Mod.regular (A (C := Cᵒᵖ) R)) ≅
      Mod.regular ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) :=
    Mod.isoMk (Iso.refl _) (by simp)
  exact (sheafEncoding J R G hG).mapIso e.symm ≪≫
    (encSheafifyIso J R G hG).app _ ≪≫
    (presheafToSheaf J (ModuleCat.{w} R)).mapIso (encPresheafRegularIso R G)

variable [HasFiniteLimits (Mod (Sheaf J Ab.{w})
  ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)))]

@[irreducible] private noncomputable def encFiniteFreeIso (n : ℕ) :
    (sheafEncoding J R G hG).obj
      (Mod.finiteFree ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) n) ≅
      (constantSheaf J (ModuleCat.{w} R)).obj
        (⨁ fun _ : Fin n ↦ G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  let H := sheafEncoding J R G hG
  let S := constantSheaf J (ModuleCat.{w} R)
  have : H.IsEquivalence := sheafEncodingIsEquivalence J R G hG
  have : H.Full := sheafEncodingFull J R G hG
  have : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full H
  have : HasBinaryProducts (Mod (Sheaf J Ab.{w})
      ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R))) :=
    HasFiniteLimits.out _
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have : PreservesFiniteColimits S := inferInstance
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  exact H.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ encRegularIso J R G hG) ≪≫
    (S.mapBiproduct _).symm

variable [PreservesFiniteColimits
  (tensorLeft ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)))]

end CategoryTheory.ConstantInternalModuleSheafEncoding

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

local instance : HasWeakSheafify (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint
local instance : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := coherentTopology Profinite.{u}) (A := Ab.{u + 1})
noncomputable local instance :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (coherentTopology Profinite.{u}) Ab.{u + 1}

local instance (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint
local instance (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})
noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

open MonoidalCategory

section Presentation

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {S : D} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

end Presentation

section SheafPresentation

variable {X : AlgebraicGeometry.Scheme.{u}}
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S]

@[irreducible] private noncomputable def finiteFree_comap
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ] (n : ℕ) :
    (Mod.comap φ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

end SheafPresentation

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- Inverse image with coefficients identified by restriction of scalars.
Keep the composite irreducible so iterated restrictions use the proved API below. -/
@[irreducible] private noncomputable def normalizedPullback (T U : Scheme.{u})
    (j : U ⟶ T) : FiniteDiscreteInternalModules B T ⥤ FiniteDiscreteInternalModules B U :=
  ((ProEtale.upperStar Ab.{u + 1} j).mapMod
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)) ⋙
      Mod.comap (inv (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j))

end AlgebraicGeometry.ProEtale.CondensedRing
