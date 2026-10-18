/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ProjectionFormulaArrows
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Projection arrows on the original small pro-etale sites

Source: proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
This repairs only the site-universe interface and reexports the existing general arrows.
The inverse is the localization of the specified finite-total chain inverse.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Unit normalization of the canonical ordinary comparison on the original site.
Source: definition 1264, ordinary finite-free identification
(blueprint: def-weil-pbc-projection-formula-arrows).
Proof: scalar multiplication identifies pullback of the coefficient ring with the
coefficient ring. On m tensor r both displayed routes multiply by the image of r.
Pure tensors generate and sheafification is universal. At the unit this equation
uniquely determines the unit identification. -/
theorem proEtaleProjectionUnit_existsUnique :
    ∃! j : (proEtaleRingModulePullback f R S c).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
        SheafOfModules.unit ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S),
      ∀ M : proEtaleRingModules Y R,
        (proEtaleOrdinaryTensorPullback f R S c M
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))).hom ≫
          (SheafOfModules.monoidalCategory S).tensorHom
            (𝟙 ((proEtaleRingModulePullback f R S c).obj M)) j.hom ≫
          ((SheafOfModules.monoidalCategory S).rightUnitor
            ((proEtaleRingModulePullback f R S c).obj M)).hom =
        (proEtaleRingModulePullback f R S c).map
          (((SheafOfModules.monoidalCategory R).rightUnitor M).hom) := sorry

/-- Bounded split-free coefficients are flat and K-flat on the original site.
Source: definition 1264, representatives C and J
(blueprint: def-weil-pbc-projection-formula-arrows).
Proof: tensoring each finite-free retract is a retract of a finite sum of the identity.
It is exact, so the term is flat. The bounded-above flat K-flat lemma, transported
through the model-site equivalence, proves K-flatness with the original site universes. -/
theorem proEtaleStrictPerfect_flat
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
    (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    proEtaleFlatRepresentatives Y R F := sorry

/-- Mixed tensor representatives, normalized at every flat K-flat resolution.
Source: definition 1264, displayed representatives C and J
(blueprint: def-weil-pbc-projection-formula-arrows).
Proof: resolve A by a flat K-flat P. Tensoring this resolution with the K-flat F is a
quasi-isomorphism. Compose its localization with the inverse model representative
comparison and the inverse of tensor applied to the resolution. Common refinements
and naturality give the square for every resolution. Its invertible left factor
also proves uniqueness. This changes no object universe or coefficient category. -/
theorem proEtaleMixedTensor_existsUnique (a : ProEtaleTensorModel Y R)
    (A F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hf : proEtaleFlatRepresentatives Y R F) :
    ∃! z : a.tensor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F (proEtaleOrdinaryTensor Y R)),
      ∀ (P : CochainComplex (proEtaleRingModules Y R) ℤ)
        (hp : proEtaleFlatRepresentatives Y R P) (p : P ⟶ A), QuasiIso p →
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj F))) ≫ z.hom =
        a.representative.inv.app (⟨P, hp⟩, ⟨F, hf⟩) ≫
          DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
            (proEtaleOrdinaryTensor Y R) (ComplexShape.up ℤ)) := sorry

/-- The unique mixed tensor comparison with the specified resolution normalization.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
def proEtaleMixedTensor (a : ProEtaleTensorModel Y R)
    (A F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hf : proEtaleFlatRepresentatives Y R F) :=
  Classical.choose (proEtaleMixedTensor_existsUnique R a A F hf).exists

/-- The specified inverse: localize the finite-total chain inverse between the canonical
mixed-tensor and K-injective representatives. Its summand formula is the existing
CategoryTheory.tensorAdjunctionTotalInverse_summand, including the signs (-1)^a.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
def proEtalePerfectProjectionInverse
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (K : CochainComplex (proEtaleRingModules X S) ℤ) (hK : K.IsKInjective)
    (rep : E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
    (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    (proEtaleRingDerivedDirectImage f R S c).obj
      (b.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj (DerivedCategory.Q.obj F))) ⟶
    a.tensor.obj ((proEtaleRingDerivedDirectImage f R S c).obj E, DerivedCategory.Q.obj F) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  letI := proEtaleTensorPreadditive Y R
  letI := proEtaleTensorPreadditive X S
  letI := hK
  let L := proEtaleRingModulePullback f R S c
  let V := proEtaleRingModuleDirectImage f R S c
  let am := proEtaleRingModuleAdjunction f R S c
  let mu := proEtaleOrdinaryTensorPullback f R S c
  have hmu := fun {M M' N N' : proEtaleRingModules Y R} (v : M ⟶ M') (z : N ⟶ N') ↦
    proEtaleOrdinaryTensorPullback_naturality f R S c M M' N N' v z
  let jd := proEtaleProjectionUnit_existsUnique f R S c
  let j := Classical.choose jd.exists
  have hj := (Classical.choose_spec jd.exists)
  let s := tensorAdjunctionTotalInverse L V am mu hmu j hj K F hb P.N P.i P.p P.splitting
  let A := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let G := (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let J := CochainComplex.mapBifunctor K G (proEtaleOrdinaryTensor X S)
  let hf := proEtaleStrictPerfect_flat R F P hb
  let hg := (proEtaleCanonicalTensorPullback f R S c a b).1 F hf
  have hJ : J.IsKInjective := tensorAdjunctionTotal_target_isKInjective L j K hK F
    hb P.N P.i P.p P.splitting
  let eA := (proEtaleRingDerivedDirectImage f R S c).mapIso rep ≪≫ V.rightDerivedFunctorObjQIso K
  let eC := a.tensor.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj F))) ≪≫
    proEtaleMixedTensor R a A F hf
  let eF := (proEtaleRingDerivedPullbackFactors f R S c).app F
  letI := hJ
  let eB := (proEtaleRingDerivedDirectImage f R S c).mapIso
    (b.tensor.mapIso (Iso.prod rep eF) ≪≫ proEtaleMixedTensor S b K G hg) ≪≫
      V.rightDerivedFunctorObjQIso J
  exact eB.hom ≫ DerivedCategory.Q.map s ≫ eC.inv

end AlgebraicGeometry.Scheme
