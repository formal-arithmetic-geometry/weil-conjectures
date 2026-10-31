/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedForgetTensorTranspositionData
public import WeilConjectures.AlgebraicGeometry.CoefficientCochainTensorCurry
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Ordinary chain evaluation under exact ringed forgetting

Source: Stacks 08J9, 070I; steps 5--8 of ringed tensor transposition
(blueprint: lem-sf-ringed-forget-chain-uncurry).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r d vd s

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

-- Reuse the small-site transport directly when elaborating coefficient-ring compositions.
attribute [local instance 1000001] RingedDerivedNative.cachedCompose


variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] homComplexFunctor homComplexπ SheafOfModules.monoidalCategory
  WeilConjectures.ZeroClassAux.tensorHomEquiv

private def ordinaryEvaluation (K L : RingedTensorModules.{c, v, r} J R) :
    (SheafOfModules.monoidalCategory R).tensorObj
      (SheafOfModules.homObj (R := R) K L) K ⟶ L :=
  (β_ (SheafOfModules.homObj (R := R) K L) K).hom ≫
    (WeilConjectures.ZeroClassAux.tensorHomEquiv.{r, c, v} R K
      (SheafOfModules.homObj (R := R) K L) L).symm (𝟙 _)

set_option maxHeartbeats 800000 in
-- Normalize the sheafified tensor generator in the two ordinary adjunction formulas.
private theorem ordinaryEvaluation_pure (K L : RingedTensorModules.{c, v, r} J R) :
    IsSheafEvaluation.{c, v, r} J R K L (ordinaryEvaluation.{c, v, r} J R K L) := by
  intro V φ x
  change ((WeilConjectures.ZeroClassAux.tensorHomEquiv.{r, c, v} R K
      (SheafOfModules.homObj (R := R) K L) L).symm (𝟙 _)).val.app V
    ((β_ (SheafOfModules.homObj (R := R) K L) K).hom.val.app V
      (sheafTensorGenerator.{c, v, r} J R (SheafOfModules.homObj (R := R) K L) K V φ x)) = _
  have hb : (β_ (SheafOfModules.homObj (R := R) K L) K).hom.val.app V
      (sheafTensorGenerator.{c, v, r} J R (SheafOfModules.homObj (R := R) K L) K V φ x) =
      sheafTensorGenerator.{c, v, r} J R K (SheafOfModules.homObj (R := R) K L) V x φ :=
    RingedDerivedNative.pure_braiding.{c, v, r} J R _ _ V φ x
  rw [hb]
  exact RingedDerivedNative.uncurry_pure.{c, v, r} J R K
    (SheafOfModules.homObj (R := R) K L) L (𝟙 _) V φ x

private theorem tensor_ext (K L N : RingedTensorModules.{c, v, r} J R)
    (f g : (SheafOfModules.monoidalCategory R).tensorObj K L ⟶ N)
    (h : ∀ (V : Cᵒᵖ) (x : K.val.obj V) (y : L.val.obj V),
      f.val.app V (sheafTensorGenerator.{c, v, r} J R K L V x y) =
        g.val.app V (sheafTensorGenerator.{c, v, r} J R K L V x y)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) K L).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).homEquiv
        (K.val ⊗ L.val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h V

private theorem curry_summand
    (P K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (φ : P ⟶ homComplex (R := R) K I)
    (ψ : (coefficientTotalTensor.{r, c, v} J R).obj (P, K) ⟶ I)
    (hψ : IsCoefficientTensorCurry.{r, c, v} J R P K I ψ φ)
    (p q : ℤ) :
    tensorSummand.{c, v, r} J R P K p q (p + q) rfl ≫ ψ.f (p + q) =
      (@MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)).map
        (X := (P.X p, K.X q))
        (Y := (SheafOfModules.homObj (R := R) (K.X q) (I.X (p + q)), K.X q))
        (φ.f p ≫ homComplexπ (R := R) K I p q (p + q) (add_comm q p), 𝟙 _) ≫
          ordinaryEvaluation.{c, v, r} J R (K.X q) (I.X (p + q)) := by
  apply tensor_ext.{c, v, r} J R
  intro V x y
  change (ψ.f (p + q)).val.app V
    (coefficientTensorGenerator.{r, c, v} J R P K p q (p + q) rfl V x y) = _
  rw [hψ p q V x y]
  change _ = (ordinaryEvaluation.{c, v, r} J R (K.X q) (I.X (p + q))).val.app V
    (((φ.f p ≫ homComplexπ (R := R) K I p q (p + q) (add_comm q p)) ⊗ₘ
      𝟙 (K.X q)).val.app V (sheafTensorGenerator.{c, v, r} J R (P.X p) (K.X q) V x y))
  have hm := CochainPullback.moduleTmul_map (R := R)
    (φ.f p ≫ homComplexπ (R := R) K I p q (p + q) (add_comm q p))
    (𝟙 (K.X q)) V x y
  change ((φ.f p ≫ homComplexπ (R := R) K I p q (p + q) (add_comm q p)) ⊗ₘ
      𝟙 (K.X q)).val.app V (sheafTensorGenerator.{c, v, r} J R (P.X p) (K.X q) V x y) =
    sheafTensorGenerator.{c, v, r} J R
      (SheafOfModules.homObj (R := R) (K.X q) (I.X (p + q))) (K.X q) V
      ((homComplexπ (R := R) K I p q (p + q) (add_comm q p)).val.app V
        ((φ.f p).val.app V x)) y at hm
  rw [hm]
  exact (ordinaryEvaluation_pure.{c, v, r} J R (K.X q) (I.X (p + q)) V
    ((homComplexπ (R := R) K I p q (p + q) (add_comm q p)).val.app V
      ((φ.f p).val.app V x)) y).symm

attribute [local irreducible] ordinaryEvaluation coefficientTensorGenerator

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive]

/-- Forgetting the ordinary uncurried chain map agrees with uncurrying after the
specified tensor and Hom comparisons. This concerns actual cochain maps, before any
K-flat or K-injective replacement or localization.

Source: Stacks Project, Tags 08J9 and 070I; step 2 of
lem-sf-ringed-forget-normalized-uncurry
(blueprint: lem-sf-ringed-forget-chain-uncurry).

Proof: in degree n, precompose with every tensor summand indexed by p+q=n.
The two curry hypotheses express the maps on that summand as evaluation of
phi in the q-th Hom projection. The tensor summand equation replaces the
mapped source inclusion by the specified underived tensor comparison. The
Hom projection equation replaces the target Hom projection by U of the
source projection followed by the specified sheaf-Hom comparison. Naturality
of the underived tensor comparison moves phi across it. The evaluation field
of u then identifies the two resulting maps. Canonical sheaf evaluation has
its stated pure tensor formula by the sheaf tensor-Hom adjunction. Finally
the tensor summand inclusions jointly detect maps out of the total complex.
One may test after the inverse tensor comparison, so no coproduct
preservation by U is needed. This works for all unbounded complexes and uses
no flatness, injectivity, boundedness or invertibility of evaluation. -/
theorem ringed_forget_chain_uncurry
    (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
    (P K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (t : (U.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, K)) ≅
      (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj P,
          (U.mapHomologicalComplex (.up ℤ)).obj K))
    (ht : ∀ (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P K p q n hpq) ≫ t.hom.f n =
        u.tensor.hom.app (P.X p, K.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj K) p q n hpq)
    (h : (U.mapHomologicalComplex (.up ℤ)).obj (homComplex (R := R) K I) ≅
      homComplex (R := R') ((U.mapHomologicalComplex (.up ℤ)).obj K)
        ((U.mapHomologicalComplex (.up ℤ)).obj I))
    (hh : ∀ (n p q : ℤ) (hpq : p + n = q),
      h.hom.f n ≫ homComplexπ (R := R') ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
        U.map (homComplexπ (R := R) K I n p q hpq) ≫
          u.hom.hom.app (op (K.X p), I.X q))
    (φ : P ⟶ homComplex (R := R) K I)
    (ψ : (coefficientTotalTensor.{r, c, v} J R).obj (P, K) ⟶ I)
    (ψ' : (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj P,
          (U.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (U.mapHomologicalComplex (.up ℤ)).obj I)
    (hψ : IsCoefficientTensorCurry.{r, c, v} J R P K I ψ φ)
    (hψ' : IsCoefficientTensorCurry.{s, d, vd} J' R'
      ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj K)
      ((U.mapHomologicalComplex (.up ℤ)).obj I) ψ'
      ((U.mapHomologicalComplex (.up ℤ)).map φ ≫ h.hom)) :
    (U.mapHomologicalComplex (.up ℤ)).map ψ = t.hom ≫ ψ' := by
  apply (cancel_epi t.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  change tensorSummand.{d, vd, s} J' R' _ _ p q (p + q) rfl ≫
    (t.inv.f (p + q) ≫ U.map (ψ.f (p + q))) =
    tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj K) p q (p + q) rfl ≫ ψ'.f (p + q)
  have hi : tensorSummand.{d, vd, s} J' R' _ _ p q (p + q) rfl ≫ t.inv.f (p + q) =
      u.tensor.inv.app (P.X p, K.X q) ≫
        U.map (tensorSummand.{c, v, r} J R P K p q (p + q) rfl) := by
    apply (cancel_epi (u.tensor.hom.app (P.X p, K.X q))).1
    rw [← Category.assoc, ← ht p q (p + q) rfl]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, Iso.hom_inv_id_app_assoc]
    exact Category.comp_id _
  rw [← Category.assoc, hi, Category.assoc, ← U.map_comp,
    curry_summand.{c, v, r} J R P K I φ ψ hψ p q, U.map_comp]
  rw [curry_summand.{d, vd, s} J' R' _ _ _ _ ψ' hψ' p q]
  let TB := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)
  let TA := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R')
  let g := φ.f p ≫ homComplexπ (R := R) K I p q (p + q) (add_comm q p)
  have he := u.evaluation (K.X q) (I.X (p + q))
    (ordinaryEvaluation.{c, v, r} J R (K.X q) (I.X (p + q)))
    (ordinaryEvaluation.{d, vd, s} J' R' (U.obj (K.X q)) (U.obj (I.X (p + q))))
    (ordinaryEvaluation_pure.{c, v, r} J R _ _) (ordinaryEvaluation_pure.{d, vd, s} J' R' _ _)
  have hn := u.tensor.inv.naturality
    (X := (P.X p, K.X q))
    (Y := (SheafOfModules.homObj (R := R) (K.X q) (I.X (p + q)), K.X q)) (g, 𝟙 _)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Functor.map_id] at hn
  have hg : ((U.mapHomologicalComplex (.up ℤ)).map φ ≫ h.hom).f p ≫
      homComplexπ (R := R') ((U.mapHomologicalComplex (.up ℤ)).obj K)
        ((U.mapHomologicalComplex (.up ℤ)).obj I) p q (p + q) (add_comm q p) =
      U.map g ≫ u.hom.hom.app (op (K.X q), I.X (p + q)) := by
    simp only [HomologicalComplex.comp_f, Category.assoc,
      Functor.mapHomologicalComplex_map_f]
    rw [hh, ← Functor.map_comp_assoc]
  rw [hg]
  change u.tensor.inv.app (P.X p, K.X q) ≫
      U.map (TB.map (X := (P.X p, K.X q))
        (Y := (SheafOfModules.homObj (R := R) (K.X q) (I.X (p + q)), K.X q))
        (g, 𝟙 _)) ≫
      U.map (ordinaryEvaluation.{c, v, r} J R (K.X q) (I.X (p + q))) =
    TA.map (X := (U.obj (P.X p), U.obj (K.X q)))
      (Y := (SheafOfModules.homObj (R := R') (U.obj (K.X q)) (U.obj (I.X (p + q))),
        U.obj (K.X q)))
      (U.map g ≫ u.hom.hom.app (op (K.X q), I.X (p + q)), 𝟙 _) ≫
      ordinaryEvaluation.{d, vd, s} J' R' (U.obj (K.X q)) (U.obj (I.X (p + q)))
  rw [← Category.assoc, ← hn, Category.assoc]
  have he' := congrArg (u.tensor.inv.app
    (SheafOfModules.homObj (R := R) (K.X q) (I.X (p + q)), K.X q) ≫ ·) he
  simp only [Iso.inv_hom_id_app_assoc] at he'
  rw [← he']
  simp only [← Category.assoc, TA, ← Functor.map_comp, prod_comp, Category.comp_id]

end CategoryTheory.RingedForgetTensorTransposition
