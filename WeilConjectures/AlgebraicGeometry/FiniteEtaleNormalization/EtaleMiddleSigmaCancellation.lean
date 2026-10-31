/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale
import WeilConjectures.CategoryTheory.Etale.EtaleMiddleTensorCancellation

/-! # The sigma cocycle with an etale middle arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

private theorem etale_normalized_middle_cancellation
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {R Q : Scheme.{u}} (r : R ⟶ Q)
    (W AA TT X : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A))
    (M N BB : _root_.DerivedCategory (Sheaf Q.smallEtaleTopology A))
    (η : M ≅ coefficientUnit A Q) (e : BB ≅ N)
    (c : X ≅ (Etale.upperStar A r).leftDerivedFunctor.obj N)
    (s : ((Etale.derivedTensor A R).obj W).obj
      ((Etale.upperStar A r).leftDerivedFunctor.obj M) ⟶ AA)
    (t : ((Etale.derivedTensor A R).obj AA).obj X ⟶ TT)
    (v : ((Etale.derivedTensor A R).obj W).obj
      ((Etale.upperStar A r).leftDerivedFunctor.obj BB) ⟶ TT)
    (k : ((Etale.derivedTensor A Q).obj M).obj N ⟶ BB)
    (hk : k ≫ e.hom = tensorUnitMap A Q M N η)
    (hc : Etale.derivedTensorHom A s (𝟙 X) ≫ t =
      (Etale.derivedTensorAssociator A R W
        ((Etale.upperStar A r).leftDerivedFunctor.obj M) X).hom ≫
      ((Etale.derivedTensor A R).obj W).map
        (Etale.derivedTensorHom A (𝟙 _) c.hom ≫
          (Etale.leftDerivedUpperStarTensorIso A r M N).inv ≫
          (Etale.upperStar A r).leftDerivedFunctor.map k) ≫ v) :
    let L := (Etale.upperStar A r).leftDerivedFunctor
    let U := ((Etale.derivedTensor A R).obj W).mapIso
      (L.mapIso η ≪≫ Etale.leftDerivedUpperStarUnitIso A r) ≪≫
        Etale.derivedTensorRightUnitor A R W
    v = Etale.derivedTensorHom A (𝟙 W) (L.map e.hom) ≫
      Etale.derivedTensorHom A (U.inv ≫ s) c.inv ≫ t := by
  dsimp only
  have h := normalized_middle_cocycle_cancellation
    (Etale.upperStar A r).leftDerivedFunctor
    (Etale.leftDerivedUpperStarTensorIso A r) (Etale.leftDerivedUpperStarUnitIso A r)
    (fun φ K ↦ Etale.leftDerivedUpperStarTensorIso_hom_naturality_left r φ K)
    (fun K ↦ Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom A r K)
    W AA TT X M N BB η e c s t v k
    (by simpa only [tensorUnitMap, Etale.derivedTensor_map_app,
      Etale.derivedTensorLeftUnitor] using hk)
    (by simpa only [Etale.derivedTensorHom, Etale.derivedTensor_map_app,
      Etale.derivedTensor_obj_map, Etale.derivedTensorAssociator,
      Etale.derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
      MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.tensorHom_def, whiskerLeft_id, id_whiskerRight,
      Category.comp_id, Category.id_comp, Category.assoc] using hc)
  simpa only [Etale.derivedTensorHom, Etale.derivedTensor_map_app,
    Etale.derivedTensor_obj_map, Etale.derivedTensorRightUnitor,
    Etale.derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
      MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.tensorHom_def, whiskerLeft_id, id_whiskerRight,
    Category.comp_id, Category.id_comp, Iso.trans_inv, Functor.mapIso_inv,
    whiskerLeftIso_inv, Category.assoc] using h

set_option maxHeartbeats 2000000 in
-- Normalize the concrete dualizing objects and their canonical unit comparisons.
/-- Remove the normalized dualizing complex of the etale middle arrow from
sigma associativity. Source: composition-coherence proof, Step 1
(blueprint: lem-pur-etale-middle-sigma-cancellation).

Proof: precompose the sigma cocycle by the inverse pullback compositor on its
third factor. The finite-etale source normalization identifies sigma for the
middle and last arrows with the unit map followed by inverse E. Apply normalized
middle tensor cancellation, using the naturality and unit law of derived
pullback's tensor comparison. Expanding the resulting right-unit map gives the
specified targetUnit. The same argument includes relative dimension zero and
empty schemes. -/
theorem sigma_etale_middle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {R Q E B : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))] [Q.Over (Spec (.of P.field.k))]
    [E.Over (Spec (.of P.field.k))] [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Q ↘ Spec (.of P.field.k))]
    [QuasiCompact (Q ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (E ↘ Spec (.of P.field.k))]
    [QuasiCompact (E ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    (r : R ⟶ Q) [r.IsOver (Spec (.of P.field.k))]
    [IsSeparated r] [LocallyOfFiniteType r] [QuasiCompact r]
    (d : ℕ) [SmoothOfRelativeDimension d r]
    (G : Q ⟶ E) [G.IsOver (Spec (.of P.field.k))]
    [Etale G] [IsSeparated G] [QuasiCompact G]
    (p : E ⟶ B) [p.IsOver (Spec (.of P.field.k))]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (e : ℕ) [SmoothOfRelativeDimension e p] :
    letI := compactification P r
    letI := compactification P G
    letI := compactification P p
    letI := compactification P (r ≫ G)
    letI := compactification P (G ≫ p)
    letI := compactification P ((r ≫ G) ≫ p)
    letI := compactification P (r ≫ G ≫ p)
    sigma P.Coefficient r (G ≫ p) (comp P r (G ≫ p)) =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 (omega P r))
          ((pull P r).map (sourceEtale P G p).hom) ≫
        Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
          ((targetUnit P.Coefficient r G (rho P G)).inv ≫
            sigma P.Coefficient r G (comp P r G))
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) r G).inv.app
            (omega P p)) ≫
        sigma P.Coefficient (r ≫ G) p (comp P (r ≫ G) p) ≫
        (congr P ((r ≫ G) ≫ p) (r ≫ G ≫ p) (Category.assoc r G p)).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) := by
  let := P.noetherian (R ↘ Spec (.of P.field.k))
  let := P.noetherian (Q ↘ Spec (.of P.field.k))
  let := P.noetherian (E ↘ Spec (.of P.field.k))
  let := P.noetherian (B ↘ Spec (.of P.field.k))
  let := compactification P r
  let := compactification P G
  let := compactification P p
  let := compactification P (r ≫ G)
  let := compactification P (G ≫ p)
  let := compactification P ((r ≫ G) ≫ p)
  let := compactification P (r ≫ G ≫ p)
  let := SmoothOfRelativeDimension.smooth d r
  let := SmoothOfRelativeDimension.smooth e p
  let W := omega P r
  let M := omega P G
  let N := (pull P G).obj (omega P p)
  let BB := omega P (G ≫ p)
  let AA := omega P (r ≫ G)
  let TT := omega P (r ≫ G ≫ p)
  let E' := sourceEtale P G p
  let η := eta P G
  let s := sigma P.Coefficient r G (comp P r G)
  let c := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) r G).app (omega P p)
  let t := sigma P.Coefficient (r ≫ G) p (comp P (r ≫ G) p) ≫
    (congr P ((r ≫ G) ≫ p) (r ≫ G ≫ p) (Category.assoc r G p)).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B)
  let v := sigma P.Coefficient r (G ≫ p) (comp P r (G ≫ p))
  have ht := (finite_etale_dualizing_normalization P G).source_etale p
  change sigma P.Coefficient G p (comp P G p) ≫ E'.hom =
    tensorUnitMap (ModuleCat.{u + 1} P.Coefficient) Q M N η at ht
  have hc := (DualizingLocality.dualizing_cocycle_source_etale P).1 r d G 0 p e
  have hn := etale_normalized_middle_cancellation
    (ModuleCat.{u + 1} P.Coefficient) r
    W AA TT ((pull P (r ≫ G)).obj (omega P p)) M N BB η E' c s t v
    (sigma P.Coefficient G p (comp P G p)) ht
    (by simpa only [s, t, v, W, M, N, AA, TT, BB, c, omega, pull, exceptional,
      coefficientUnit, Etale.dualizingComplex, Iso.app_hom] using hc)
  simpa only [s, t, v, W, M, N, AA, TT, BB, c, E', η, targetUnit, eta,
    omega, pull, exceptional, coefficientUnit, Etale.dualizingComplex,
    Iso.app_inv] using hn

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
