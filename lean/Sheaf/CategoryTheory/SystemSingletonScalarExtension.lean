/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.CategoryTheory.SystemEvaluationTopos
public import Sheaf.CategoryTheory.SystemSingleDerivedExtension
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SystemSingleDerivedEvaluation
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.SystemScalarCoherence

public import Sheaf.CategoryTheory.SystemSingletonScalarBasic
import Sheaf.CategoryTheory.SystemSingletonKFlat
import Sheaf.CategoryTheory.SystemSingletonScalarRepresentative
import Sheaf.CategoryTheory.SystemSingletonScalarLower
/-! # Singleton extension and arbitrary coefficient change

Source: Stacks 0D6D, lemma-derived-pullback-composition, and Zheng, Construction 4.1.
The singleton functor is an extension left adjoint, not a geometric inverse image.
(blueprint: lem-pur-system-singleton-scalar-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

private def singletonIdentityInverseImage (R : Sheaf J CommRingCat.{w}) :
    AlgebraicInverseImage (𝟭 (Sheaf J (Type w))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private theorem singletonScalarModel_kFlat {R R' : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ R'} (F : SystemScalarModel φ)
    (P : CochainComplex (ringedSiteModules.{w}
      (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((F.model.E.mapHomologicalComplex (.up ℤ)).obj P) ∧
    (∀ i : ℤ, IsFlatOnSite (R := R') (F.model.E.obj (P.X i))) := by
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (singletonIdentityInverseImage R) φ F.model.E F.model.obj_eq F.model.map_eq P hP hf

private theorem singletonSequenceComparison_isIso
    (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (P : CochainComplex (systemLevel R n) ℤ) (hP : systemLevelKFlat R n P) :
    IsIso (singletonSequenceComparison S T R n P) := by
  have := (systemSingleDerivedExtension R n S T).computes P hP
  unfold singletonSequenceComparison
  have hfac : IsIso
      ((strictSystemSequenceEquivalence R).functor.mapDerivedCategoryFactors.hom.app
      (((systemSingleFunctor S T R n).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ((strictSystemSequenceEquivalence R).functor.mapDerivedCategoryFactors.app
      (((systemSingleFunctor S T R n).mapHomologicalComplex (.up ℤ)).obj P)).isIso_hom
  exact IsIso.comp_isIso'
    ((strictSystemSequenceEquivalence R).functor.mapDerivedCategory.map_isIso
      ((systemSingleDerivedExtension R n S T).comparison.app P)) hfac

private theorem singletonScalarOrdinary_tmul (n : ℕ) (P : systemLevel B n)
    (j : ℕ) (h : j ≤ n) (U : Cᵒᵖ) (b : (B.obj (op j)).obj.obj U)
    (c : (D.obj (op j)).obj.obj U) (x : P.val.obj U) :
      ((singletonScalarOrdinaryIso S T a A n).hom.app P).val.app (op (j, U.unop))
        (systemModelTmul A.model ((singletonSequenceOrdinary S T B n).obj P)
          (op (j, U.unop)) c
          ((systemSingleLevelBelow S B n P h).inv.val.app U
            (systemModelTmul (S (B.map (homOfLE h).op)).model P U b x))) =
      (systemSingleLevelBelow S D n ((S (a.app (op n))).model.E.obj P) h).inv.val.app U
        (systemModelTmul (S (D.map (homOfLE h).op)).model
          ((S (a.app (op n))).model.E.obj P) U ((a.app (op j)).hom.app U b * c)
          (systemModelTmul (S (a.app (op n))).model P U 1 x)) := by
  let N := (singletonSequenceOrdinary S T D n).obj ((S (a.app (op n))).model.E.obj P)
  let : Module ((D.obj (op j)).obj.obj U) (N.val.obj (op (j, U.unop))) :=
    inferInstanceAs (Module
      ((derivedChangeRingIndependentCoefficients (coefficientSequenceTopology J)
        (systemSequenceRing D)).obj.obj (op (j, U.unop))) (N.val.obj (op (j, U.unop))))
  let f := (singletonScalarOrdinaryIso S T a A n).hom.app P
  let g := A.ordinaryAdj.homEquiv _ N f
  let g' := (strictSystemSequenceEquivalence B).toAdjunction.homEquiv _ _ g
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((singletonSequenceOrdinaryAdjunction S T B n).comp A.ordinaryAdj).ofNatIsoRight
      (singletonRestrictionEvaluation a n))
    ((S (a.app (op n))).ordinaryAdj.comp
      (singletonSequenceOrdinaryAdjunction S T D n)) P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hu
  have hx := congrArg (fun k ↦ k.val.app U x) hu
  change (g'.app n).val.app U ((systemSingleUnit S T B n P).val.app U x) =
    ((singletonSequenceOrdinaryAdjunction S T D n).unit.app
      ((S (a.app (op n))).model.E.obj P)).val.app U
        (((S (a.app (op n))).ordinaryAdj.unit.app P).val.app U x) at hx
  have ht := systemSingleTranspose S T B n h P _ g'
  have hb := systemScalarModel_transpose_tmul (S (B.map (homOfLE h).op)) P
    (((strictSystemSequenceEquivalence B).inverse.obj
      ((singletonSequenceRestriction a).obj N)).level j)
    ((systemSingleBelow S T B n h).inv.app P ≫ g'.app j) U b x
  rw [ht] at hb
  change (g'.app j).val.app U
    ((systemSingleLevelBelow S B n P h).inv.val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model P U b x)) =
    (show (derivedChangeRingIndependentCoefficients J (B.obj (op j))).obj.obj U from b) •
      (show (((strictSystemSequenceEquivalence B).inverse.obj
      ((singletonSequenceRestriction a).obj N)).level j).val.obj U from
      (((strictSystemSequenceEquivalence B).inverse.obj
        ((singletonSequenceRestriction a).obj N)).transition h).val.app U
          ((g'.app n).val.app U ((systemSingleUnit S T B n P).val.app U x))) at hb
  rw [hx] at hb
  have hf := systemScalarModel_transpose_tmul A
    ((singletonSequenceOrdinary S T B n).obj P) N f (op (j, U.unop)) c
    ((systemSingleLevelBelow S B n P h).inv.val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model P U b x))
  change f.val.app (op (j, U.unop)) _ = _
  refine hf.trans ?_
  change c • (show N.val.obj (op (j, U.unop)) from (g'.app j).val.app U
    ((systemSingleLevelBelow S B n P h).inv.val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model P U b x))) = _
  erw [hb]
  have hstep (y : ((S (a.app (op n))).model.E.obj P).val.obj U) :
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (((singletonSequenceOrdinaryAdjunction S T D n).unit.app
          ((S (a.app (op n))).model.E.obj P)).val.app U y) =
      (systemSingleLevelBelow S D n ((S (a.app (op n))).model.E.obj P) h).inv.val.app U
        (systemModelTmul (S (D.map (homOfLE h).op)).model
          ((S (a.app (op n))).model.E.obj P) U 1 y) := by
    change (systemSingleLevel S D n ((S (a.app (op n))).model.E.obj P) j).val.map (𝟙 U)
      ((systemSingleTransition S T D n ((S (a.app (op n))).model.E.obj P) h).val.app U
        ((systemSingleUnit S T D n ((S (a.app (op n))).model.E.obj P)).val.app U y)) = _
    rw [PresheafOfModules.map_id]
    change (systemSingleTransition S T D n ((S (a.app (op n))).model.E.obj P) h).val.app U
      ((systemSingleUnit S T D n ((S (a.app (op n))).model.E.obj P)).val.app U y) = _
    rw [systemSingleUnit_tmul, systemSingleTransition_tmul, map_one]
  change c • (((a.app (op j)).hom.app U b) •
    (show N.val.obj (op (j, U.unop)) from
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
      (((singletonSequenceOrdinaryAdjunction S T D n).unit.app
        ((S (a.app (op n))).model.E.obj P)).val.app U
          (((S (a.app (op n))).ordinaryAdj.unit.app P).val.app U x)))) = _
  erw [hstep, (S (a.app (op n))).unit_normalized]
  simp only [systemModelTmul, one_smul]
  erw [((systemSingleLevelBelow S D n
    ((S (a.app (op n))).model.E.obj P) h).inv.val.app U).hom.map_smul]
  change c • (((a.app (op j)).hom.app U b) •
    (show N.val.obj (op (j, U.unop)) from _)) =
    (((a.app (op j)).hom.app U b) * c) •
      (show N.val.obj (op (j, U.unop)) from _)
  exact (mul_smul c ((a.app (op j)).hom.app U b) _).symm.trans
    (congrArg (fun d : (D.obj (op j)).obj.obj U ↦ d •
      (show N.val.obj (op (j, U.unop)) from _)) (mul_comm _ _))

/-- Scalar extension commutes with derived singleton extension, including its specified
Hom transposes, actual system-complex representatives, and lower-singleton maps.
Source: Stacks 0D6D (lemma-derived-pullback-composition), with the agent singleton
argument over Zheng Construction 4.1
(blueprint: lem-pur-system-singleton-scalar-extension).

Proof: (1) Vertical coverings make sheafification, scalar restriction and evaluation
levelwise, giving the identity right-adjoint square. (2) The ordinary comparison sends
(b tensor q) tensor c to a_j(b)c tensor (q tensor 1); its inverse moves the second
C_n scalar into C_j. Both maps respect balancing by naturality of a.
(3) Naturality of a also proves compatibility with every system transition; above n
both sides vanish, and at n tensor multiplication gives the normalization.
(4) Extension of flat modules along any ring map is flat, and tensor exactness is
detected levelwise, so singleton extension has flat terms on its sequence site.
(5) For an acyclic system complex K, the jth tensor with the singleton is
Res_{B_n to B_j}(K_j) tensor_{B_n} Q below n, and zero above n. Exact scalar
restriction and K-flatness of Q prove whole-sequence-site K-flatness.
(6) Ringed-topos K-flat pullback along coefficient change proves the same properties
for both scalar-extended representatives; the universal comparisons are isomorphisms.
(7) Compose the two normalized adjunctions on each side. Their ordinary units both
insert two unit tensors, and the right comparisons are the identity square. The
normalized adjunction-composition theorem identifies their conjugate with localization
of the ordinary comparison. (8) Its Hom equation identifies the actual transposes;
taking identity maps gives the corresponding unit and counit equations.
(9) For m at least n, both lower-singleton routes on local generators give
 a_j(b rho_jn(t))c tensor (q tensor 1) =
 a_j(b)c rho_jn(a_n(t)) tensor (q tensor 1).
These strict maps agree before localization and hence after the canonical scalar
associators. No flat coefficient maps or bounded complexes are used. -/
theorem singletonScalarExtension :
    (∀ (n : ℕ) (P : DerivedCategory (systemLevel B n))
      (M : DerivedCategory (systemSequenceModules D))
      (f : ((S (a.app (op n))).model.T ⋙ singletonSequenceDerived S T D n).obj P ⟶ M),
      ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).homEquiv P M
          ((singletonScalarDerivedIso S T a A n).hom.app P ≫ f) ≫
        (singletonDerivedRestrictionEvaluation a n).hom.app M =
      ((S (a.app (op n))).adjunction.comp
        (singletonSequenceDerivedAdjunction S T D n)).homEquiv P M f) ∧
    (∀ (n : ℕ) (P : CochainComplex (systemLevel B n) ℤ), systemLevelKFlat B n P →
      CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
        (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) ∧
      (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B)
        (((singletonSequenceOrdinary S T B n).obj (P.X i)))) ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing D)
        ((A.model.E.mapHomologicalComplex (.up ℤ)).obj
          (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing D)
        (A.model.E.obj ((singletonSequenceOrdinary S T B n).obj (P.X i)))) ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing D)
        (((singletonSequenceOrdinary S T D n).mapHomologicalComplex (.up ℤ)).obj
          ((((S (a.app (op n))).model.E).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing D)
        ((singletonSequenceOrdinary S T D n).obj
          ((S (a.app (op n))).model.E.obj (P.X i)))) ∧
      IsIso (singletonScalarSourceComparison S T a A n P) ∧
      IsIso (singletonScalarTargetComparison S T a n P) ∧
      (singletonScalarDerivedIso S T a A n).hom.app (DerivedCategory.Q.obj P) ≫
          singletonScalarTargetComparison S T a n P =
        singletonScalarSourceComparison S T a A n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
            (.up ℤ)).hom.app P)) ∧
    (∀ (n : ℕ) (P : systemLevel B n) (j : ℕ) (h : j ≤ n) (U : Cᵒᵖ)
      (b : (B.obj (op j)).obj.obj U) (c : (D.obj (op j)).obj.obj U) (x : P.val.obj U),
      ((singletonScalarOrdinaryIso S T a A n).hom.app P).val.app (op (j, U.unop))
        (systemModelTmul A.model ((singletonSequenceOrdinary S T B n).obj P)
          (op (j, U.unop)) c
          ((systemSingleLevelBelow S B n P h).inv.val.app U
            (systemModelTmul (S (B.map (homOfLE h).op)).model P U b x))) =
      (systemSingleLevelBelow S D n ((S (a.app (op n))).model.E.obj P) h).inv.val.app U
        (systemModelTmul (S (D.map (homOfLE h).op)).model
          ((S (a.app (op n))).model.E.obj P) U ((a.app (op j)).hom.app U b * c)
          (systemModelTmul (S (a.app (op n))).model P U 1 x))) ∧
    (∀ (n : ℕ) (P : systemLevel B n) (j : ℕ), n < j →
      IsZero ((systemSequenceEvaluation D j).obj
        (A.model.E.obj ((singletonSequenceOrdinary S T B n).obj P))) ∧
      IsZero ((systemSequenceEvaluation D j).obj
        ((singletonSequenceOrdinary S T D n).obj ((S (a.app (op n))).model.E.obj P))) ∧
      (systemSequenceEvaluation D j).map
        ((singletonScalarOrdinaryIso S T a A n).hom.app P) = 0) ∧
    (∀ (n m : ℕ) (h : n ≤ m) (P : DerivedCategory (systemLevel B m)),
      A.model.T.map (singletonLowerMap S T B h P) ≫
          (singletonScalarDerivedIso S T a A m).hom.app P =
        (singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P) ≫
          (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
          singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n P M f
    simpa only [singletonScalarDerivedIso, Adjunction.homEquiv_ofNatIsoRight_apply] using
      leftAdjointUniq_homEquiv_comp
      (((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).ofNatIsoRight
        (singletonDerivedRestrictionEvaluation a n))
      ((S (a.app (op n))).adjunction.comp
        (singletonSequenceDerivedAdjunction S T D n)) P M f
  · intro n P hP
    have hB := singletonSequenceOrdinary_kFlat S T B n P hP
    have hseq := singletonScalarModel_kFlat A
      (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P)
      hB.1 hB.2
    have hn := singletonScalarModel_kFlat (S (a.app (op n))) P hP.1 hP.2
    have hD := singletonSequenceOrdinary_kFlat S T D n
      ((((S (a.app (op n))).model.E).mapHomologicalComplex (.up ℤ)).obj P) hn
    refine ⟨hB.1, hB.2, hseq.1, hseq.2, hD.1, hD.2, ?_, ?_,
      singletonScalarDerivedIso_rep S T a A n P⟩
    · have := singletonSequenceComparison_isIso S T B n P hP
      have := A.model.computes
        (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) hB.1
      dsimp only [singletonScalarSourceComparison]
      infer_instance
    · have := (S (a.app (op n))).model.computes P hP.1
      have := singletonSequenceComparison_isIso S T D n
        ((((S (a.app (op n))).model.E).mapHomologicalComplex (.up ℤ)).obj P) hn
      dsimp only [singletonScalarTargetComparison]
      infer_instance
  · exact singletonScalarOrdinary_tmul S T a A
  · intro n P j hj
    have hz := systemSingleLevelAbove S D n
      ((S (a.app (op n))).model.E.obj P) hj
    change IsZero ((systemSequenceEvaluation D j).obj
      (A.model.E.obj ((singletonSequenceOrdinary S T B n).obj P))) ∧ _
    have ht : IsZero ((systemSequenceEvaluation D j).obj
        ((singletonSequenceOrdinary S T D n).obj
          ((S (a.app (op n))).model.E.obj P))) :=
      hz.of_iso ((systemEvaluation D j).mapIso
        ((strictSystemSequenceEquivalence D).unitIso.symm.app
          ((systemSingleFunctor S T D n).obj ((S (a.app (op n))).model.E.obj P))))
    have hs := ht.of_iso ((systemSequenceEvaluation D j).mapIso
      ((singletonScalarOrdinaryIso S T a A n).app P))
    exact ⟨hs, ht, hs.eq_of_src _ _⟩
  · exact singletonScalarDerivedIso_lower S T a A

end SheafOfModules
