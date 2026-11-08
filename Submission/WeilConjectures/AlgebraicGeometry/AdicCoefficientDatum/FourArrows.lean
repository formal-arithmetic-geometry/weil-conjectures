/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import Submission.WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Submission.WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import Submission.WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Abelian.RightDerived
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The four finite-level arrows

Source: blueprint, proper base change, four finite-level arrows, order 1343;
Stacks Project Tags 07A7, 09C9, 0B56 and 0944 (blueprint: def-weil-pbc-four-arrows).

The horizontal arrows and the finite exchange are isomorphisms. The reduced ambient
exchange is a morphism; neither its invertibility nor commutativity of this square is
part of this definition. All scalar extensions and pullbacks are uncompleted.

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits

private theorem invertSquare {C : Type u₁} [Category.{v₁} C]
    {U V W X Y Z : C} (u : U ⟶ V) (b : V ≅ W) (e : W ≅ X)
    (t : U ≅ Y) (a : Y ≅ Z) (v : Z ⟶ X)
    (h : u ≫ b.hom ≫ e.hom = t.hom ≫ a.hom ≫ v) :
    v ≫ e.inv ≫ b.inv = a.inv ≫ t.inv ≫ u := by
  have hh := congrArg (fun k ↦ a.inv ≫ t.inv ≫ k ≫ e.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using hh.symm

private theorem invertMappedSquare {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] (P : C ⥤ E) (Q : D ⥤ E)
    {B₁ B₂ : C} {T₁ T₂ : D} {U V : E}
    (b : B₁ ≅ B₂) (t : T₁ ≅ T₂) (e : P.obj B₁ ≅ V)
    (a : U ≅ Q.obj T₁) (u : Q.obj T₂ ⟶ P.obj B₂) (v : U ⟶ V)
    (h : u ≫ P.map b.inv ≫ e.hom = Q.map t.inv ≫ a.inv ≫ v) :
    v ≫ e.inv ≫ P.map b.hom = a.hom ≫ Q.map t.hom ≫ u := by
  exact invertSquare u (P.mapIso b.symm) e (Q.mapIso t.symm) a.symm v h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem swap
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {U : C ⥤ A} {S' : B ⥤ D} {U' : D ⥤ B}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (sc : S ⊣ U) (sc' : S' ⊣ U')
    (b : L' ⋙ U' ≅ U ⋙ L)
    (a : L ⋙ S' ≅ S ⋙ L')
    (ha : a.hom = (mateEquiv sc sc').symm b.inv)
    (d : R' ⋙ U ≅ U' ⋙ R)
    (hd : ∀ (M : C) (N : D) (t : L'.obj M ⟶ N),
      adj.homEquiv _ _ (b.inv.app M ≫ U'.map t) =
        U.map (adj'.homEquiv M N t) ≫ d.hom.app N)
    (H : B) :
    adj'.homEquiv _ _ (a.inv.app (R.obj H) ≫ S'.map (adj.counit.app H)) =
      (sc.homEquiv _ _).symm
        (R.map (sc'.unit.app H) ≫ d.inv.app (S'.obj H)) := by
  apply (sc.homEquiv _ _).injective
  dsimp only [Functor.id_obj] at *
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono (d.hom.app (S'.obj H))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj]
  rw [Category.comp_id]
  rw [Adjunction.homEquiv_unit, Category.assoc, ← hd]
  erw [← adj.homEquiv_naturality_left]
  have hu := unit_mateEquiv_symm sc sc' (TwoSquare.mk _ _ _ _ b.inv) (R.obj H)
  rw [← ha] at hu
  change L.map (sc.unit.app (R.obj H)) ≫ b.inv.app (S.obj (R.obj H)) =
    sc'.unit.app (L.obj (R.obj H)) ≫ U'.map (a.hom.app (R.obj H)) at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc, ← U'.map_comp, Iso.hom_inv_id_app_assoc]
  have hn := sc'.unit.naturality (adj.counit.app H)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← hn]
  rw [adj.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, adj.right_triangle_components, Category.id_comp]

namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
private theorem ordinaryComparison (n : ℕ) :
    completedRestrictionDirectImageIso f d n =
      (proEtaleRingRestrictionDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).symm := by
  apply (completedRestrictionDirectImageIso_exists f d n).unique
  · exact (completedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  · intro M U x
    let e := proEtaleRingRestrictionDirectImage f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)
    have h := congrArg (fun a ↦ a.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at h
    have he := (proEtaleRingRestrictionDirectImage_existsUnique f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)).choose_spec.1
    exact (he M U _).symm.trans h

private theorem completedUnit_eq
    (C : CochainComplex (proEtaleRingModules X (d.completedRing X)) ℤ) :
    completedDirectImageComplexUnit f d C =
      proEtaleRingDirectImageDerivedUnit f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f) C := by
  have h : (((completedModuleDirectImage f d).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) =
      𝟙 _ := rfl
  simp only [completedDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit,
    h]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem finiteUnit_eq (n : ℕ)
    (C : CochainComplex (proEtaleRingModules X (d.finiteRing X n)) ℤ) :
    completedFiniteDirectImageComplexUnit f d n C =
      proEtaleRingDirectImageDerivedUnit f (d.finiteRing Y n) (d.finiteRing X n)
        (d.finiteRingIso f n) C := by
  have h : (((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors
      (.up ℤ)).inv.app C) = 𝟙 _ := rfl
  simp only [completedFiniteDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit,
    h]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Comparing the two normalized derived presentations requires unfolding their factor isos.
private theorem derivedComparison (n : ℕ) :
    completedDerivedRestrictionDirectImageIso f d n =
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).symm := by
  let D := proEtaleRingRestrictionDerivedDirectImage f
    (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
    (d.projection Y n) (d.projection X n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let E := completedDerivedRestrictionDirectImageIso f d n
  have he := (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  have hD : D = E.symm := by
    apply (proEtaleRingRestrictionDerivedDirectImage_existsUnique f
      (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
      (d.projection Y n) (d.projection X n) (d.integralRingIso f)
      (d.finiteRingIso f n) (d.projection_comm f n)).unique
    · exact (proEtaleRingRestrictionDerivedDirectImage_existsUnique f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).choose_spec.1
    · intro C
      have hC := he C
      change completedDirectImageComplexUnit f d _ ≫ _ ≫ E.hom.app _ = _ at hC
      rw [ordinaryComparison d f n, completedUnit_eq d f, finiteUnit_eq d f n] at hC
      let b := (pbcRestrict (pbcAdicProjection X d n)).mapDerivedCategoryFactors.app C
      let a := (pbcRestrict (pbcAdicProjection Y d n)).mapDerivedCategoryFactors.app
        (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C)
      let o := proEtaleRingRestrictionDirectImage f
        (d.completedRing Y) (d.finiteRing Y n) (d.completedRing X) (d.finiteRing X n)
        (d.projection Y n) (d.projection X n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)
      let t := NatIso.mapHomologicalComplex o (.up ℤ)
      let P := d.push f
      let u := proEtaleRingDirectImageDerivedUnit f (d.completedRing Y)
        (d.completedRing X) (d.integralRingIso f)
        (((pbcRestrict (pbcAdicProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C)
      let v := (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
        (proEtaleRingDirectImageDerivedUnit f (d.finiteRing Y n) (d.finiteRing X n)
          (d.finiteRingIso f n) C)
      change u ≫ P.map b.inv ≫ E.hom.app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map (t.inv.app C) ≫ a.inv ≫ v at hC
      change v ≫ E.inv.app (DerivedCategory.Q.obj C) ≫ P.map b.hom =
        a.hom ≫ DerivedCategory.Q.map (t.hom.app C) ≫ u
      exact invertMappedSquare P DerivedCategory.Q b (t.app C)
        (E.app (DerivedCategory.Q.obj C)) a u v hC
  exact (congrArg Iso.symm hD).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarProjection_eq (H : DerivedCategory (proEtaleRingModules U RU)) :
    (proEtaleRingDerivedAdjunction f SV SU cS).homEquiv _ _
      ((proEtaleReductionPullbackIso f RV SV RU SU aV aU cR cS comm).hom.app
        ((proEtaleRingDerivedDirectImage f RV RU cR).obj H) ≫
        (proEtaleRingDerivedExtension aU).map
          ((proEtaleRingDerivedAdjunction f RV RU cR).counit.app H)) =
      ((proEtaleRingDerivedExtensionAdjunction aV).homEquiv _ _).symm
        ((proEtaleRingDerivedDirectImage f RV RU cR).map
          ((proEtaleRingDerivedExtensionAdjunction aU).unit.app H) ≫
          (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm).inv.app
            ((proEtaleRingDerivedExtension aU).obj H)) := by
  exact swap (proEtaleRingDerivedAdjunction f RV RU cR)
    (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedExtensionAdjunction aV)
    (proEtaleRingDerivedExtensionAdjunction aU)
    (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm)
    (proEtaleReductionPullbackIso f RV SV RU SU aV aU cR cS comm).symm rfl
    (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm)
    (proEtaleRingSheafChangeAdjunction f RV SV RU SU aV aU cR cS comm).2.2 H
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The finite-coefficient projection is the adjunct of chi followed by scalar extension
of the ambient counit. Its target retains the quotient-coefficient action.
Source: blueprint four arrows; Stacks Tags 0B56 and 0944
(blueprint: def-weil-pbc-four-arrows). -/
noncomputable def AdicCoefficientDatum.finiteProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) :
    (d.reduction Y n).obj ((d.push f).obj H) ⟶
      (d.finitePush f n).obj ((d.reduction X n).obj H) :=
  (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n)
    (d.finiteRingIso f n)).homEquiv _ _
      ((d.chi f n).hom.app ((d.push f).obj H) ≫
        (d.reduction X n).map
          ((proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f)).counit.app H))

/-- The specified finite projection is invertible, also without properness or a bound on H.
Source: blueprint four arrows; Stacks Tags 0944, 0D6D and 0D6E
(blueprint: def-weil-pbc-four-arrows).
Proof: the coefficient-change adjunction comparison identifies the restriction of this
adjunct with the canonical uncompleted projection-formula mate for (P_n)_Y. The perfect
coefficient theorem lemma-weil-pbc-perfect-projection-formula gives the signed finite-total
inverse. Exact restriction reflects derived isomorphisms by
lem-weil-pbc-ring-sheaf-change-adjunction, hence the original quotient-linear map is an
isomorphism. The same argument applies to f' and H = Lg'*K. -/
theorem AdicCoefficientDatum.finiteProjection_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : d.derived X) (n : ℕ) : IsIso (d.finiteProjection f H n) := by
  have he : d.finiteProjection f H n = completedDirectImageProjectionFormula f d n H := by
    rw [AdicCoefficientDatum.finiteProjection, completedDirectImageProjectionFormula,
      derivedComparison d f n]
    exact scalarProjection_eq f (d.completedRing Y) (d.finiteRing Y n)
      (d.completedRing X) (d.finiteRing X n) (d.projection Y n) (d.projection X n)
      (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n) H
  rw [he]
  exact (completedDirectImageProjectionFormula_properties f d).1 n H

attribute [instance] AdicCoefficientDatum.finiteProjection_isIso

/-- A square of four arrows with exactly the asserted three isomorphisms. No equation
between its two paths is imposed. Source: blueprint four arrows
(blueprint: def-weil-pbc-four-arrows). -/
structure FourFiniteLevelArrows {C : Type v} [Category.{w} C] (corners : Fin 4 → C) where
  h : corners 0 ≅ corners 1
  h' : corners 2 ≅ corners 3
  v : corners 0 ⟶ corners 2
  v' : corners 1 ≅ corners 3

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

-- Keep coefficient transport outside the expanded exchange term. In particular, generalize
-- the ring sheaves before specializing from the function presentation to the quotient tower.
private structure ExchangeInvertible (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (M : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ))) : Prop where
  isIso : ∀ hc : HEq
    (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing X' Λ) c_f c_g')
    (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing Y' Λ)
      (finiteOriginFunctionRing X' Λ) c_g c_f'),
    IsIso ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing Y Λ)
      (finiteOriginFunctionRing X' Λ) (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app M)

end AlgebraicGeometry.Scheme
