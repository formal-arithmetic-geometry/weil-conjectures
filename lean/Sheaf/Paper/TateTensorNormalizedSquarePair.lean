/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
import Sheaf.Paper.TateTensorPairFiniteSquare
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Fixed-pair reduction of the normalized Tate tensor square.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square-pair)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange finiteModelIso

def normalizedAt
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d) (n : ℕ)
    (c : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d) : Prop :=
  ProjectionBalanced T ell n d c ∧
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map
        ((finiteModelIso T ell hT n d).inv ≫ (e n).inv) ≫ (M.evaluation n).hom ≫
        (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map (eqToHom h) =
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
        (-(2 * (d : ℤ)))).hom.app _ ≫
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map
        ((pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)).map c.hom) ≫
      (Functor.mapDerivedCategorySingleFunctor
        ((CategoryTheory.evaluation ℕᵒᵖ
          (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
        (-(2 * (d : ℤ)))).inv.app (strictTower T ell d)

private theorem single_restriction_injective
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (n : ℤ) {M N : A}
    (f g : (_root_.DerivedCategory.singleFunctor A n).obj M ⟶
      (_root_.DerivedCategory.singleFunctor A n).obj N)
    (h : F.mapDerivedCategory.map f = F.mapDerivedCategory.map g) : f = g := by
  obtain ⟨f, rfl⟩ := (_root_.DerivedCategory.singleFunctor A n).map_surjective f
  obtain ⟨g, rfl⟩ := (_root_.DerivedCategory.singleFunctor A n).map_surjective g
  congr 1
  apply F.map_injective
  apply (_root_.DerivedCategory.singleFunctor B n).map_injective
  apply (cancel_epi ((F.mapDerivedCategorySingleFunctor n).hom.app M)).1
  have hf := (F.mapDerivedCategorySingleFunctor n).hom.naturality f
  have hg := (F.mapDerivedCategorySingleFunctor n).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← hf, ← hg, h]

private theorem restriction_injective_on_models
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (n : ℤ)
    {X Y : DerivedCategory (pbcModules T S)} {M N : pbcModules T S}
    (i : X ≅ (_root_.DerivedCategory.singleFunctor _ n).obj M)
    (j : Y ≅ (_root_.DerivedCategory.singleFunctor _ n).obj N)
    (f g : X ⟶ Y) (h : (pbcDerivedRestrict φ).map f =
      (pbcDerivedRestrict φ).map g) : f = g := by
  have : (pbcRestrict φ).Faithful := ⟨fun {M N} f g h ↦ by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h⟩
  have hh : i.inv ≫ f ≫ j.hom = i.inv ≫ g ≫ j.hom := by
    apply single_restriction_injective (pbcRestrict φ) n
    change (pbcDerivedRestrict φ).map (i.inv ≫ f ≫ j.hom) =
      (pbcDerivedRestrict φ).map (i.inv ≫ g ≫ j.hom)
    simp only [Functor.map_comp, h]
  exact (cancel_epi i.inv).1 ((cancel_mono j.hom).1 (by
    simpa only [Category.assoc] using hh))

private theorem normalizedAt_evaluation
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d) (n : ℕ)
    (c : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d)
    (hc : normalizedAt T ell hT d M e h n c) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map (e n).hom ≫
        (finiteEvaluationModel T ell hT d n c).hom =
      (M.evaluation n).hom ≫
        (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map (eqToHom h) := by
  have hn := congrArg (fun z ↦
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map
      ((e n).hom ≫ (finiteModelIso T ell hT n d).hom) ≫ z) hc.2
  simpa only [finiteEvaluationModel, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id_assoc] using hn.symm

private theorem normalized_pair_assembly
    {B A C : Type*} [Category B] [Category A] [Category C]
    {L : B ⥤ A} {S : A ⥤ B} (adj : L ⊣ S)
    (P : B ⥤ C) (Q : A ⥤ C) (v : S ⋙ P ≅ Q)
    {Mb X : B} {Ma Y : A} (eb : Mb ≅ X) (ea : Ma ≅ Y)
    (ρ : L.obj Mb ≅ Ma) (γ : L.obj X ⟶ Y)
    {tb ta sb sa : C} (vb : P.obj Mb ≅ tb) (va : Q.obj Ma ≅ ta)
    (βb : P.obj X ≅ sb) (βa : Q.obj Y ≅ sa)
    (t : tb ⟶ ta) (s : sb ⟶ sa) (kb : tb ⟶ sb) (ka : ta ⟶ sa)
    (hb : P.map eb.hom ≫ βb.hom = vb.hom ≫ kb)
    (ha : Q.map ea.hom ≫ βa.hom = va.hom ≫ ka)
    (ht : t ≫ ka = kb ≫ s)
    (hρ : P.map (adj.homEquiv _ _ ρ.hom) ≫ v.hom.app Ma ≫ va.hom = vb.hom ≫ t)
    (hγ : P.map (adj.homEquiv _ _ γ) ≫ v.hom.app Y ≫ βa.hom = βb.hom ≫ s)
    (hinj : ∀ f g : Mb ⟶ S.obj Y, P.map f = P.map g → f = g) :
    L.map eb.hom ≫ γ = ρ.hom ≫ ea.hom := by
  apply (adj.homEquiv Mb Y).injective
  apply hinj
  apply (cancel_mono (v.hom.app Y ≫ βa.hom)).1
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [Functor.map_comp, Category.assoc]
  rw [hγ]
  have hv := v.hom.naturality ea.hom
  dsimp only [Functor.comp_map] at hv
  rw [reassoc_of% hv, ha, reassoc_of% hρ, reassoc_of% hb]
  simpa only [Category.assoc] using congrArg (fun z ↦ vb.hom ≫ z) ht.symm

/-- The finite scalar square for one fixed pair, assuming the two selected
projection-normalized models. This is the local tensor and mate calculation;
the all-level theorem only supplies these two models from `ProjectionNormalized`.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square-pair)

Proof: evaluate the two maps on the selected ordinary root-tensor models. The
`ProjectionBalanced` equations identify scalar extension followed by the finite
root comparison with quotient tensor balancing. The two `normalizedAt` equations
transport these ordinary formulas through exact single/evaluation comparisons.
The scalar adjunction mate and the strict tower transition then identify the
result with `M.normalization`; generator equality extends by sheafification.
Equal indices, zero tensor powers, and empty schemes use the same unit formulas. -/
theorem tateTensor_normalizedSquare_of_pair
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d)
    (b a : ℕ) (hab : a ≤ b)
    (cb : (realization T ell b).obj (finiteSheaf T ell b d) ≅ quotientLine T ell b d)
    (ca : (realization T ell a).obj (finiteSheaf T ell a d) ≅ quotientLine T ell a d)
    (hb : normalizedAt T ell hT d M e h b cb)
    (ha : normalizedAt T ell hT d M e h a ca)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
        (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
        (derivedRealization T ell a).map (proTwistMap d r) =
      (M.normalization b a hab).hom ≫ (e a).hom := by
  let ψ := pbcAdicQuotient T (datum.{u} ell) b a hab
  let πb := pbcAdicProjection T (datum.{u} ell) b
  let πa := pbcAdicProjection T (datum.{u} ell) a
  let P := pbcDerivedRestrict πb
  let Q := pbcDerivedRestrict πa
  let S := pbcDerivedRestrict ψ
  let L := pbcDerivedExtend ψ
  let adj := pbcDerivedScalarAdjunction ψ
  let v := pbcDerivedRestrictComp πb ψ πa
    (pbcAdicProjection_comp T (datum.{u} ell) b a hab)
  let Eb := (derivedRealization T ell b).obj (finiteTwist T ell b d)
  let Ea := (derivedRealization T ell a).obj (finiteTwist T ell a d)
  let γ : L.obj Eb ⟶ Ea :=
    (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
      (derivedRealization T ell a).map (proTwistMap d r)
  let βb := finiteEvaluationModel T ell hT d b cb
  let βa := finiteEvaluationModel T ell hT d a ca
  have hβb := normalizedAt_evaluation T ell hT d M e h b cb hb
  have hβa := normalizedAt_evaluation T ell hT d M e h a ca ha
  have hfinite := finite_transition_square T ell hT d b a hab r cb ca hb.1 ha.1
  change P.map (adj.homEquiv Eb Ea γ) ≫ v.hom.app Ea ≫ βa.hom =
    βb.hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app
        (strictDerivedTower T ell d) at hfinite
  have htransition := M.transition b a hab
  change P.map (adicTowerSemilinearTransition T (datum.{u} ell)
      M.level M.normalization b a hab) ≫ v.hom.app (M.level a) ≫
      (M.evaluation a).hom = (M.evaluation b).hom ≫
        (pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app
          M.tower at htransition
  have hnorm : adj.homEquiv _ _ (M.normalization b a hab).hom =
      adicTowerSemilinearTransition T (datum.{u} ell)
        M.level M.normalization b a hab := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [← hnorm] at htransition
  apply normalized_pair_assembly adj P Q v (e b) (e a) (M.normalization b a hab) γ
    (M.evaluation b) (M.evaluation a) βb βa
    ((pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app M.tower)
    ((pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app
      (strictDerivedTower T ell d))
    ((pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) b).map (eqToHom h))
    ((pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) a).map (eqToHom h))
    hβb hβa _ htransition hfinite
  · intro f g hfg
    exact restriction_injective_on_models T πb (-(2 * (d : ℤ)))
      (e b ≪≫ finiteModelIso T ell hT b d)
      (S.mapIso (finiteModelIso T ell hT a d) ≪≫
        (Functor.mapDerivedCategorySingleFunctor (pbcRestrict ψ)
          (-(2 * (d : ℤ)))).app _) f g hfg
  · exact ((pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell))
      b a hab).naturality (eqToHom h)).symm

end AlgebraicGeometry.Scheme.PurityIntegralTower
