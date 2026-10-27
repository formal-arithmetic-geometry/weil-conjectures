/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf

import all Sheaf.Paper.ConstructibleCoefficientSerre
import all Sheaf.Paper.FiniteCoefficientIntrinsicConstructibility
import Sheaf.Paper.LisseNormalizedTowerLocalModels
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! Properties of normalized Tate tensor models.

Source: smooth-purity transport, construction of the normalized Tate-unit tower.
(blueprint: lem-pur-normalized-tate-tensor-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped ZeroObject
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem finiteSheaf_lisse (T : Scheme.{u}) [IsNoetherian T]
    (ell : ℕ) [Fact ell.Prime] (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    ProEtale.IsFiniteLocallyConstant (coefficient ell (n + 1))
      (finiteSheaf T ell n d) := by
  let A := coefficient.{u} ell (n + 1)
  let F := finiteEtaleTateTwist T (ell ^ (n + 1)) A (CharP.cast_eq_zero _ _) d
  have hInv (t : T) : IsUnit ((ell ^ (n + 1) : ℕ) : T.presheaf.stalk t) := by
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (hT.pow (n + 1)).map (T.presheaf.germ ⊤ t (by trivial)).hom
  obtain ⟨⟨V, hV⟩, _, _, _⟩ := finite_etale_torsion_twist_line T (ell ^ (n + 1))
    (pow_pos (Fact.out : ell.Prime).pos _) hInv A (CharP.cast_eq_zero _ _) d
  let D : LocallyConstantDatum F :=
    { cover := V
      isConstant := fun i ↦ Sheaf.isConstant_of_iso _ (hV i).some }
  have hF : IsFiniteLocallyConstantSheaf F :=
    (finite_locally_constant_module_values_iff F).1.mp
      ⟨D, fun i ↦ ⟨ModuleCat.of A A, inferInstance, hV i⟩⟩
  let := hF
  exact ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj F

private def finiteTwist_singleIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    finiteTwist T ell n d ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (finiteSheaf T ell n d) :=
  (comparison (coefficient ell (n + 1)) T).mapIso
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
      (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
      (CharP.cast_eq_zero _ _) T (by simpa using hT.pow (n + 1)) d) ≪≫
    ((comparison (coefficient ell (n + 1)) T).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((Functor.mapDerivedCategorySingleFunctor
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (coefficient ell (n + 1))) T) 0).app _) ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ))
      (-(2 * (d : ℤ))) 0 (by omega)).app _

private theorem finiteTwist_lisse (T : Scheme.{u}) [IsNoetherian T]
    (ell : ℕ) [Fact ell.Prime] (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) (q : ℤ) :
    ProEtale.IsFiniteLocallyConstant (coefficient ell (n + 1))
      ((_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d)) := by
  let e := (_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (finiteTwist_singleIso T ell hT n d)
  apply ProEtale.isFiniteLocallyConstant_of_iso e.symm
  by_cases hq : q = -(2 * (d : ℤ))
  · subst q
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _
        (-(2 * (d : ℤ)))).app _).symm (finiteSheaf_lisse T ell hT n d)
  · have hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (finiteSheaf T ell n d))) := by
      rcases lt_or_gt_of_ne hq with hq | hq
      · exact _root_.DerivedCategory.isZero_of_isGE _ _ _ hq
      · exact _root_.DerivedCategory.isZero_of_isLE _ _ _ hq
    let Z : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (n + 1))) := 0
    let : IsFiniteLocallyConstantSheaf Z :=
      IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)
    let P := ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (coefficient ell (n + 1))) T
    have hzero : IsZero (P.obj Z) := P.map_isZero (isZero_zero _)
    exact ProEtale.isFiniteLocallyConstant_of_iso (hzero.iso hz)
      (ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj Z)

/-- Finite local constancy depends only on the finite underlying local set models:
a finite refinement makes every operation of the new finite coefficient ring constant. -/
private theorem finite_lisse_change_coefficients (X : Scheme.{u})
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (e : (sheafCompose (ProEt.topology X) (CategoryTheory.forget (ModuleCat B))).obj G ≅
      (sheafCompose (ProEt.topology X) (CategoryTheory.forget (ModuleCat A))).obj F)
    (hF : ProEtale.IsFiniteLocallyConstant A F) :
    ProEtale.IsFiniteLocallyConstant B G := by
  classical
  obtain ⟨I, W, g, hg, he⟩ := hF
  let V : Cover.{u + 1} proetalePrecoverage X :=
    { I₀ := I
      X := W
      f := g
      mem₀ := hg }
  have hl (i : I) : ProEtale.IsFiniteLocallyConstant B
      ((ProEtale.upperStar (ModuleCat B) (g i)).obj G) := by
    obtain ⟨N, hN, ⟨eN⟩⟩ := he i
    let := hN
    exact finiteConstantUnderlying_lisse (W i) B _ N
      ((fixedUnderlyingPullback (g i) B).app G ≪≫
        (proEtaleSheafInverseImage (g i) (Type (u + 1))).mapIso e ≪≫
        ((fixedUnderlyingPullback (g i) A).app F).symm ≪≫
        (sheafCompose (ProEt.topology (W i))
          (CategoryTheory.forget (ModuleCat A))).mapIso eN ≪≫
        (constantCommuteCompose (ProEt.topology (W i))
          (CategoryTheory.forget (ModuleCat A))).app N)
  choose J Z f hf hmodels using hl
  refine ⟨Σ i, J i, fun p ↦ Z p.1 p.2, fun p ↦ f p.1 p.2 ≫ g p.1,
    Precoverage.comp_mem_coverings V.f V.mem₀ f hf, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ := hmodels i j
  exact ⟨N, hN, ⟨(ProEtale.upperStarComp (ModuleCat B) (f i j) (g i)).app G ≪≫ eN⟩⟩

private def realizationUnderlying (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (F : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (coefficient ell (n + 1)))) :
    (underlying T ((pbcAdicRings T (datum ell)).obj (op n))).obj
      ((realization T ell n).obj F) ≅
      (sheafCompose (ProEt.topology T)
        (CategoryTheory.forget (ModuleCat (coefficient ell (n + 1))))).obj F := by
  exact (sheafCompose (ProEt.topology T)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      (asIso ((sheafificationAdjunction (ProEt.topology T)
        AddCommGrpCat.{u + 1}).counit.app
          ((sheafCompose (ProEt.topology T)
            (forget₂ (ModuleCat.{u + 1} (coefficient ell (n + 1))) AddCommGrpCat.{u + 1})).obj F)))

/-- The exact module pullback comparison gives the converse of local_finite. -/
private theorem relative_lisse_of_fixed {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : adicLisseConstantRing Y A ⟶ R)
    (K : DerivedCategory (pbcModules Y R)) (q : ℤ)
    (h : ProEtale.IsFiniteLocallyConstant A
      ((ProEtale.upperStar (ModuleCat A) g).obj
        ((CoefficientSerre.proEtaleModuleRestriction Y A).obj
          ((pbcRestrict c).obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K))))) :
    IsRelativelyFiniteLisseModule g A
      ((pbcRestrict ((adicTowerInverseImage g).map c)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((adicTowerPullback g R).obj K))) := by
  let C := adicLisseConstantRing Y A
  let R' := (adicTowerInverseImage g).obj R
  let C' := (adicTowerInverseImage g).obj C
  let FR := proEtaleRingModulePullback g R R' (Iso.refl _)
  let FC := proEtaleRingModulePullback g C C' (Iso.refl _)
  let H := (_root_.DerivedCategory.homologyFunctor _ q).obj K
  let U := pbcRestrict ((adicTowerInverseImage g).map c)
  let U₀ := pbcRestrict c
  let e₁ : U.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((adicTowerPullback g R).obj K)) ≅ U.obj (FR.obj H) :=
    U.mapIso ((FR.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  let e₂ : FC.obj (U₀.obj H) ≅ U.obj (FR.obj H) := by
    let t := proEtaleRingRestrictionPullbackInv g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    exact asIso (t.app H)
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl C')).choose
  let e₃ : FC.obj (U₀.obj H) ≅
      (proEtaleModuleInverseImage g C).obj (U₀.obj H) := by exact θ _
  apply (CoefficientSerre.relative_finite_iff g A _).mpr
  exact ProEtale.isFiniteLocallyConstant_of_iso
    ((CoefficientSerre.relativeRestriction g A).mapIso (e₁ ≪≫ e₂.symm ≪≫ e₃) ≪≫
      CoefficientSerre.relativePullbackComparison g A (U₀.obj H)).symm h

/-- A projection-normalized strict Tate tensor tower has a common single-degree
local model and constructible cohomology in both finite coefficient presentations.
This constructs the local models for an already given tower, rather than constructing
or reconstructing that tower.

Source: smooth-purity transport, the proof of
`lem-pur-normalized-tate-tensor-tower`, Step 4.
(blueprint: lem-pur-normalized-tate-tensor-models)

Proof: the finite-etale primitive-root trivializations give finite-lisse finite
Tate lines. Exact site comparison and the explicit single-complex isomorphism show
that finiteTwist has finite-lisse cohomology in degree -2d and zero elsewhere.
Exact coefficient realization and e identify the underlying cohomology sheaves of M
with these sheaves. Restriction of scalars preserves underlying sets. A finite
covering refinement makes all module operations constant on each finite constant
set model, so finite local constancy transfers between the two coefficient rings.
The exact ringed pullback and scalar restriction comparisons give the relative
finite-lisse hypotheses on the identity stratum. The same single-complex
isomorphisms give the common cohomological window [-2d,-2d]. Apply the generic
lisseNormalizedTower_local_models theorem, invert its identifications and cancel
these isomorphisms in its transition equation. On the trivial stratification this
gives UniformAdicTowerData with both endpoints -2d. The finite-lisse cohomology in
each presentation gives constructibility on that same stratum. The argument also
applies to d=0 and the empty scheme. The retained strict-tower and projection
normalization assumptions are stronger than this route needs.
-/
theorem normalizedTateTensorTower_properties
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅
      (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d)
    (hp : ProjectionNormalized T ell hT d M e h)
    (hsquare : ∀ (b a : ℕ) (hab : a ≤ b)
      (r : CoefficientLineComparison
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
        (ell ^ (b + 1)) (ell ^ (a + 1))
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T),
      (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
          (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
          (derivedRealization T ell a).map (proTwistMap d r) =
        (M.normalization b a hab).hom ≫ (e a).hom) :
    ∃ (S : Stratification T) (W : UniformAdicTowerData (datum.{u} ell) M S),
      W.lower = -(2 * (d : ℤ)) ∧ W.upper = -(2 * (d : ℤ)) ∧
    (∀ (n : ℕ) (q : ℤ),
      @IsConstructibleProEtaleCoefficientModuleSheaf T (Ring.{u} ell ⧸
          (datum.{u} ell).ideal ^ (n + 1)) _ ((datum.{u} ell).quotientFinite n)
        ((pbcRestrict (pbcLevelConstantComparison T (datum.{u} ell) n).hom).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)))) ∧
    (∀ (n : ℕ) (q : ℤ),
      IsConstructibleProEtaleFixedModuleSheaf T (coefficient ell (n + 1))
        ((_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d))) := by
  classical
  have _ := hp
  have _ := hsquare
  let k : ℤ := -(2 * (d : ℤ))
  have hb (n : ℕ) (q : ℤ) (hq : q < k ∨ k < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)) := by
    apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (e n ≪≫ finiteModelIso T ell hT n d))
    rcases hq with hq | hq
    · exact _root_.DerivedCategory.isZero_of_isGE _ _ _ hq
    · exact _root_.DerivedCategory.isZero_of_isLE _ _ _ hq
  have hl (n : ℕ) (q : ℤ) :
      ProEtale.IsFiniteLocallyConstant ((Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1)))
        ((CoefficientSerre.proEtaleModuleRestriction T _).obj
          ((pbcRestrict (pbcLevelConstantComparison T (datum ell) n).hom).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)))) := by
    let F := (_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d)
    let E := (_root_.DerivedCategory.homologyFunctor _ q).mapIso (e n) ≪≫
      (((realization T ell n).mapDerivedCategoryHomologyFunctorIso q).app
        (finiteTwist T ell n d)).symm
    let G := (CoefficientSerre.proEtaleModuleRestriction T
      (Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1))).obj
        ((pbcRestrict (pbcLevelConstantComparison T (datum ell) n).hom).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    have eSets : (sheafCompose (ProEt.topology T)
        (CategoryTheory.forget (ModuleCat.{u + 1}
          (Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1))))).obj G ≅
        (sheafCompose (ProEt.topology T)
          (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient ell (n + 1))))).obj F := by
      change (underlying T ((pbcAdicRings T (datum ell)).obj (op n))).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)) ≅ _
      exact (underlying T _).mapIso E ≪≫ realizationUnderlying T ell n F
    exact finite_lisse_change_coefficients T (coefficient ell (n + 1)) _ F G eSets
      (finiteTwist_lisse T ell hT n d q)
  have hr (n : ℕ) (q : ℤ) := relative_lisse_of_fixed (𝟙 T)
    ((Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1))) _
    (pbcLevelConstantComparison T (datum ell) n).hom (M.level n) q
    (ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId _ T).app _).symm (hl n q))
  obtain ⟨V, hV, hmodels⟩ := lisseNormalizedTower_local_models T T (𝟙 T)
    (datum ell) M k k le_rfl hb hr
  let S := Stratification.trivial T
  have hm (U : T.ProEt) (f : U ⟶ ⊤_ T.ProEt) (hf : V f) :
      Nonempty (AdicTowerLocalModel (datum ell) (U.hom ≫ 𝟙 T) M k k) := by
    obtain ⟨L, hbound, hadic, hfinite, ε, hε⟩ := hmodels U f hf
    refine ⟨{
      complex := L
      bounded := hbound
      adicLisse := hadic
      finiteLisse := hfinite
      identification := fun n ↦ (ε n).symm
      compatible := ?_ }⟩
    intro b a hab
    apply (cancel_epi (ε b).hom).1
    simp only [Iso.symm_hom]
    rw [← Category.assoc, hε b a hab]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    let F := pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ 𝟙 T)).map
      (pbcAdicQuotient T (datum ell) b a hab))
    have hi := (F.mapIso (ε a)).hom_inv_id
    change F.map (ε a).hom ≫ F.map (ε a).inv = 𝟙 _ at hi
    rw [hi, Category.comp_id]
  let W : UniformAdicTowerData (datum ell) M S :=
    { lower := k
      upper := k
      bounds := le_rfl
      cover := fun _ ↦ V
      covering := fun _ ↦ hV
      model := fun _ U f hf ↦ (hm U f hf).some }
  refine ⟨S, W, rfl, rfl, ?_, ?_⟩
  · intro n q
    apply (CoefficientSerre.coefficient_constructible_iff T _ _).mpr
    refine ⟨S, fun _ ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId _ T).app _).symm (hl n q)
  · intro n q
    let H := (_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d)
    have hloc (i : Fin S.n) : ProEtale.IsFiniteLocallyConstant (coefficient ell (n + 1))
        ((ProEtale.upperStar (ModuleCat (coefficient ell (n + 1)))
          (S.immersion i)).obj H) :=
      ProEtale.isFiniteLocallyConstant_of_iso
        ((ProEtale.upperStarId _ T).app H).symm (finiteTwist_lisse T ell hT n d q)
    refine ⟨S, Nat.zero_lt_one, S.isConstructible_stratum, fun i ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over _ _ (hloc i)
      exact ⟨I, U, f, hf, fun j ↦ ⟨(he j).choose, (he j).choose_spec.2⟩⟩
    · exact ProEtale.finite_geometricStalk_of_finite_models _ _ (hloc i)

end AlgebraicGeometry.Scheme.PurityIntegralTower
