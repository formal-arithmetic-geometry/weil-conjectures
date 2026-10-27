/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.TowerCompactSupportProjectionFormula
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SmoothPurityCoefficientTowers

import Sheaf.Algebra.Homology.CochainTensorModelRigidity
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedTensorComparisonExtension
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Uniform tensor domains and evaluation of tower projection maps

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3);
Stacks Project, Tags 08G1, 06YQ, 0G7E, 07A4, 06YU and 0118
(blueprint: lem-sp-tower-projection-domain-evaluation).

The existing properMap, openTensor inverse, maps_natural, properMap_evaluation and
openMap_evaluation supply the canonical arrows and their already recorded evaluation
laws. The theorem below supplies their uniform domains, their bounded level models,
and the direct-image naturality square. No finite-level representatives form a tower.
The index n denotes the positive exponent n+1 throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped ZeroObject

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The exact finite open operation applied termwise to a level complex.
This only packages the existing extension functor with its existing additive instance.
Source: blueprint paragraph (3), the representative j_!T_n
(blueprint: lem-sp-tower-projection-domain-evaluation). -/
def levelOpenComplex (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :=
  letI := b.finite n
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  (sfIntrinsicExtensionByZero j (R l E n)).mapHomologicalComplex (.up ℤ)

@[irreducible] private def tensorRepresentativeComparison
    {C₁ C₂ C₃ P S : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* P] [Category* S]
    (ι : P ⥤ C₁) (J : P ⥤ S) (κ : S ⥤ C₂)
    (L : C₁ ⥤ C₂) (Qh : C₂ ⥤ C₃) (Q : C₁ ⥤ C₃)
    (B : C₂ × C₂ ⥤ C₂) (T : C₃ × C₃ ⥤ C₃) (F : C₁ × C₁ ⥤ C₁)
    (c : (L.prod L) ⋙ B ≅ F ⋙ L)
    (t : (κ.prod κ) ⋙ B ⋙ Qh ≅ ((κ ⋙ Qh).prod (κ ⋙ Qh)) ⋙ T)
    (hj : (ι.prod ι) ⋙ (L.prod L) = (J.prod J) ⋙ (κ.prod κ))
    (hjQ : (J.prod J) ⋙ ((κ ⋙ Qh).prod (κ ⋙ Qh)) =
      ((ι ⋙ L ⋙ Qh).prod (ι ⋙ L ⋙ Qh))) (q : L ⋙ Qh ≅ Q) :
    (ι.prod ι) ⋙ F ⋙ Q ≅ ((ι ⋙ Q).prod (ι ⋙ Q)) ⋙ T :=
  Functor.isoWhiskerLeft ((ι.prod ι) ⋙ F) q.symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (ι.prod ι) c.symm) Qh ≪≫
    Functor.isoWhiskerRight (eqToIso hj) (B ⋙ Qh) ≪≫
    Functor.isoWhiskerLeft (J.prod J) t ≪≫
    Functor.isoWhiskerRight (eqToIso hjQ) T ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerLeft ι q) (Functor.isoWhiskerLeft ι q)) T

private theorem siteTensorComparison (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) R ≅
      SheafOfModules.wfSiteDerivedTensor (ProEt.topology X) R) := by
  let J := ProEt.topology X
  let A := SemilinearSections.Mod.{u + 1, u, u + 1} J R
  let P := SheafOfModules.cochainTensorFlatRepresentatives J R
  let W := (SheafOfModules.wf_site_derived_tensor_descent.{u + 1, u, u + 2, 0, 0}
    J R).choose
  have hW := (SheafOfModules.wf_site_derived_tensor_descent.{u + 1, u, u + 2, 0, 0}
    J R).choose_spec
  let q := HomotopyCategory.quotient A (.up ℤ)
  let i : P.FullSubcategory ⥤ W.FullSubcategory :=
    W.lift (P.ι ⋙ q) (fun K ↦ by
      apply (hW.1 _).2
      refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K.obj).1
        K.property.1, ?_⟩
      intro n
      exact (SheafOfModules.flat_to_cat R _ (K.property.2 n)).2)
  let H := hW.2.2.1.choose
  let hH := hW.2.2.1.choose_spec.1.some
  let hT := hW.2.2.1.choose_spec.2.choose_spec.some
  let total := SheafOfModules.cochainTensorTotal J R
  have hc : (q.prod q) ⋙ H ≅ total ⋙ q := hH
  have ht : (W.ι.prod W.ι) ⋙ H ⋙ DerivedCategory.Qh ≅
      ((W.ι ⋙ DerivedCategory.Qh).prod (W.ι ⋙ DerivedCategory.Qh)) ⋙
        SheafOfModules.wfSiteDerivedTensor J R := hT
  let r := tensorRepresentativeComparison P.ι i W.ι q DerivedCategory.Qh
    DerivedCategory.Q H (SheafOfModules.wfSiteDerivedTensor J R) total hc ht rfl rfl
      (DerivedCategory.quotientCompQhIso A)
  exact ⟨((SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u, u + 1, u + 2, 0, 0}
    J R).choose_spec.2.1 _ r).choose⟩

private theorem level_flat_model (Y : Scheme.{u})
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (K : DerivedCategory (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology Y) R)) (v w : ℤ)
    (h : HasRingedSiteTorAmplitudeOfUniverses.{u + 1, u, u + 1, u + 2} R K v w) :
    ∃ P : CochainComplex
        (SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology Y) R) ℤ,
      (∀ i : ℤ, i < v ∨ w < i → IsZero (P.X i)) ∧
      SemilinearSections.flatTerms.{u + 1, u, u + 1} (ProEt.topology Y) R P ∧
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  have ht : ∀ M i, i < v ∨ w < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((SheafOfModules.wfSiteDerivedTensor (ProEt.topology Y) R).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj M))) := by
    intro M i hi
    obtain ⟨e⟩ := siteTensorComparison Y R
    exact (h.2 M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (e.app (K, (DerivedCategory.singleFunctor _ 0).obj M))).symm
  obtain ⟨P, hf, hb, he⟩ :=
    (SheafOfModules.torAmplitude_iff_exists_bounded_flat_model
      (ProEt.topology Y) R K v w h.1).1 ht
  have : P.IsStrictlyLE w :=
    (CochainComplex.isStrictlyLE_iff P w).2 (fun i hi ↦ hb i (Or.inr hi))
  exact ⟨P, hb, hf,
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P w hf, he⟩

private theorem bounds_of_model (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology X) R))
    (P : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology X) R) ℤ) (a b : ℤ)
    (hp : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (e : K ≅ DerivedCategory.Q.obj P) : K.IsGE a ∧ K.IsLE b := by
  have hz (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    exact ((P.sc i).isZero_homology_of_isZero_X₂ (hp i hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app P)
  exact ⟨(DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (Or.inl hi)),
    (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (Or.inr hi))⟩

private theorem total_support (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology X) R) ℤ) (a b v w : ℤ)
    (hP : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hQ : ∀ i : ℤ, i < v ∨ w < i → IsZero (Q.X i)) :
    ∀ i : ℤ, i < a + v ∨ b + w < i →
      IsZero (((SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (ProEt.topology X) R).obj (P, Q)).X i) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have heq : p + q = i := hpq
  have hz : IsZero (((CategoryTheory.MonoidalCategory.curriedTensor _).obj
      (P.X p)).obj (Q.X q)) := by
    by_cases hp : p < a ∨ b < p
    · exact ((CategoryTheory.MonoidalCategory.curriedTensor _).flip.obj
        (Q.X q)).map_isZero (hP p hp)
    · exact ((CategoryTheory.MonoidalCategory.curriedTensor _).obj
        (P.X p)).map_isZero (hQ q (by omega))
  exact hz.eq_of_src _ _

@[irreducible] private def levelTensorModel (base : Base l E) (X : Scheme.{u}) (n : ℕ) :
    ProEtaleTensorModel X (SpTowerShriek.B l E X n) := by
  let i := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives X (SpTowerShriek.B l E X n))
    (P' := CochainComplex.IsKFlatIndependentCoefficients)
    (fun P hP ↦ (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1)
  exact { tensor := levelTensor l E base X n
          representative := Functor.isoWhiskerLeft (i.prod i)
            ((base.calculus X).levelTensorModels n).comparison }

private theorem pull_kflat (base : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (P : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology Y) (SpTowerShriek.B l E Y n)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : SemilinearSections.flatTerms.{u + 1, u, u + 1}
      (ProEt.topology Y) (SpTowerShriek.B l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((proEtaleConstantRingPullback (R l E n) f).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hp : proEtaleFlatRepresentatives Y (SpTowerShriek.B l E Y n) P :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hk, hf⟩
  have h := (proEtaleCanonicalTensorPullback f _ _
    (proEtaleConstantRingComparison f (R l E n))
    (levelTensorModel l E base Y n) (levelTensorModel l E base X n)).1 P hp
  exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 h.1

@[irreducible] private def tensor_level_iso (base : Base l E) (o : Operations l E base)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : D l E X) (B : D l E Y) (n : ℕ)
    (T : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology X) (SpTowerShriek.B l E X n)) ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1}
      (ProEt.topology Y) (SpTowerShriek.B l E Y n)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : SemilinearSections.flatTerms.{u + 1, u, u + 1}
      (ProEt.topology Y) (SpTowerShriek.B l E Y n) P)
    (eT : (Ev l E X n).obj C ≅ DerivedCategory.Q.obj T)
    (eP : (Ev l E Y n).obj B ≅ DerivedCategory.Q.obj P) :
    (Ev l E X n).obj ((tensor l E base X).obj
      (C, (pull l E base (o.geometry f)).obj B)) ≅
    DerivedCategory.Q.obj ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
      (ProEt.topology X) (SpTowerShriek.B l E X n)).obj
      (T, ((proEtaleConstantRingPullback (R l E n) f).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let e := ((o.geometry f).pullEvaluation n).app B ≪≫
    (proEtaleConstantRingDerivedPullback (R l E n) f).mapIso eP ≪≫
      (Functor.mapDerivedCategoryFactors (proEtaleConstantRingPullback (R l E n) f)).app P
  let t := (ringedTensorComparison_extension (ProEt.topology X)
    (SpTowerShriek.B l E X n) ((base.calculus X).levelClosed n)
      ((base.calculus X).levelTensorModels n)).choose
  exact ((base.calculus X).tensorEvaluation n).app _ ≪≫
    (levelTensor l E base X n).mapIso (Iso.prod eT e) ≪≫
      (t T _ (Or.inr (pull_kflat l E base f n P hk hf))).symm

private theorem isZero_of_levels (base : Base l E) (X : Scheme.{u})
    (M : S l E X) (h : ∀ n : ℕ, IsZero ((ev l E X n).obj M)) : IsZero M := by
  let s := ShortComplex.mk (0 : (0 : S l E X) ⟶ M) (0 : M ⟶ 0) (by simp)
  have hs : s.Exact := ((base.calculus X).componentwise s).2
    (fun n ↦ ShortComplex.exact_of_isZero_X₂ _ (h n))
  exact hs.isZero_X₂ rfl rfl

private theorem isGE_of_levels (base : Base l E) (X : Scheme.{u})
    (K : D l E X) (a : ℤ) (h : ∀ n : ℕ, ((Ev l E X n).obj K).IsGE a) :
    K.IsGE a := by
  apply (DerivedCategory.isGE_iff K a).2
  intro i hi
  apply isZero_of_levels l E base X
  intro n
  exact ((DerivedCategory.isGE_iff _ a).1 (h n) i hi).of_iso
    (((ev l E X n).mapDerivedCategoryHomologyFunctorIso i).app K)

private theorem isLE_of_levels (base : Base l E) (X : Scheme.{u})
    (K : D l E X) (b : ℤ) (h : ∀ n : ℕ, ((Ev l E X n).obj K).IsLE b) :
    K.IsLE b := by
  apply (DerivedCategory.isLE_iff K b).2
  intro i hi
  apply isZero_of_levels l E base X
  intro n
  exact ((DerivedCategory.isLE_iff _ b).1 (h n) i hi).of_iso
    (((ev l E X n).mapDerivedCategoryHomologyFunctorIso i).app K)

private theorem openTensor_inv_natural (base : Base l E) (o : Operations l E base)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    {C C' : D l E U} {L L' : D l E Z} (h : C ⟶ C') (k : L ⟶ L') :
    (openD l E base (o.openOp j)).map
        ((tensor l E base U).map
          (Prod.mkHom h ((pull l E base (o.geometry j)).map k))) ≫
        (o.openTensor j C' L').inv =
      (o.openTensor j C L).inv ≫ (tensor l E base Z).map
        (Prod.mkHom ((openD l E base (o.openOp j)).map h) k) := by
  apply ((o.openOp j).derivedAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    o.openTensor_mate, o.openTensor_mate]
  have hn := (o.geometry j).tensorPullback.inv.naturality
    (Prod.mkHom ((openD l E base (o.openOp j)).map h) k)
  change (tensor l E base U).map
      (Prod.mkHom ((pull l E base (o.geometry j)).map
        ((openD l E base (o.openOp j)).map h))
        ((pull l E base (o.geometry j)).map k)) ≫ _ = _ at hn
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
    ← Functor.map_comp]
  congr 2
  ext
  · exact (o.openOp j).derivedAdjunction.unit.naturality h
  · simp

/-- Uniform tensor domains, independent bounded representatives at every positive level,
and evaluation of the proper direct image of the specified open-unit transpose.
The arrows and the other evaluation/naturality laws are the existing properMap,
Operations.openTensor_mate, maps_natural, properMap_evaluation and openMap_evaluation.
Fcomparison is the canonical comparison for both bounded-below inputs obtained here.
There are no constructibility, normalization, origin or projection-invertibility tests.

Source: blueprint latest, integral direct-image proof, paragraph (3); Stacks 08G1,
06YQ, 0G7E, 07A4, 06YU and 0118
(blueprint: lem-sp-tower-projection-domain-evaluation).

Proof:
1. Apply lem-sp-ringed-site-tor-flat-model to B_n with the common interval [v,w].
   Testing Tor amplitude on the tensor unit gives its cohomology interval. By
   det-sp-coefficient-towers-abelian and lem-coef-semilinear-derived-sections,
   exact evaluation computes tower cohomology componentwise and detects zero
   objects. Thus C, B and the exact open extension of C are bounded below.
2. For any representative K_n of C_n, good truncation truncGE a (truncLE b K_n)
   gives T_n supported in [a,b], by def-kun-truncations. Both maps in the truncation
   roof are quasi-isomorphisms, including a=b, where the only term is H^a(K_n).
3. The bounded flat P_n from step 1 is K-flat: filter the signed total tensor of
   any acyclic complex with P_n by its finitely many columns. The quotients are
   shifts of tensor with one flat term, hence acyclic; the filtration sequences
   are degreewise split. Finite induction proves the K-flat test, using
   def-pc-flat-sheaf-modules, def-pc-kflat-complex and def-pc-tensor-complex-sheaves.
4. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves the flat-term K-flat
   models under exact constant-coefficient inverse image. The one-K-flat comparison
   of lem-sfb-ringed-tensor-comparison-extension computes the specified level
   tensor even though T_n need not be flat. Exact j_! preserves the bounds
   of T_n. Total degrees are sums in [a+v,b+w]. Componentwise cohomology detection
   gives the same bounds on both actual tower tensors.
5. The existing properMap is the counit transpose of epsilon tensor one, after
   the canonical pullback/tensor comparison. The existing openTensor inverse is
   the unit transpose of eta tensor one, by Operations.openTensor_mate. The
   simultaneous derived-sections calculus makes both actual natural tower maps;
   maps_natural records this, and properMap_evaluation and openMap_evaluation
   record their identical finite counit/unit transpose words.
6. Apply naturality of Geometry.pushEvaluation to the actual openTensor inverse.
   This is exactly the last displayed square. Compose pushEvaluation with the
   exact openEvaluation, as in Fcomparison, for D=C and D=C tensor f inverse B.
   Steps 1 and 4 put both D in D+. No inference from faithfulness of evaluations,
   no strict assembly of the level models and no projection invertibility is used.
-/
theorem tower_projection_domain_evaluation
    (base : Base l E) (o : Operations l E base)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) (a b v w : ℤ)
    (_hab : a ≤ b) (_hvw : v ≤ w)
    (_hC : ∀ n : ℕ, ((Ev l E X n).obj C).IsGE a ∧
      ((Ev l E X n).obj C).IsLE b)
    (_hB : ∀ n : ℕ, HasRingedSiteTorAmplitudeOfUniverses.{u + 1, u, u + 1, u + 2}
      (SpTowerShriek.B l E Y n) ((Ev l E Y n).obj B) v w) :
    C.IsGE a ∧ B.IsGE v ∧ ((openD l E base (o.openOp c.i)).obj C).IsGE a ∧
    (((tensor l E base X).obj (C, (pull l E base (o.geometry f)).obj B)).IsGE (a + v) ∧
      ((tensor l E base X).obj (C, (pull l E base (o.geometry f)).obj B)).IsLE (b + w)) ∧
    (((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
        (pull l E base (o.geometry c.g)).obj B)).IsGE (a + v) ∧
      ((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
        (pull l E base (o.geometry c.g)).obj B)).IsLE (b + w)) ∧
    (∀ n : ℕ, ∃ T : CochainComplex
        (SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology X) (SpTowerShriek.B l E X n)) ℤ,
      ∃ P : CochainComplex
        (SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology Y) (SpTowerShriek.B l E Y n)) ℤ,
      (∀ i : ℤ, i < a ∨ b < i → IsZero (T.X i)) ∧
      (∀ i : ℤ, i < v ∨ w < i → IsZero (P.X i)) ∧
      SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (ProEt.topology Y) (SpTowerShriek.B l E Y n) P ∧
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P ∧
      Nonempty ((Ev l E X n).obj C ≅ DerivedCategory.Q.obj T) ∧
      Nonempty ((Ev l E Y n).obj B ≅ DerivedCategory.Q.obj P) ∧
      Nonempty ((Ev l E X n).obj
          ((tensor l E base X).obj (C, (pull l E base (o.geometry f)).obj B)) ≅
        DerivedCategory.Q.obj
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (ProEt.topology X)
            (SpTowerShriek.B l E X n)).obj
            (T, ((proEtaleConstantRingPullback (R l E n) f).mapHomologicalComplex
              (.up ℤ)).obj P))) ∧
      Nonempty ((Ev l E c.Z n).obj
          ((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
            (pull l E base (o.geometry c.g)).obj B)) ≅
        DerivedCategory.Q.obj
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (ProEt.topology c.Z)
            (SpTowerShriek.B l E c.Z n)).obj
            ((levelOpenComplex l E base c.i n).obj T,
              ((proEtaleConstantRingPullback (R l E n) c.g).mapHomologicalComplex
                (.up ℤ)).obj P)))) ∧
    (∀ (C' : D l E X) (B' : D l E Y) (h : C ⟶ C') (k : B ⟶ B'),
      (source l E base o c).map (Prod.mkHom h k) ≫ properMap l E base o c C' B' =
        properMap l E base o c C B ≫ (middle l E base o c).map (Prod.mkHom h k) ∧
      (openSource l E base o c).map (Prod.mkHom h k) ≫ openMap l E base o c C' B' =
        openMap l E base o c C B ≫ (middle l E base o c).map (Prod.mkHom h k)) ∧
    (∀ (C' : D l E X) (B' : D l E Y) (h : C ⟶ C') (k : B ⟶ B'),
      (openD l E base (o.openOp c.i)).map
          ((tensor l E base X).map (Prod.mkHom h
            ((pull l E base (o.geometry c.i)).map
              ((pull l E base (o.geometry c.g)).map k)))) ≫
          (o.openTensor c.i C' ((pull l E base (o.geometry c.g)).obj B')).inv =
        (o.openTensor c.i C ((pull l E base (o.geometry c.g)).obj B)).inv ≫
          (tensor l E base c.Z).map
            (Prod.mkHom ((openD l E base (o.openOp c.i)).map h)
              ((pull l E base (o.geometry c.g)).map k))) ∧
    (∀ n : ℕ,
      (Ev l E Y n).map (properMap l E base o c C B) ≫
          ((o.geometry c.g).pushEvaluation n).hom.app
            ((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
              (pull l E base (o.geometry c.g)).obj B)) ≫
          (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor.map
            (((base.calculus c.Z).tensorEvaluation n).hom.app
                ((openD l E base (o.openOp c.i)).obj C,
                  (pull l E base (o.geometry c.g)).obj B) ≫
              (levelTensor l E base c.Z n).map (Prod.mkHom (𝟙 _)
                (((o.geometry c.g).pullEvaluation n).hom.app B))) =
        ((base.calculus Y).tensorEvaluation n).hom.app ((F l E base o c).obj C, B) ≫
          (levelTensor l E base Y n).map
            (Prod.mkHom (((o.geometry c.g).pushEvaluation n).hom.app
              ((openD l E base (o.openOp c.i)).obj C)) (𝟙 _)) ≫
          finiteProperMap l E base (o.geometry c.g) n
            ((openD l E base (o.openOp c.i)).obj C) B) ∧
    (∀ n : ℕ,
      (Ev l E c.Z n).map ((o.openTensor c.i C ((pull l E base (o.geometry c.g)).obj B)).inv) ≫
          ((base.calculus c.Z).tensorEvaluation n).hom.app
            ((openD l E base (o.openOp c.i)).obj C, ((pull l E base (o.geometry c.g)).obj B)) ≫
          (levelTensor l E base c.Z n).map
            (Prod.mkHom ((openEvaluation l E base (o.openOp c.i) n).hom.app C) (𝟙 _)) =
        (openEvaluation l E base (o.openOp c.i) n).hom.app
            ((tensor l E base X).obj
              (C, (pull l E base (o.geometry c.i)).obj
                ((pull l E base (o.geometry c.g)).obj B))) ≫
          (sfIntrinsicDerivedOpen (R l E n) c.i).map
            (((base.calculus X).tensorEvaluation n).hom.app
                (C, (pull l E base (o.geometry c.i)).obj ((pull l E base (o.geometry c.g)).obj B)) ≫
              (levelTensor l E base X n).map (Prod.mkHom (𝟙 _)
                (((o.geometry c.i).pullEvaluation n).hom.app
                  ((pull l E base (o.geometry c.g)).obj B)))) ≫
          finiteOpenMap l E base o c.i n C ((pull l E base (o.geometry c.g)).obj B)) ∧
    (∀ n : ℕ,
      (Ev l E Y n).map (openMap l E base o c C B) ≫
          ((o.geometry c.g).pushEvaluation n).hom.app
            ((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
              (pull l E base (o.geometry c.g)).obj B)) =
        ((o.geometry c.g).pushEvaluation n).hom.app
            ((openD l E base (o.openOp c.i)).obj
              ((tensor l E base X).obj
                (C, (pull l E base (o.geometry c.i)).obj
                  ((pull l E base (o.geometry c.g)).obj B)))) ≫
          (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor.map
            ((Ev l E c.Z n).map
              ((o.openTensor c.i C ((pull l E base (o.geometry c.g)).obj B)).inv))) := by
  have models : (∀ n : ℕ, ∃ T : CochainComplex
        (SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology X) (SpTowerShriek.B l E X n)) ℤ,
      ∃ P : CochainComplex
        (SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology Y) (SpTowerShriek.B l E Y n)) ℤ,
      (∀ i : ℤ, i < a ∨ b < i → IsZero (T.X i)) ∧
      (∀ i : ℤ, i < v ∨ w < i → IsZero (P.X i)) ∧
      SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (ProEt.topology Y) (SpTowerShriek.B l E Y n) P ∧
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P ∧
      Nonempty ((Ev l E X n).obj C ≅ DerivedCategory.Q.obj T) ∧
      Nonempty ((Ev l E Y n).obj B ≅ DerivedCategory.Q.obj P) ∧
      Nonempty ((Ev l E X n).obj
          ((tensor l E base X).obj (C, (pull l E base (o.geometry f)).obj B)) ≅
        DerivedCategory.Q.obj
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (ProEt.topology X)
            (SpTowerShriek.B l E X n)).obj
            (T, ((proEtaleConstantRingPullback (R l E n) f).mapHomologicalComplex
              (.up ℤ)).obj P))) ∧
      Nonempty ((Ev l E c.Z n).obj
          ((tensor l E base c.Z).obj ((openD l E base (o.openOp c.i)).obj C,
            (pull l E base (o.geometry c.g)).obj B)) ≅
        DerivedCategory.Q.obj
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (ProEt.topology c.Z)
            (SpTowerShriek.B l E c.Z n)).obj
            ((levelOpenComplex l E base c.i n).obj T,
              ((proEtaleConstantRingPullback (R l E n) c.g).mapHomologicalComplex
                (.up ℤ)).obj P)))) := by
    intro n
    have := (_hC n).1
    have := (_hC n).2
    obtain ⟨T, hTa, hTb, ⟨eT⟩⟩ :=
      DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE ((Ev l E X n).obj C) a b
    obtain ⟨P, hP, hf, hk, ⟨eP⟩⟩ :=
      level_flat_model Y (SpTowerShriek.B l E Y n) ((Ev l E Y n).obj B) v w (_hB n)
    have hT : ∀ i : ℤ, i < a ∨ b < i → IsZero (T.X i) := by
      intro i hi
      rcases hi with hi | hi
      · exact T.isZero_of_isStrictlyGE a i hi
      · exact T.isZero_of_isStrictlyLE b i hi
    let := base.finite n
    let := sfIntrinsicExtensionByZero_additive c.i (R l E n)
    let := sfIntrinsicExtensionByZero_preservesFiniteLimits c.i (R l E n)
    let := sfIntrinsicExtensionByZero_preservesFiniteColimits c.i (R l E n)
    let eOpen : (Ev l E c.Z n).obj ((openD l E base (o.openOp c.i)).obj C) ≅
        DerivedCategory.Q.obj ((levelOpenComplex l E base c.i n).obj T) :=
      (openEvaluation l E base (o.openOp c.i) n).app C ≪≫
        (sfIntrinsicDerivedOpen (R l E n) c.i).mapIso eT ≪≫
          (Functor.mapDerivedCategoryFactors
            (sfIntrinsicExtensionByZero c.i (R l E n))).app T
    exact ⟨T, P, hT, hP, hf, hk, ⟨eT⟩, ⟨eP⟩,
      ⟨tensor_level_iso l E base o f C B n T P hk hf eT eP⟩,
      ⟨tensor_level_iso l E base o c.g _ B n
        ((levelOpenComplex l E base c.i n).obj T) P hk hf eOpen eP⟩⟩
  have hCa := isGE_of_levels l E base X C a (fun n ↦ (_hC n).1)
  have hBa : B.IsGE v := by
    apply isGE_of_levels l E base Y
    intro n
    obtain ⟨T, P, hT, hP, hf, hk, eT, ⟨eP⟩, et, eo⟩ := models n
    exact (bounds_of_model Y _ _ P v w hP eP).1
  have hOpen : ((openD l E base (o.openOp c.i)).obj C).IsGE a := by
    have := hCa
    exact (o.openOp c.i).extension.isGE_mapDerivedCategory_obj C a
  have ht (n : ℕ) :
      ((Ev l E X n).obj ((tensor l E base X).obj
        (C, (pull l E base (o.geometry f)).obj B))).IsGE (a + v) ∧
      ((Ev l E X n).obj ((tensor l E base X).obj
        (C, (pull l E base (o.geometry f)).obj B))).IsLE (b + w) := by
    obtain ⟨T, P, hT, hP, hf, hk, eT, eP, ⟨et⟩, eo⟩ := models n
    have hp (i : ℤ) (hi : i < v ∨ w < i) :
        IsZero ((((proEtaleConstantRingPullback (R l E n) f).mapHomologicalComplex
          (.up ℤ)).obj P).X i) :=
      (proEtaleConstantRingPullback (R l E n) f).map_isZero (hP i hi)
    exact bounds_of_model X _ _ _ (a + v) (b + w)
      (total_support X _ T _ a b v w hT hp) et
  have ho (n : ℕ) :
      ((Ev l E c.Z n).obj ((tensor l E base c.Z).obj
        ((openD l E base (o.openOp c.i)).obj C,
          (pull l E base (o.geometry c.g)).obj B))).IsGE (a + v) ∧
      ((Ev l E c.Z n).obj ((tensor l E base c.Z).obj
        ((openD l E base (o.openOp c.i)).obj C,
          (pull l E base (o.geometry c.g)).obj B))).IsLE (b + w) := by
    obtain ⟨T, P, hT, hP, hf, hk, eT, eP, et, ⟨eo⟩⟩ := models n
    let := base.finite n
    let := sfIntrinsicExtensionByZero_additive c.i (R l E n)
    have hj (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero (((levelOpenComplex l E base c.i n).obj T).X i) :=
      (sfIntrinsicExtensionByZero c.i (R l E n)).map_isZero (hT i hi)
    have hp (i : ℤ) (hi : i < v ∨ w < i) :
        IsZero ((((proEtaleConstantRingPullback (R l E n) c.g).mapHomologicalComplex
          (.up ℤ)).obj P).X i) :=
      (proEtaleConstantRingPullback (R l E n) c.g).map_isZero (hP i hi)
    exact bounds_of_model c.Z _ _ _ (a + v) (b + w)
      (total_support c.Z _ _ _ a b v w hj hp) eo
  refine ⟨hCa, hBa, hOpen,
    ⟨isGE_of_levels l E base X _ _ (fun n ↦ (ht n).1),
      isLE_of_levels l E base X _ _ (fun n ↦ (ht n).2)⟩,
    ⟨isGE_of_levels l E base c.Z _ _ (fun n ↦ (ho n).1),
      isLE_of_levels l E base c.Z _ _ (fun n ↦ (ho n).2)⟩,
    models, ?_, ?_, ?_, ?_, ?_⟩
  · intro C' B' h k
    exact maps_natural l E base o c h k
  · intro C' B' h k
    exact openTensor_inv_natural l E base o c.i h ((pull l E base (o.geometry c.g)).map k)
  · intro n
    exact properMap_evaluation l E base o c n C B
  · intro n
    exact openMap_evaluation l E base o c.i n C ((pull l E base (o.geometry c.g)).obj B)
  · intro n
    exact ((o.geometry c.g).pushEvaluation n).hom.naturality
      ((o.openTensor c.i C ((pull l E base (o.geometry c.g)).obj B)).inv)

end AlgebraicGeometry.ProEtale.SpTowerProjection
