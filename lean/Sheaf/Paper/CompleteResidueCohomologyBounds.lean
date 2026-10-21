/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.IntegralReductionSuccessorTriangle
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic

/-! # Cohomological bounds from complete residue Tor amplitude

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1) and (2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

The completion is the inverse limit of constant quotient ring sheaves, not the
constant sheaf of the valuation ring. Level zero of the reduction API means the
positive exponent one, hence the residue field. No characteristic, constructibility,
or local constancy condition is imposed.
-/

@[expose] public section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] integralOperationsAbLocallyBijective integralOperationsAbSheafify
  integralOperationsCommHasDerivedCategory
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  integralReductionSiteEssentiallySmall
  integralReductionSourceHasDerivedCategory integralReductionTargetHasDerivedCategory
  integralCompletedRingHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralTowerHasDerivedCategory

attribute [local instance 5000] HasDerivedCategory.standard

private noncomputable local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

private local instance fixedSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence

private theorem map_transition
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (F : ℕᵒᵖ ⥤ DerivedCategory C)
    [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    [HasCountableProducts C]
    (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).map
        (towerTransitionEndomorphism (fun n ↦ F.map (homOfLE n.le_succ).op)) ≫
        piComparison (DerivedCategory.homologyFunctor C q) (fun n : ℕ ↦ F.obj (op n)) =
      piComparison (DerivedCategory.homologyFunctor C q) (fun n : ℕ ↦ F.obj (op n)) ≫
        towerTransitionEndomorphism
          (fun n ↦ (DerivedCategory.homologyFunctor C q).map
            (F.map (homOfLE n.le_succ).op)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_π, Functor.map_sub, Functor.map_comp,
    Preadditive.comp_sub, Category.assoc, piComparison_comp_π,
    piComparison_comp_π_assoc]

private theorem derivedLimit_degree_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [HasCountableProducts C]
    (F : ℕᵒᵖ ⥤ DerivedCategory C)
    [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (K : DerivedCategory C)
    (p : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op) K p δ)
    (j : ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C j)]
    [PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C (j - 1))]
    (hz : ∀ n : ℕ, IsZero ((DerivedCategory.homologyFunctor C j).obj (F.obj (op n))))
    (he : Epi (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (DerivedCategory.homologyFunctor C (j - 1)).obj (F.obj (op n)))
      (fun n ↦ (DerivedCategory.homologyFunctor C (j - 1)).map
        (F.map (homOfLE n.le_succ).op)))) :
    IsZero ((DerivedCategory.homologyFunctor C j).obj K) := by
  let T := Triangle.mk p
    (towerTransitionEndomorphism (fun n ↦ F.map (homOfLE n.le_succ).op)) δ
  have hprod : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₂) := by
    apply IsZero.of_iso _ (asIso (piComparison (DerivedCategory.homologyFunctor C j)
      (fun n : ℕ ↦ F.obj (op n))))
    apply (limit.isLimit _).isZero_pt
    exact Functor.isZero _ (fun n ↦ hz n.as)
  have he' : Epi ((DerivedCategory.homologyFunctor C (j - 1)).map T.mor₂) := by
    have := he
    have h : Epi ((DerivedCategory.homologyFunctor C (j - 1)).map T.mor₂ ≫
        piComparison (DerivedCategory.homologyFunctor C (j - 1))
          (fun n : ℕ ↦ F.obj (op n))) := by
      rw [show (DerivedCategory.homologyFunctor C (j - 1)).map T.mor₂ ≫ _ = _ from
        map_transition F (j - 1)]
      infer_instance
    exact (epi_comp_iff_of_isIso _
      (piComparison (DerivedCategory.homologyFunctor C (j - 1))
        (fun n : ℕ ↦ F.obj (op n)))).1 h
  have hδ : DerivedCategory.HomologySequence.δ T (j - 1) j (by omega) = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT
      (j - 1) j (by omega)).1 he'
  exact (DerivedCategory.HomologySequence.exact₁ T hT (j - 1) j (by omega)).isZero_X₂
    hδ (hprod.eq_of_tgt _ _)

private theorem derivedLimit_bounds
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [HasCountableProducts C]
    (F : ℕᵒᵖ ⥤ DerivedCategory C)
    [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (K : DerivedCategory C)
    (p : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op) K p δ)
    (a b : ℤ) (_hab : a ≤ b)
    (hz : ∀ n j, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor C j).obj (F.obj (op n))))
    (htop : ∀ n : ℕ, Epi ((DerivedCategory.homologyFunctor C b).map
      (F.map (homOfLE n.le_succ).op)))
    (hprod : ∀ j, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j))
    (hroos : ∀ M : ℕᵒᵖ ⥤ C, (∀ n : ℕ, Epi (M.map (homOfLE n.le_succ).op)) →
      Epi (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ M.obj (op n))
        (fun n : ℕ ↦ M.map (homOfLE n.le_succ).op))) :
    ∀ j, j < a ∨ b < j → IsZero ((DerivedCategory.homologyFunctor C j).obj K) := by
  intro j hj
  let := hprod j
  let := hprod (j - 1)
  apply derivedLimit_degree_zero F K p δ hT j (fun n ↦ hz n j hj)
  apply hroos (F ⋙ DerivedCategory.homologyFunctor C (j - 1))
  intro n
  change Epi ((DerivedCategory.homologyFunctor C (j - 1)).map
    (F.map (homOfLE n.le_succ).op))
  by_cases he : j - 1 = b
  · exact he.symm ▸ htop n
  · exact (hz n (j - 1) (by omega)).epi _

private theorem tor_bounds (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) (j : ℤ) (hj : j < a ∨ b < j) :
    IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules X
      (proEtaleConstantRing X A)) j).obj K) := by
  classical
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  let := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have (M : C) : (tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent R M
  have (M : C) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  have : MonoidalPreadditive C :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) L
  have hP' : CochainComplex.IsAcyclicTensorKFlat (R := R) P := hP
  have hz := h.2 L P ⟨e⟩ f hf hP' (𝟙_ C) j hj
  have : QuasiIso f := hf
  let d : derivedTensor X A L
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (𝟙_ C)) P f hf hP' ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  exact hz.of_iso ((DerivedCategory.homologyFunctor C j).mapIso d).symm

/-- A derived-complete complex has the same cohomological bounds as a Tor interval
of its residue reduction, tested after restriction to every small-site object.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1),(2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

Proof:
1. Test residue Tor amplitude with the coefficient sheaf itself on X. The tensor
unit identity gives vanishing of residue cohomology outside [a,b].
2. Choose one flat-term K-flat resolution P by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings its reductions compute every K_n. Their actual
chain maps 1_P tensor (C_(n+1) to C_n) give the canonical quotient transitions.
3. The DVR coefficient sequence 0 to k_X to C_(n+1) to C_n to 0 is short exact:
the first map sends r to varpi^n r; cancellation proves injectivity and identifies
its image with the quotient kernel. Surjectivity and these identities pass to
constant sheaves locally. Compatibility of the limit projections makes the maps
B_X-linear (def-weil-l-adic-coefficient-extension, def-weil-pbc-constant-sheaf).
4. Flatness of each term of P preserves this exact sequence
(def-pc-flat-sheaf-modules). Apply lem-weil-pbc-complex-ses-triangle and
lem-sf-derived-homology-long-exact to obtain the cohomology exact sequences.
5. Induction gives cohomology in [a,b] for all K_n. The exact sequence in degree b
also makes each canonical transition on H^b epimorphic.
6. Apply det-pe-milnor-sequence to this strict tower. By det-pe-products-derived,
its termwise product represents the product in D(Mod(B_X)), and localization
identifies 1-T with the tower transition endomorphism. Rotating the cone triangle
gives a Roos triangle (def-weil-abstract-derived-category,
def-weil-triangulated-category, def-weil-derived-limit). Completeness and the
uniqueness clause of lem-weil-derived-limit-existence identify K up to isomorphism
with this Milnor middle term.
7. For j<a and j>b+1 both outer Milnor terms vanish. At j=b+1, the right term is
zero and det-pe-milnor-epimorphic kills R^1 lim H^b(K_n), since its transitions are
epimorphic. Exactness gives the asserted vanishing in every remaining degree. -/
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K) := by
  classical
  let C := integralTowerModules.{u, u} l E X
  let R := completedIntegralCoefficientSheafUnrestricted.{u, u} l E X
  let : HasDerivedCategory C := integralTowerHasDerivedCategory.{u, u} l E X
  let A := Padic.coefficientExtensionRing l E 1
  let : Finite A := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  have ht := _hTor (ProEt.mk (𝟙 X))
  change HasProEtaleTorAmplitude X A
    ((proEtaleConstantRingDerivedPullback A (𝟙 X)).obj
      ((scalarReductionDerivedExtension l E X 0).obj K)) a b at ht
  obtain ⟨_, _, _, _, _, _, _, _, _, _, γ, _⟩ := proEtaleDerivedPullback_identity X A
  have hres (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules X
        (proEtaleConstantRing X A)) j).obj
        ((scalarReductionDerivedExtension l E X 0).obj K)) := by
    exact (tor_bounds X A _ a b ht j hj).of_iso
      ((DerivedCategory.homologyFunctor _ j).mapIso (γ.app _)).symm
  obtain ⟨D, hl, P, G, q, hq, e, hprod, δ, hδ⟩ := _hcomplete
  let F : ℕᵒᵖ ⥤ DerivedCategory C := integralReductionTower.{0, u, u} l E X D hl P
  let := hprod
  have hbase (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((DerivedCategory.homologyFunctor C j).obj
        (F.obj (op 0))) := by
    let d := (scalarReductionDerivedExtension l E X 0).mapIso e.symm ≪≫
      unrestrictedTowerResolutionIso.{u, u} l E X 0 q hq
    have hz := (hres j hj).of_iso ((DerivedCategory.homologyFunctor _ j).mapIso d).symm
    have hz' := (scalarReductionRestriction l E X 0).isZero_homologyFunctor_mapDerivedCategory_obj
      hz
    exact hz'.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      ((scalarReductionRestriction l E X 0).mapDerivedCategoryFactors.app _)).symm
  have htri (n : ℕ) :
      ∃ (ι : F.obj (op 0) ⟶ F.obj (op (n + 1)))
        (d : F.obj (op n) ⟶ (F.obj (op 0))⟦(1 : ℤ)⟧),
        Triangle.mk ι (F.map (homOfLE n.le_succ).op) d ∈ distTriang (DerivedCategory C) := by
    exact integralReduction_successor_triangle l E X D hl P hq.2 n
  have hall (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((DerivedCategory.homologyFunctor C j).obj
        (F.obj (op n))) := by
    induction n with
    | zero => exact hbase j hj
    | succ n ih =>
      obtain ⟨ι, d, hd⟩ := htri n
      exact (DerivedCategory.HomologySequence.exact₂ (Triangle.mk ι _ d) hd j).isZero_X₂
        ((hbase j hj).eq_of_src _ _) (ih.eq_of_tgt _ _)
  have hepi (n : ℕ) :
      Epi ((DerivedCategory.homologyFunctor C b).map
        (F.map (homOfLE n.le_succ).op)) := by
    obtain ⟨ι, d, hd⟩ := htri n
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      (Triangle.mk ι _ d) hd b (b + 1) (by omega)).2
      ((hbase (b + 1) (Or.inr (by omega))).eq_of_tgt _ _)
  have : HasExactLimitsOfShape (Discrete ℕ) C := ProEt.products_exact.{u, u + 1} X R ℕ
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have : CountableAB4Star C := CountableAB4Star.of_hasExactLimitsOfShape_nat C
  obtain ⟨hproducts, _, hhomology, _⟩ := derivedCategory_countableProducts_and_towerLimit C
  apply derivedLimit_bounds F K _ δ hδ a b _hab hall hepi (hhomology ℕ)
  intro M hm
  exact (AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, u} X R M hm).1

end WeilConjectures
