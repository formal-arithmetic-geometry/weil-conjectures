/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefTowerCoaugmentation
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComparisonRealization
public import WeilConjectures.AlgebraicGeometry.InverseImagePullbackComparisonDerived
public import WeilConjectures.TraceFormula.PointTransportComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.PointIntegralRestrictionNatural
import WeilConjectures.AlgebraicGeometry.ExactProductTowerLimitMate
import WeilConjectures.AlgebraicGeometry.IntegralTowerInverseImageUnit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExact
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.AlgebraicGeometry.IsomorphismScalarQuotientChainSquares

/-!
# Normalized comparisons for integral coefficient systems

Source: Weil blueprint, main-20261015, `sec-trace-formula/sk-d-weil`,
`prop-trf-rational-frobenius-integral-model.proof.md`, prerequisite to clause (3)
(blueprint: lem-trf-integral-point-transport-tower-powers).

The definitions below specify the strict-system map before localization, its naturality
and power law, and the normalized comparison with the completed integral realization.

The comparison declarations are kept in a separate compilation unit so the
completed coefficient actions are checked independently of the realization laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.pointReductionModuleDerived
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

private theorem equivMate_isIso
    {C B : Type*} [Category C] [Category B] {K : C ⥤ B} {R : B ⥤ C}
    (adj : K ⊣ R) (F : C ⥤ C) (G : B ⥤ B) [F.IsEquivalence] [G.IsEquivalence]
    (e : F ⋙ K ≅ K ⋙ G) :
    IsIso (mateEquiv adj adj e.hom).natTrans := by
  let a := (mateEquiv adj adj e.hom).natTrans
  have ha (Y : B) : K.map (a.app Y) ≫ adj.counit.app (G.obj Y) =
      e.hom.app (R.obj Y) ≫ G.map (adj.counit.app Y) :=
    mateEquiv_counit adj adj e.hom Y
  have hb (X : C) (Y : B) :
      Function.Bijective (fun f : F.obj X ⟶ F.obj (R.obj Y) ↦ f ≫ a.app Y) := by
    let q := (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
      ((adj.homEquiv X Y).symm.trans
        ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.trans
          ((Iso.homCongr (e.app X).symm (Iso.refl (G.obj Y))).trans
            (adj.homEquiv (F.obj X) (G.obj Y)))))
    have hq (f : F.obj X ⟶ F.obj (R.obj Y)) : q f = f ≫ a.app Y := by
      apply (adj.homEquiv _ _).symm.injective
      dsimp only [q, Equiv.trans_apply]
      erw [Equiv.symm_apply_apply]
      simp only [Iso.homCongr, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
      change e.hom.app X ≫ G.map ((adj.homEquiv X Y).symm (F.preimage f)) =
        (adj.homEquiv _ _).symm (f ≫ a.app Y)
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, ha, ← Category.assoc]
      have he := e.hom.naturality (F.preimage f)
      dsimp only [Functor.comp_map] at he
      rw [Functor.map_preimage] at he
      rw [← he]
      simp only [Category.assoc]
    constructor
    · intro f g hfg
      apply q.injective
      rw [hq, hq]
      exact hfg
    · intro g
      obtain ⟨f, hf⟩ := q.surjective g
      exact ⟨f, (hq f).symm.trans hf⟩
  have h (Y : B) : IsIso (a.app Y) := by
    apply isIso_of_yoneda_map_bijective
    intro Z
    let i := F.objObjPreimageIso Z
    have hZ := hb (F.objPreimage Z) Y
    constructor
    · intro f g hfg
      apply (cancel_epi i.hom).1
      apply hZ.1
      simpa only [Category.assoc] using congrArg (i.hom ≫ ·) hfg
    · intro f
      obtain ⟨g, hg⟩ := hZ.2 (i.hom ≫ f)
      refine ⟨i.inv ≫ g, ?_⟩
      change (i.inv ≫ g) ≫ a.app Y = f
      change g ≫ a.app Y = i.hom ≫ f at hg
      rw [Category.assoc, hg, Iso.inv_hom_id_assoc]
  exact NatIso.isIso_of_isIso_app a

namespace IntegralPointTransportTower

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded constant-tower functor in the point-fibre derived presentation.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev moduleConstant :=
  @CoefTower.constant (CoefTower.coefficient l E) _ (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The recorded total limit, with the same point-fibre derived presentation.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev moduleLimit :=
  @CoefTower.totalLimit (CoefTower.coefficient l E) _ (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The specified derived constant/total-limit adjunction in that presentation.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev moduleAdjunction :=
  @CoefTower.adjunction (CoefTower.coefficient l E) _ (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- Evaluation in the same point-fibre presentation of derived R-modules.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev moduleEvaluation (n : ℕ) :=
  @CoefTower.evaluate (CoefTower.coefficient l E) _ (HasDerivedCategory.ofIsGrothendieckAbelian _) n

/-- The exact tensor model of termwise inverse image, identified with inverse image by j_r.
Source: blueprint clause (3), proof steps 1--3
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev ordinaryPullback (r : ℕ) :=
  integralComparisonSequencePullback l E ((pointFrobeniusAut D) ^ r).hom

/-- Exact termwise inverse image on the derived category of entire semilinear systems.
Source: blueprint clause (3), proof steps 1--3
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev pullback (r : ℕ) :=
  integralComparisonDerivedSequencePullback l E ((pointFrobeniusAut D) ^ r).hom

/-- Restriction of coefficients followed by exact sections, with the original transitions.
Source: blueprint clause (3), proof steps 2--3; the module-valued refinement of
coefficientTowerSections is CoefTower.towerSections
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev ordinarySections :=
  coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙ CoefTower.towerSections D l E

/-- Gamma_bullet takes values in the derived category of strict R-module towers.
Source: blueprint clause (3), proof step 3
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev sections :=
  coefficientSequenceDerivedRestriction l E (Spec (.of D.k)) ⋙ CoefTower.derivedTowerSections D l E

/-- The canonical exact-functor composition comparison. Source: blueprint proof step 3
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def sectionsFactors : (ordinarySections D l E).mapDerivedCategory ≅ sections D l E :=
  Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E (Spec (.of D.k)))
    (CoefTower.towerSections D l E)

/-- Read an actual system section in its restricted point module; scalar restriction
changes only the action. Source: blueprint clause (3), proof step 2
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def systemSection (M : coefficientSequenceModules l E (Spec (.of D.k))) (n : ℕ)
    (x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((ordinarySections D l E).obj M).obj (op n) :=
  integralComparisonRestrictedSection l E (Spec (.of D.k)) M n
    (op (ProEt.mk (𝟙 (Spec (.of D.k))))) x

/-- The defining restriction, colimit insertion, sheafification and tensor-unit formula.
The generator is the actual unit of the recorded system pullback adjunction.
Source: blueprint clause (3), proof steps 1--2
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def sectionTransport (r : ℕ) (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (n : ℕ) (x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((ordinarySections D l E).obj ((ordinaryPullback D l E r).obj M)).obj (op n) :=
  systemSection D l E ((ordinaryPullback D l E r).obj M) n
    (((ordinaryPullback D l E r).obj M).val.map
      (CategoryTheory.Prod.mkHom (𝟙 n)
        (proEtaleIsoCommaArrow ((pointFrobeniusAut D) ^ r).hom
          (ProEt.mk (𝟙 (Spec (.of D.k)))))).op
      (integralComparisonSequenceGenerator l E ((pointFrobeniusAut D) ^ r).hom M n
        ((proEtaleIsoPostcompose ((pointFrobeniusAut D) ^ r).hom).obj
          (ProEt.mk (𝟙 (Spec (.of D.k)))))
        (M.val.map (CategoryTheory.Prod.mkHom (𝟙 n) (pointPowerRestriction D r)).op x)))

/-- The power equality in the automorphism group, with the source convention h then h^m.
Source: blueprint clause (3), proof step 4
(blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: composition of the powers is their (m+1)-st power, by the multiplication law
in Aut and the usual power recursion. -/
theorem powerHom (m : ℕ) :
    (pointFrobeniusAut D).hom ≫ ((pointFrobeniusAut D) ^ m).hom =
      ((pointFrobeniusAut D) ^ (m + 1)).hom := by
  rw [pow_succ]
  exact rfl

/-- t_m is the inverse of the recorded strict-system compositor, with the power equality.
Source: blueprint clause (3), proof step 4
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def compositor (m : ℕ) : pullback D l E m ⋙ pullback D l E 1 ≅ pullback D l E (m + 1) :=
  (integralComparisonSystemComposition l E (pointFrobeniusAut D).hom
    ((pointFrobeniusAut D) ^ m).hom).symm ≪≫
    eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) (powerHom D m))

/-- Exact inverse image on completed-module towers, retaining their transitions.
Source: blueprint proof steps 1 and 5
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev ordinaryInverseTower (r : ℕ) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom)

/-- Exactness of inverse image on the tower category.
Source: blueprint proof steps 1 and 5
(blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: inverse image along an isomorphism is an exact equivalence; finite limits
and colimits of strict towers are computed componentwise. -/
theorem inverseTower_exact (r : ℕ) :
    (ordinaryInverseTower D l E r).Additive ∧
      PreservesFiniteLimits (ordinaryInverseTower D l E r) ∧
      PreservesFiniteColimits (ordinaryInverseTower D l E r) := by
  exact ⟨inferInstance, ⟨fun _ _ _ ↦ inferInstance⟩, ⟨fun _ _ _ ↦ inferInstance⟩⟩

/-- The exactness instances are the preceding componentwise assertion.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance inverseTowerAdditive (r : ℕ) : (ordinaryInverseTower D l E r).Additive :=
  (inverseTower_exact D l E r).1

/-- Finite limits are preserved componentwise.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance inverseTowerLimits (r : ℕ) : PreservesFiniteLimits (ordinaryInverseTower D l E r) :=
  (inverseTower_exact D l E r).2.1

/-- Finite colimits are preserved componentwise.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance inverseTowerColimits (r : ℕ) : PreservesFiniteColimits (ordinaryInverseTower D l E r) :=
  (inverseTower_exact D l E r).2.2

/-- Exact termwise inverse image localized on the whole tower category.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev inverseTower (r : ℕ) := (ordinaryInverseTower D l E r).mapDerivedCategory

/-- j_r after restriction of scalars, fixed at every site object by x tensor 1.
Source: blueprint proof steps 1--2 and 5
(blueprint: lem-trf-integral-point-restriction-comparison).
Proof: the coefficient square pi_n c = c_n F(pi_n) makes the finite tensor-unit
isomorphisms completed-linear. Their balancing inverses commute with all actual
quotient transitions. The generator formula below determines each section map,
so also determines the natural isomorphism uniquely. -/
theorem restrictionComparison_existsUnique (r : ℕ) :
    ∃! j : coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙ ordinaryInverseTower D l E r ≅
        ordinaryPullback D l E r ⋙ coefficientSequenceRestriction l E (Spec (.of D.k)),
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k))) (n : ℕ) (U : (Spec (.of D.k)).ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose
          ((pointFrobeniusAut D) ^ r).hom).obj U))),
        (((j.hom.app M).app (op n)).val.app (op U))
          (integralComparisonRestrictedSection l E (Spec (.of D.k)) M n
            (op ((proEtaleIsoPostcompose ((pointFrobeniusAut D) ^ r).hom).obj U)) x) =
        integralComparisonRestrictedSection l E (Spec (.of D.k))
          ((ordinaryPullback D l E r).obj M) n (op U)
          (((ordinaryPullback D l E r).obj M).val.map
            (CategoryTheory.Prod.mkHom (𝟙 n)
              (proEtaleIsoCommaArrow ((pointFrobeniusAut D) ^ r).hom U)).op
            (integralComparisonSequenceGenerator l E ((pointFrobeniusAut D) ^ r).hom M n
              ((proEtaleIsoPostcompose ((pointFrobeniusAut D) ^ r).hom).obj U) x)) := by
  exact integralTowerInverseImageUnit_existsUnique l E ((pointFrobeniusAut D) ^ r).hom

/-- The unique tensor-unit identification, preserving all horizontal maps.
Source: blueprint proof steps 1 and 5
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def restrictionComparison (r : ℕ) := (restrictionComparison_existsUnique D l E r).exists.choose

section OrdinaryTransportProof
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted pointIntegralSectionMap constantSheaf

/-- The canonical ordinary whole-system transformation is determined on every section.
Source: blueprint clause (3), proof steps 1--3
(blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: restrictions commute with differentials, system morphisms and horizontal quotient
maps. The quotient sends 1 to 1, so the tensor units commute with the actual transitions.
The completed coefficient square proves R-linearity. Sections generate their own modules,
so the displayed formula determines every component and proves uniqueness. -/
theorem ordinaryTransport_existsUnique (r : ℕ) :
    ∃! I : ordinarySections D l E ⟶ ordinaryPullback D l E r ⋙ ordinarySections D l E,
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k))) (n : ℕ)
        (x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((I.app M).app (op n)) (systemSection D l E M n x) = sectionTransport D l E r M n x := by
  let sigmaTower := PointIntegralRestrictionNatural.sigmaTower D l E r
  let I : ordinarySections D l E ⟶ ordinaryPullback D l E r ⋙ ordinarySections D l E :=
    Functor.whiskerLeft (coefficientSequenceRestriction l E (Spec (.of D.k))) sigmaTower ≫
      Functor.whiskerRight (restrictionComparison D l E r).hom (CoefTower.towerSections D l E)
  refine ⟨I, ?_, ?_⟩
  · intro M n x
    change (((restrictionComparison D l E r).hom.app M).app (op n)).val.app
        (op (ProEt.mk (𝟙 _)))
        (((sigmaTower.app ((coefficientSequenceRestriction l E (Spec (.of D.k))).obj M)).app
          (op n)) (systemSection D l E M n x)) = _
    rw [PointIntegralRestrictionNatural.sigmaTower_app]
    unfold systemSection
    rw [PointIntegralRestrictionNatural.restriction_cast]
    exact (restrictionComparison_existsUnique D l E r).exists.choose_spec M n
      (ProEt.mk (𝟙 _)) _
  · intro I' hI'
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x₀ := cast (integralComparisonRestrictedSectionType l E (Spec (.of D.k)) M n.unop
      (op (ProEt.mk (𝟙 _)))) x
    have hx : systemSection D l E M n.unop x₀ = x := by
      simp [systemSection, integralComparisonRestrictedSection, x₀]
    rw [← hx]
    exact (hI' M n.unop x₀).trans (by
      change _ = ((I.app M).app (op n.unop)) (systemSection D l E M n.unop x₀)
      change _ = (((restrictionComparison D l E r).hom.app M).app (op n.unop)).val.app
        (op (ProEt.mk (𝟙 _)))
        (((sigmaTower.app ((coefficientSequenceRestriction l E (Spec (.of D.k))).obj M)).app
          (op n.unop)) (systemSection D l E M n.unop x₀))
      rw [PointIntegralRestrictionNatural.sigmaTower_app]
      unfold systemSection
      rw [PointIntegralRestrictionNatural.restriction_cast]
      exact ((restrictionComparison_existsUnique D l E r).exists.choose_spec M n.unop
        (ProEt.mk (𝟙 _)) _).symm)

end OrdinaryTransportProof

/-- The ordinary transformation is chosen from its unique sectionwise specification.
Source: blueprint clause (3), proof step 2
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def ordinaryTransport (r : ℕ) := (ordinaryTransport_existsUnique D l E r).exists.choose

/-- I_r is the localization of that specified transformation on whole complexes.
Source: blueprint clause (3), proof step 3
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def transport (r : ℕ) : sections D l E ⟶ pullback D l E r ⋙ sections D l E :=
  (sectionsFactors D l E).inv ≫
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E (Spec (.of D.k)))
      (ComplexShape.up ℤ)) _ _ ((ordinarySections D l E).mapDerivedCategory)
    ((ordinaryPullback D l E r ⋙ ordinarySections D l E).mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (ordinaryTransport D l E r) (ComplexShape.up ℤ))
      DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (ordinaryPullback D l E r)
      (ordinarySections D l E)).hom ≫
    Functor.whiskerLeft (pullback D l E r) (sectionsFactors D l E).hom

/-- The localization of that entire-tower identification.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def derivedRestrictionComparison (r : ℕ) :
    coefficientSequenceDerivedRestriction l E (Spec (.of D.k)) ⋙ inverseTower D l E r ≅
      pullback D l E r ⋙ coefficientSequenceDerivedRestriction l E (Spec (.of D.k)) :=
  letI := inverseTowerAdditive D l E r
  letI := inverseTowerLimits D l E r
  letI := inverseTowerColimits D l E r
  letI := integralComparisonSequencePullbackAdditive l E ((pointFrobeniusAut D) ^ r).hom
  letI := coefficientSequenceRestriction_additive l E (Spec (.of D.k))
  letI := coefficientSequenceRestriction_limits l E (Spec (.of D.k))
  letI := coefficientSequenceRestriction_colimits l E (Spec (.of D.k))
  letI := integralComparisonSequencePullbackLimits l E ((pointFrobeniusAut D) ^ r).hom
  letI := integralComparisonSequencePullbackColimits l E ((pointFrobeniusAut D) ^ r).hom
  (Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E (Spec (.of D.k)))
    (ordinaryInverseTower D l E r)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComparison D l E r) ≪≫
    Functor.mapDerivedCategoryCompIso (ordinaryPullback D l E r)
      (coefficientSequenceRestriction l E (Spec (.of D.k)))

/-- Constant towers commute with exact inverse image by the termwise identity.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def constantInverseComparison (r : ℕ) :
    inverseImageIntegralDerived l E ((pointFrobeniusAut D) ^ r).hom ⋙
        integralComparisonConstantTower l E (Spec (.of D.k)) ≅
      integralComparisonConstantTower l E (Spec (.of D.k)) ⋙ inverseTower D l E r :=
  (Functor.mapDerivedCategoryCompIso
    (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom)
    (Functor.const ℕᵒᵖ)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) (ordinaryInverseTower D l E r)

/-- Constant towers commute with exact point sections by the termwise identity.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def constantSectionsComparison :
    pointFibreIntegralAmbient D l E ⋙ moduleConstant l E ≅
      integralComparisonConstantTower l E (Spec (.of D.k)) ⋙ CoefTower.derivedTowerSections D l E :=
  (Functor.mapDerivedCategoryCompIso (pointIntegralSections l E D.k) (Functor.const ℕᵒᵖ)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ) (CoefTower.towerSections D l E)

/-- The exact inverse-image comparison is normalized by the entire derived limit cone.
The counit is the ordinary limit cone on simultaneous K-injective tower resolutions.
Source: blueprint proof steps 5--6 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: apply exact inverse image to the entire counit, use its constant-tower
identity and j_r, and transpose under the specified constant/total-limit adjunction.
This mate is invertible since inverse image is an equivalence preserving products.
The adjunction bijection proves uniqueness, without any faithfulness assumption on
individual derived evaluations. In Roos coordinates the map is diagonal on both products. -/
theorem inverseLimitComparison_existsUnique (r : ℕ) :
    ∃! a : coefficientSequenceLimit l E (Spec (.of D.k)) ⋙
        inverseImageIntegralDerived l E ((pointFrobeniusAut D) ^ r).hom ≅
      pullback D l E r ⋙ coefficientSequenceLimit l E (Spec (.of D.k)),
      ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
        (integralComparisonConstantTower l E (Spec (.of D.k))).map (a.hom.app C) ≫
            (integralComparisonTowerCounit l E (Spec (.of D.k))).app
              ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
                ((pullback D l E r).obj C)) =
          (constantInverseComparison D l E r).hom.app
              ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
            (inverseTower D l E r).map
              ((integralComparisonTowerCounit l E (Spec (.of D.k))).app
                ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C)) ≫
            (derivedRestrictionComparison D l E r).hom.app C := by
  have : (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom).IsEquivalence :=
    ScalarQuotientChain.sectionwiseModules_equivalence ((pointFrobeniusAut D) ^ r).hom
      (inverseImageCompletedCoefficientMap l E ((pointFrobeniusAut D) ^ r).hom)
  have : (ordinaryInverseTower D l E r).IsEquivalence := inferInstance
  let adj := integralComparisonConstantAdjunction l E (Spec (.of D.k))
  let F := inverseImageIntegralDerived l E ((pointFrobeniusAut D) ^ r).hom
  let G := inverseTower D l E r
  let e := constantInverseComparison D l E r
  have : IsIso (mateEquiv adj adj e.hom).natTrans := equivMate_isIso adj F G e
  let a := asIso (mateEquiv adj adj e.hom).natTrans
  let b := Functor.isoWhiskerLeft
      (coefficientSequenceDerivedRestriction l E (Spec (.of D.k))) a ≪≫
    Functor.isoWhiskerRight (derivedRestrictionComparison D l E r)
      (coefficientConstantTowerLimit l E (Spec (.of D.k)))
  have hb : ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
      (integralComparisonConstantTower l E (Spec (.of D.k))).map (b.hom.app C) ≫
          (integralComparisonTowerCounit l E (Spec (.of D.k))).app
            ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
              ((pullback D l E r).obj C)) =
        e.hom.app ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
          G.map ((integralComparisonTowerCounit l E (Spec (.of D.k))).app
            ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C)) ≫
          (derivedRestrictionComparison D l E r).hom.app C := by
    intro C
    dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [Functor.map_comp, Category.assoc]
    have hn := adj.counit.naturality ((derivedRestrictionComparison D l E r).hom.app C)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, adj] at hn
    unfold integralComparisonTowerCounit
    erw [hn]
    simpa only [a, asIso, adj, G, coefficientSequenceLimit, Functor.comp_obj,
      Category.assoc] using
      congrArg (· ≫ (derivedRestrictionComparison D l E r).hom.app C)
      (mateEquiv_counit adj adj e.hom
        ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C))
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext C
  apply (adj.homEquiv _ _).symm.injective
  change (integralComparisonConstantTower l E (Spec (.of D.k))).map (b'.hom.app C) ≫
      adj.counit.app _ =
    (integralComparisonConstantTower l E (Spec (.of D.k))).map (b.hom.app C) ≫
      adj.counit.app _
  exact (hb' C).trans (hb C).symm

/-- a_r is the uniquely normalized mate of the entire limit cone.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def inverseLimitComparison (r : ℕ) :=
  (inverseLimitComparison_existsUnique D l E r).exists.choose

/-- Sections of the total limit are normalized by the whole derived counit.
Source: blueprint proof steps 5--6 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: transpose exact sections of the entire limit-cone counit. Exact sections
preserve products, so the mate is invertible by the normalized Roos model.
The adjunction bijection proves uniqueness. Both cone summands use the canonical
product comparison; no off-diagonal component or levelwise reconstruction is used. -/
theorem sectionsLimitComparison_existsUnique :
    ∃! z : coefficientSequenceLimit l E (Spec (.of D.k)) ⋙ pointFibreIntegralAmbient D l E ≅
        sections D l E ⋙ moduleLimit l E,
      ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
        (moduleConstant l E).map (z.hom.app C) ≫
            (moduleAdjunction l E).counit.app
              ((sections D l E).obj C) =
          (constantSectionsComparison D l E).hom.app
              ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
            (CoefTower.derivedTowerSections D l E).map
              ((integralComparisonTowerCounit l E (Spec (.of D.k))).app
                ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C)) := by
  let : IsGrothendieckAbelian.{u + 1} (integralTowerModules l E (Spec (.of D.k))) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology (Spec (.of D.k)))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).1
  let : PreservesFiniteLimits (pointIntegralSections l E D.k) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _
      (ProEtale.pointModuleSections D.k (completedIntegralCommRingSheafUnrestricted l E
        (Spec (.of D.k))))
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E D.k))
      ((ProEtale.point_proEtale_sections_exact.{u,u+2,u+1} D.k).2 _).1 inferInstance
  let : PreservesFiniteColimits (pointIntegralSections l E D.k) :=
    @comp_preservesFiniteColimits _ _ _ _ _ _
      (ProEtale.pointModuleSections D.k (completedIntegralCommRingSheafUnrestricted l E
        (Spec (.of D.k))))
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E D.k))
      ((ProEtale.point_proEtale_sections_exact.{u,u+2,u+1} D.k).2 _).2.1 inferInstance
  let : PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E D.k) := by
    let U := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointIntegralSectionMap l E D.k)
    have : PreservesLimitsOfShape (Discrete ℕ) U := ⟨fun {K} ↦
      ModuleCat.preservesLimit_restrictScalars (pointIntegralSectionMap l E D.k) K⟩
    exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
      (ProEtale.pointModuleSections D.k (completedIntegralCommRingSheafUnrestricted l E
        (Spec (.of D.k)))) U inferInstance inferInstance
  let adj := moduleAdjunction l E
  let e := constantSectionsComparison D l E
  let a := (mateEquiv (integralComparisonConstantAdjunction l E (Spec (.of D.k)))
    adj e.hom).natTrans
  have : IsIso a := by
    have he : Functor.compConstIso ℕᵒᵖ (pointIntegralSections l E D.k) =
        Iso.refl (pointIntegralSections l E D.k ⋙ Functor.const ℕᵒᵖ) := by
      apply Iso.ext
      rfl
    let : HasDerivedCategory.{u + 2} (integralTowerModules l E (Spec (.of D.k))) :=
      HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (CoefTower.coefficient l E)) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ integralTowerModules l E (Spec (.of D.k))) :=
      HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (CoefTower.coefficient l E)) :=
      HasDerivedCategory.standard _
    have hid : (Functor.mapDerivedCategoryNatIso
        (Iso.refl (pointIntegralSections l E D.k ⋙ Functor.const ℕᵒᵖ))).hom = 𝟙 _ :=
      @Functor.mapDerivedCategoryNatIso_refl
        (integralTowerModules l E (Spec (.of D.k)))
        (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (CoefTower.coefficient l E)) _ _ _ _
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (pointIntegralSections l E D.k ⋙ Functor.const ℕᵒᵖ) _ _ _
    have h := exactProductTowerLimitMate_isIso.{u+2,u+1,u+2,u+1,u+2,u+1,u+2,u+2}
      (A := integralTowerModules l E (Spec (.of D.k)))
      (B := ModuleCat.{u + 1} (CoefTower.coefficient l E))
      (pointIntegralSections l E D.k)
    simp only [he, Iso.trans_hom, hid, Category.id_comp] at h
    dsimp only [a, adj, e, constantSectionsComparison, integralComparisonConstantAdjunction,
      moduleAdjunction, CoefTower.adjunction, CoefTower.derivedTowerSections,
      CoefTower.towerSections, coefficientConstantTowerLimit, coefficientSequenceRestrictedDerived,
      pointFibreIntegralAmbient, CoefTower.totalLimit]
    exact h
  let z := Functor.isoWhiskerLeft
    (coefficientSequenceDerivedRestriction l E (Spec (.of D.k))) (asIso a)
  have hz : ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
      (moduleConstant l E).map (z.hom.app C) ≫ adj.counit.app ((sections D l E).obj C) =
        e.hom.app ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
          (CoefTower.derivedTowerSections D l E).map
            ((integralComparisonTowerCounit l E (Spec (.of D.k))).app
              ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C)) := by
    intro C
    exact mateEquiv_counit (integralComparisonConstantAdjunction l E (Spec (.of D.k)))
      adj e.hom ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj C)
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  apply Iso.ext
  apply NatTrans.ext
  funext C
  apply (adj.homEquiv _ _).symm.injective
  change (moduleConstant l E).map (z'.hom.app C) ≫ adj.counit.app _ =
    (moduleConstant l E).map (z.hom.app C) ≫ adj.counit.app _
  exact (hz' C).trans (hz C).symm

/-- zeta is the inverse of the canonically normalized sections/limit mate.
Source: blueprint proof step 5 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def zeta := (sectionsLimitComparison_existsUnique D l E).exists.choose.symm

end IntegralPointTransportTower
end WeilConjectures
