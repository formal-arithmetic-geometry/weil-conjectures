/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.IntegralPointCoefficientAdjunction
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Derived sections of the regular quotient sequence at a point

Source: prop-coef-integral-dualizing, second proof paragraph; Stacks 03CW and 0941.
(blueprint: lem-coef-point-integral-regular-quotient-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev regularSequence (W : Scheme.{u}) : coefficientSequenceModules.{u, u} l E W :=
  SheafOfModules.unit.{u, u + 1, u + 1}
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E W))

private def regularSections (W : Scheme.{u}) : coefPairingModules l E :=
  (coefHomTowerSections l E W).obj
    ((coefficientSequenceRestriction l E W).obj (regularSequence l E W))

private def regularSectionValue (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (n : ℕ) :
    coefTraceQuotientModule l E n ⟶
      (coefHomSections l E (Spec (.of D.k))).obj
        ((scalarReductionRestriction l E (Spec (.of D.k)) n).obj
          ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj
            (regularSequence l E (Spec (.of D.k))))) := by
  let W := Spec (.of D.k)
  refine ConcreteCategory.ofHom (C := ModuleCat (coefTraceRing l E)) ?_
  refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }
  · intro x
    exact IntegralPointCoefficientAdjunction.finiteValue D.k l E n x
  · intro x y
    exact map_add _ x y
  · intro r x
    change finiteDualizingCoeff l E n at x
    let V := op (PointDerivedHom.finalObject D.k)
    have heq : ((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app V) =
        𝟙 ((integralCoefficientSheaf l E W n).obj.obj V) := by
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change IntegralPointCoefficientAdjunction.finiteValue D.k l E n
        (coefTraceQuotient l E n r * x) =
      @HMul.hMul ((integralCoefficientSheaf l E W n).obj.obj V)
        ((integralCoefficientSheaf l E W n).obj.obj V)
        ((integralCoefficientSheaf l E W n).obj.obj V) _
      (((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app V).hom
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V
          (coefHomScalar l E W r)) :
          (integralCoefficientSheaf l E W n).obj.obj V)
        (IntegralPointCoefficientAdjunction.finiteValue D.k l E n x)
    rw [heq]
    change IntegralPointCoefficientAdjunction.finiteValue D.k l E n
        (coefTraceQuotient l E n r * x) =
      @HMul.hMul ((integralCoefficientSheaf l E W n).obj.obj V)
        ((integralCoefficientSheaf l E W n).obj.obj V)
        ((integralCoefficientSheaf l E W n).obj.obj V) _
        ((completedIntegralCoefficientProjection l E W D hl n).hom.app V
          (PointDerivedHom.scalar D.k (IntegralPointCoefficientAdjunction.B D.k l E)
            (IntegralPointCoefficientAdjunction.alpha D.k l E) V r))
        (IntegralPointCoefficientAdjunction.finiteValue D.k l E n x)
    have hs := IntegralPointCoefficientAdjunction.integral_point_coefficient_adjunction l E D hl
    rw [hs.2.2.2.2.2.1]
    exact map_mul _ _ _

private def regularSectionComponent (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (n : ℕ) :
    coefTraceQuotientModule l E n ⟶ (regularSections l E (Spec (.of D.k))).obj (op n) :=
  regularSectionValue l E D hl n ≫
    ((coefHomSections l E (Spec (.of D.k))).mapIso
      (eqToIso ((coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec.1
        (regularSequence l E (Spec (.of D.k))) n))).inv

private theorem sectionCast (W : Scheme.{u}) (M N : scalarReductionSource l E W)
    (h : M = N) (x : (coefHomSections l E W).obj M) :
    HEq ((coefHomSections l E W).map (eqToHom h) x) x := by
  subst N
  rfl

private theorem regularSectionComponent_heq (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (n : ℕ) (x : coefTraceQuotientModule l E n) :
    HEq (regularSectionComponent l E D hl n x)
      (IntegralPointCoefficientAdjunction.finiteValue D.k l E n x) := by
  exact sectionCast l E (Spec (.of D.k)) _ _
    ((coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec.1
      (regularSequence l E (Spec (.of D.k))) n).symm
    (regularSectionValue l E D hl n x)

private instance regularSectionValue_isIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (n : ℕ) : IsIso (regularSectionValue l E D hl n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (IntegralPointCoefficientAdjunction.integral_point_coefficient_adjunction l E D hl).2.2.1 n

private instance regularSectionComponent_isIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (n : ℕ) : IsIso (regularSectionComponent l E D hl n) := by
  dsimp only [regularSectionComponent]
  infer_instance

private theorem apply_heq {α γ : Type (u + 1)} {β δ : Type (u + 1)}
    {f : α → β} {g : γ → δ} {x : α} {y : γ}
    (hcod : β = δ) (h : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst δ
  exact heq_of_eq (congr_heq h hx)

private theorem regularSectionComponent_naturality
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (n : ℕ) :
    (coefCurryingQuotients l E).map (homOfLE (Nat.le_succ n)).op ≫
        regularSectionComponent l E D hl n =
      regularSectionComponent l E D hl (n + 1) ≫
        (regularSections l E (Spec (.of D.k))).map (homOfLE (Nat.le_succ n)).op := by
  ext x
  let W := Spec (.of D.k)
  let V := op (PointDerivedHom.finalObject D.k)
  have hcod :
      ↥((regularSections l E W).obj (op n)) =
        ↥((regularSequence l E W).val.obj (op (n, V.unop))) :=
    congrArg (fun M : scalarReductionSource l E W ↦ ↥(M.val.obj V))
      ((coefficientSequenceRestriction_exists l E W).exists.choose_spec.1
        (regularSequence l E W) n)
  have hmap := (coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.1
    (regularSequence l E W) (n + 1) n (Nat.le_succ n) V
  have hx := regularSectionComponent_heq l E D hl (n + 1) x
  have hh := apply_heq hcod hmap hx
  have hval : (regularSequence l E W).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V.unop)).op
        (IntegralPointCoefficientAdjunction.finiteValue D.k l E (n + 1) x) =
      IntegralPointCoefficientAdjunction.finiteValue D.k l E n
        ((coefCurryingQuotients l E).map (homOfLE (Nat.le_succ n)).op x) := by
    have hr : (coefficientSequenceCommRingPresheaf l E W).map
        (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V.unop)).op =
        (coefficientSequenceCommRingTransition l E W n).hom.app V := by
      change (((coefficientSequenceCommRingSystem l E W).map
        (homOfLE (Nat.le_succ n)).op).hom.app V) ≫
        ((coefficientSequenceCommRingSystem l E W).obj (op n)).obj.map (𝟙 V) = _
      erw [((coefficientSequenceCommRingSystem l E W).obj (op n)).obj.map_id,
        Category.comp_id]
      simp only [coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    change ((coefficientSequenceCommRingPresheaf l E W).map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V.unop)).op).hom _ = _
    rw [hr]
    simp only [coefCurryingQuotients, Functor.ofOpSequence_map_homOfLE_succ]
    change ((integralCoefficientSheafTransition l E W n).hom.app V).hom _ = _
    rcases x with ⟨x⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (IntegralPointCoefficientAdjunction.integral_point_coefficient_adjunction
      l E D hl).2.2.2.1 n (ULift.up (Ideal.Quotient.mk _ a))
  have hh' := hh.trans (heq_of_eq hval)
  exact eq_of_heq ((regularSectionComponent_heq l E D hl n _).trans hh'.symm)

private def regularSectionsIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    regularSections l E (Spec (.of D.k)) ≅ coefCurryingQuotients l E := by
  let f : coefCurryingQuotients l E ⟶ regularSections l E (Spec (.of D.k)) :=
    NatTrans.ofOpSequence (regularSectionComponent l E D hl)
      (regularSectionComponent_naturality l E D hl)
  have : ∀ X, IsIso (f.app X) := fun X ↦
    regularSectionComponent_isIso l E D hl X.unop
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact (asIso f).symm

private theorem sectionsExact (D : FiniteFieldDatum.{u}) :
    PreservesFiniteLimits (coefHomSections l E (Spec (.of D.k))) ∧
      PreservesFiniteColimits (coefHomSections l E (Spec (.of D.k))) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have h := (AlgebraicGeometry.ProEtale.point_proEtale_sections_exact_of_universes.{u, u,
    u + 2, u + 2} D.k).2 (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))
  let := h.1
  let := h.2.1
  change PreservesFiniteLimits
      (AlgebraicGeometry.ProEtale.pointModuleSectionsOfUniverses.{u, u} D.k
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (coefHomScalar l E (Spec (.of D.k)))) ∧
    PreservesFiniteColimits
      (AlgebraicGeometry.ProEtale.pointModuleSectionsOfUniverses.{u, u} D.k
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (coefHomScalar l E (Spec (.of D.k))))
  let A := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (coefHomScalar l E (Spec (.of D.k)))
  have : PreservesFiniteLimits A := by
    constructor
    intro J _ _
    constructor
    intro F
    exact ModuleCat.preservesLimit_restrictScalars _ F
  have : PreservesFiniteColimits A := by
    constructor
    intro J _ _
    constructor
    intro F
    exact ModuleCat.preservesColimit_restrictScalars _ F
  exact ⟨comp_preservesFiniteLimits _ A, comp_preservesFiniteColimits _ A⟩

/-- The actual quotient tower in the small-Hom localization, transported back to
its standard localization. No derived sections or unspecified witness is chosen.
Source: Stacks 0941 (blueprint: lem-coef-point-integral-regular-quotient-sections). -/
def pointIntegralQuotientTower : coefPairingDerived l E :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  (integralDualizingTowerEquivalence l E).functor.obj
    ((DerivedCategory.singleFunctor (coefPairingModules l E) 0).obj
      (coefCurryingQuotients l E))

private def derivedRegularSections (D : FiniteFieldDatum.{u})
    (h : regularSections l E (Spec (.of D.k)) ≅ coefCurryingQuotients l E) :
    (coefHomConstantDerivedSections l E (Spec (.of D.k))).obj
      ((coefHomEquivalence l E (Spec (.of D.k))).inverse.mapDerivedCategory.obj
        ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
          (coefTraceInput l E (Spec (.of D.k))
            (ringedTensorUnitComplex.{u + 1, u, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology (Spec (.of D.k))))
              (coefficientSequenceCommRingSheaf l E (Spec (.of D.k))))))) ≅
        pointIntegralQuotientTower l E := by
  let W := Spec (.of D.k)
  let A := coefficientSequenceRestriction l E W
  let B := (coefHomEquivalence l E W).inverse
  let Γ := coefHomTowerSections l E W
  let G := coefHomConstantSections l E W
  letI := (sectionsExact l E D).1
  letI := (sectionsExact l E D).2
  have hΓl : PreservesFiniteLimits Γ := by
    constructor
    intro J _ _
    exact whiskeringRight_preservesLimitsOfShape (coefHomSections l E W)
  have hΓc : PreservesFiniteColimits Γ := by
    constructor
    intro J _ _
    exact whiskeringRight_preservesColimitsOfShape (coefHomSections l E W)
  letI := hΓl
  letI := hΓc
  have hGl : PreservesFiniteLimits G := inferInstanceAs
    (PreservesFiniteLimits ((coefHomEquivalence l E W).functor ⋙ Γ))
  have hGc : PreservesFiniteColimits G := inferInstanceAs
    (PreservesFiniteColimits ((coefHomEquivalence l E W).functor ⋙ Γ))
  letI := hGl
  letI := hGc
  let e : B ⋙ G ≅ Γ :=
    (Functor.associator B (coefHomEquivalence l E W).functor Γ).symm ≪≫
      Functor.isoWhiskerRight (coefHomEquivalence l E W).counitIso Γ ≪≫ Γ.leftUnitor
  let Q := DerivedCategory.Q.obj (ringedTensorUnitComplex.{u + 1, u, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W))
  let a := G.rightDerivedFunctorIsoMapDerivedCategory.app
    (B.mapDerivedCategory.obj (A.mapDerivedCategory.obj Q))
  let b := (Functor.mapDerivedCategoryCompIso B G).symm.app
    (A.mapDerivedCategory.obj Q)
  let c := (Functor.mapDerivedCategoryCompIso A (B ⋙ G)).symm.app Q
  let d := (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft A e)).app Q
  let t := ((A ⋙ Γ).mapDerivedCategorySingleFunctor 0).app (regularSequence l E W)
  let q := (DerivedCategory.singleFunctor (coefPairingModules l E) 0).mapIso h
  let v := (Localization.compUniqFunctor (integralDualizingSmallTowerQ l E)
    DerivedCategory.Q (HomologicalComplex.quasiIso (coefPairingModules l E) (.up ℤ))).app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (coefCurryingQuotients l E))
  exact a ≪≫ b ≪≫ c ≪≫ d ≪≫ t ≪≫ q ≪≫ v.symm

/-- Sections of the actual regular quotient-system complex give the actual
quotient module tower, including every quotient transition.

Source: prop-coef-integral-dualizing, second proof paragraph, final scalar
adjunction; integral_point_coefficient_adjunction; Stacks 03CW, 0941.
(blueprint: lem-coef-point-integral-regular-quotient-sections).

Proof: the regular sequence module has at (n,U) the finite coefficient ring
A_n(U); restriction to the constant completed ring changes only its action.
The constant-sequence equivalence therefore realizes its restriction as the
strict tower of these regular finite sheaves. At the final object of the
algebraically closed point, the constant-value maps A_n to A_n(s) are bijective.
Their inverses are linear for the actual integral scalar action, because the
completed projection of a constant is its quotient. The transition identity
in integral_point_coefficient_adjunction shows that these maps form one tower
isomorphism with coefCurryingQuotients. Final-object sections at this point are
exact; apply that fact levelwise to strict towers. Consequently their total
right derived functor on the degree-zero regular sequence is computed by
ordinary sections, including the actual maps. Apply the single-complex functor
to the tower isomorphism, then the unique identity-on-complexes comparison of
localizations. This gives the asserted isomorphism. The index 0 denotes the
first positive quotient, so no zero-exponent exception is needed. -/
theorem point_integral_regular_quotient_sections
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    Nonempty ((coefHomConstantDerivedSections l E (Spec (.of D.k))).obj
      ((coefHomEquivalence l E (Spec (.of D.k))).inverse.mapDerivedCategory.obj
        ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
          (coefTraceInput l E (Spec (.of D.k))
            (ringedTensorUnitComplex.{u + 1, u, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology (Spec (.of D.k))))
              (coefficientSequenceCommRingSheaf l E (Spec (.of D.k))))))) ≅
        pointIntegralQuotientTower l E) := by
  exact ⟨derivedRegularSections l E D (regularSectionsIso l E D hl)⟩

end WeilConjectures
