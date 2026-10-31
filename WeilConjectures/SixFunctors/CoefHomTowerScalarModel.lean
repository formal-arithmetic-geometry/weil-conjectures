/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefHomTowerScalarData

/-! # The Hom-tower representative and scalar-adjunction comparison

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2;
Stacks Project, Tags 06YS, 0A95, 0A96, 07A6, 08J9 and 0941
(blueprint: lem-coef-hom-tower-scalar-model).

All sections retain the integral action and the strict tower index. The natural-number
index n denotes exponent n+1. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe t u c v r d w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The actual ordinary-section square commutes by identity on underlying sections.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: both composites evaluate M at (n,W); their integral scalar action is the
completion projection followed by the constant integral map. The limit-cone
identity says this is exactly the finite quotient of that constant map. The
section-preserving sequence equivalence retains all section objects and maps,
so identity on each section defines the required isomorphism, uniquely. -/
theorem coefHomOrdinaryFactorization_exists :
    ∃! γ : coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
        coefHomOrdinaryRestriction l E W ⋙ coefHomConstantSections l E W,
      ∀ (M : coefficientSequenceModules l E W) (n : ℕ)
        (x : (((coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E).obj M).obj
          (op n))), HEq (((γ.hom.app M).app (op n)) x) x := by
  have hs (n : ℕ) (r : ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) :
      (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app
          (op (Scheme.ProEt.mk (𝟙 W))) (coefHomScalar l E W r) =
        coefHomQuotientSectionScalarComponent l E W n
          (coefHomPointScalarComponent l E n r) := by
    let U := op (Scheme.ProEt.mk (𝟙 W))
    let q := CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
    have hc := limit.lift_π (integralConstantConeOfUniverses l E W) (op n)
    have hx := congrArg (fun z ↦ (z.hom.app U)
      (((forget₂ CommRingCat RingCat).map
        ((toSheafify (Scheme.ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app
              U)) r)) hc
    change (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U
      (coefHomScalar l E W r) = _ at hx
    rw [hx]
    have hq := toSheafify_naturality (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map q)
    have hqa := congrArg (fun z ↦ z.app U) hq
    exact (ConcreteCategory.congr_hom hqa r).symm
  let γ : coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
      coefHomOrdinaryRestriction l E W ⋙ coefHomConstantSections l E W :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦
      { hom := ConcreteCategory.ofHom
          (C := ModuleCat (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))
          (X := (((coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E).obj M).obj n))
          (Y := (((coefHomOrdinaryRestriction l E W ⋙
            coefHomConstantSections l E W).obj M).obj n))
          { toFun := fun x ↦
              (show M.val.obj (op (n.unop, Scheme.ProEt.mk (𝟙 W))) from x)
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro r x
              exact congrArg (fun z ↦
                ((M.val.obj (op (n.unop, Scheme.ProEt.mk (𝟙 W)))).smul z).hom x)
                  (hs n.unop r).symm }
        inv := ConcreteCategory.ofHom
          (C := ModuleCat (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))
          (X := (((coefHomOrdinaryRestriction l E W ⋙
            coefHomConstantSections l E W).obj M).obj n))
          (Y := (((coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E).obj M).obj n))
          { toFun := fun x ↦
              (show M.val.obj (op (n.unop, Scheme.ProEt.mk (𝟙 W))) from x)
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro r x
              exact congrArg (fun z ↦
                ((M.val.obj (op (n.unop, Scheme.ProEt.mk (𝟙 W)))).smul z).hom x)
                  (hs n.unop r) }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl))
      (by intros; ext n x; rfl)
  refine ⟨γ, ?_, ?_⟩
  · intro M n x
    rfl
  · intro ε hε
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext x
    exact eq_of_heq (hε M n.unop x)

/-- The uniquely section-normalized ordinary square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomOrdinaryFactorization :
    coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
      coefHomOrdinaryRestriction l E W ⋙ coefHomConstantSections l E W :=
  (coefHomOrdinaryFactorization_exists l E W).choose

/-- The same identity section square on actual complexes, with all composition transports.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFactorizationComplexIso (L : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ((coefHomPointRestriction l E).mapHomologicalComplex (.up ℤ)).obj
        (((coefHomQuotientSections l E W).mapHomologicalComplex (.up ℤ)).obj L) ≅
      ((coefHomConstantSections l E W).mapHomologicalComplex (.up ℤ)).obj
        (((coefHomOrdinaryRestriction l E W).mapHomologicalComplex (.up ℤ)).obj L) :=
  (NatIso.mapHomologicalComplex (coefHomOrdinaryFactorization l E W) (.up ℤ)).app L

/-- The universal-comparison equation that fixes the derived section square.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomDerivedFactorizationNormalization
    (κ : coefHomRestrictedQuotientSections l E W ≅
      coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W) : Prop :=
  ∀ L : CochainComplex (coefficientSequenceModules l E W) ℤ,
    (coefHomPointRestriction l E).mapDerivedCategoryFactors.inv.app
        (((coefHomQuotientSections l E W).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (coefHomPointDerivedRestriction l E).map
        (coefficientRightDerivedComparison (coefHomQuotientSections l E W) L) ≫
      κ.hom.app (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map (coefHomFactorizationComplexIso l E W L).hom ≫
      coefficientRightDerivedComparison (coefHomConstantSections l E W)
        (((coefHomOrdinaryRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
          L) ≫
      (coefHomConstantDerivedSections l E W).map
        ((coefHomOrdinaryRestriction l E W).mapDerivedCategoryFactors.inv.app L)

/-- The canonical derived composition comparison, fixed by its universal units.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the ordinary square is the identity on sections. Derive it in two ways.
Exact restriction at the point commutes with right derivation; on the site,
the normalized ringed-topos derived-pushforward composition theorem applies.
Its acyclicity statement compares the section direct images of the two resolutions;
it does not require scalar restriction to preserve K-injectives. The universal
units give the displayed equality on every complex. The right-derived universal
property determines the comparison uniquely;
the K-injective calculation proves it is invertible. -/
theorem coefHomDerivedFactorization_exists :
    ∃! κ : coefHomRestrictedQuotientSections l E W ≅
        coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W,
      CoefHomDerivedFactorizationNormalization l E W κ := by
  sorry

/-- The derived square uniquely normalized by its universal comparison on complexes.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedFactorization :
    coefHomRestrictedQuotientSections l E W ≅
      coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W :=
  (coefHomDerivedFactorization_exists l E W).choose

/-- Derived global sections with integral coefficients and their actual scalar action.
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedSections : DerivedCategory (scalarReductionSource l E W) ⥤
    DerivedCategory (ModuleCat.{max u (t + 1)}
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  (coefHomSections l E W).rightDerivedFunctor

/-- The finite restricted global Hom, as a whole object of D(R).
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteIntegral (n : ℕ) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤
        DerivedCategory (ModuleCat.{max u (t + 1)}
          (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((𝟭 _).prod (coefficientSequenceDerivedEvaluation l E W n ⋙
    coefficientFiniteDerivedRestriction l E W n)) ⋙
      coefficientIntegralInternalHom l E W ⋙ coefHomDerivedSections l E W

/-- Finite quotient-linear Hom followed by scalar restriction and integral sections.
The ringed-topos composition comparison identifies this with restricted
quotient-linear derived sections, as a whole integral-coefficient complex.
Source: Stacks 07A6, 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteQuotient
    (S : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (n : ℕ) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤
        DerivedCategory (ModuleCat.{max u (t + 1)}
          (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  (((S.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).derived.op).prod
    (coefficientSequenceDerivedEvaluation l E W n)) ⋙
      coefficientFiniteInternalHom l E W n ⋙ coefficientFiniteDerivedRestriction l E W n ⋙
        coefHomDerivedSections l E W

/-- The finite scalar extension is the recorded K_n construction, by the unique
unit-compatible comparison of left adjoints to the same actual restriction functor.
Source: Stacks 06YY, 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteExtensionIso
    (F : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (n : ℕ) :
    (F.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).derived ≅
      coefficientFiniteDerivedExtension l E W n :=
  Adjunction.leftAdjointUniq
    (F.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).adjunction
    (coefficientFiniteAdjunction l E W n)

/-- The constant-ring sequence complex of a simultaneous tower resolution.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceComplex
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomConstantModules l E W) ℤ :=
  ((coefHomEquivalence l E W).inverse.mapHomologicalComplex (.up ℤ)).obj I

/-- The actual sheaf Hom complex on the constant-ring sequence site.
Source: Stacks 0A8X, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceHomComplex
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomConstantModules l E W) ℤ :=
  homComplex (R := coefHomConstantRing l E W)
    (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
    (coefHomSequenceComplex l E W I)

/-- Actual un-derived sections of the sequence-site sheaf Hom complex.
Source: Stacks 0A8Z, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceSectionComplex
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomPointModules.{t, u} l E) ℤ :=
  ((coefHomConstantSections l E W).mapHomologicalComplex (.up ℤ)).obj
    (coefHomSequenceHomComplex l E W P I)

/-- Componentwise normalization of the slice identification. At (n,U), restrict the
slice morphism to the same terminal index n; its earlier components are forced by
postcomposition with the transitions. The product index p is retained in every degree.
Source: Stacks 04TT, 0A8X, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomSliceNormalization
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (ε : coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I) : Prop :=
  ∀ (i p : ℤ) (n : ℕ) (U : W.ProEt)
    (f : U ⟶ Scheme.ProEt.mk (𝟙 W))
    (x : ((coefHomSequenceSectionComplex l E W P I).X i).obj (op n)),
    HEq
      ((((coefficientHomComponent.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n)) i p (p + i) rfl).val.app
          (op (Scheme.ProEt.mk (𝟙 W))))
        (((ε.hom.f i).app (op n)) x)).app (op (Over.mk f)))
      ((((coefficientHomComponent.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefHomConstantRing l E W)
        (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (coefHomSequenceComplex l E W I) i p (p + i) rfl).val.app
          (op (n, Scheme.ProEt.mk (𝟙 W)))) x).app
            (op (Over.mk (Prod.mkHom (𝟙 n) f))))

/-- The slice Hom identification, including the actual differentials and transitions.
Source: Stacks 04TT, 0A8X, 0A8Z, 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof: on the sequence slice ending at (n,U), a map out of a constant source is
determined by its component at n; all earlier components are postcompositions with
the target transitions. Restriction to the terminal index and this reconstruction
are inverse. Apply this in each factor of the degree-r product. The differential
on both sides is d_I f - (-1)^r f d_P, so the factorwise identification is a chain
isomorphism. Vertical restriction commutes with the formula, and horizontal
restriction is precisely postcomposition. Apply global sections retaining scalars. -/
theorem coefHomSequenceSections_iso
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ∃! ε : coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I,
      CoefHomSliceNormalization l E W P I ε := by
  sorry

/-- The uniquely slice-normalized complex isomorphism.
Source: Stacks 04TT, 0A8X (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceSectionsIso
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I :=
  (coefHomSequenceSections_iso l E W P I).choose

/-- The canonical representative map: the universal sections comparison followed by
sections of the replacement-normalized internal Hom comparison, transported by eP,eI.
Source: Stacks 0A95, 0A96 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomRepresentativeMap
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) :
    DerivedCategory.Q.obj (coefHomSequenceSectionComplex l E W P I) ⟶
      (coefHomTower l E W).obj (op K, N) :=
  coefficientRightDerivedComparison (coefHomConstantSections l E W)
      (coefHomSequenceHomComplex l E W P I) ≫
    (coefHomConstantDerivedSections l E W).map
      (coefHomInternalComparison.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W)) (coefHomConstantRing l E W)
        (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (coefHomSequenceComplex l E W I) ≫
      (coefHomConstantInternalHom l E W).map
        (Prod.mkHom
          (((coefHomDerivedConstant l E W).map eP.inv ≫
            (coefHomConstant l E W).mapDerivedCategoryFactors.hom.app P).op)
          eI.hom))

/-- The actual Hom representative computes the canonical derived Hom tower.
Source: Stacks 0A95, 0A96, 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof: the constant complex of P is K-flat with flat terms by the levelwise tensor
and exactness tests. The constant-ring sequence equivalence carries the simultaneous
K-injective tower I to a K-injective sequence-site complex; evaluation also keeps
each I_n K-injective. The recorded derived-Hom comparison identifies the localization
of Hom(const P,I) with RHom(V,rho_*N). K-flat into K-injective Hom is K-injective,
so its un-derived section complex computes the total right derived sections.
The slice isomorphism identifies it with the signed strict global Hom tower.
Transport along eP and eI. This works for every choice of those representatives,
including unbounded ones, since Hom preserves the requisite quasi-isomorphisms. -/
theorem coefHomTower_representative
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (_hflat : ∀ i : ℤ,
      IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective]
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) :
    (coefHomSequenceHomComplex l E W P I).IsKInjective ∧
      (∃ η : DerivedCategory.Q.obj (coefHomStrictComplex l E W P I) ≅
          (coefHomTower l E W).obj (op K, N),
        η.hom = DerivedCategory.Q.map (coefHomSequenceSectionsIso l E W P I).inv ≫
          coefHomRepresentativeMap l E W K N P I eP eI) ∧
      (∃ θ : DerivedCategory.Q.obj (coefHomSequenceSectionComplex l E W P I) ≅
          (coefHomTower l E W).obj (op K, N),
        θ.hom = coefHomRepresentativeMap l E W K N P I eP eI) := by
  sorry

/-- The exact nth level of the constructed constant-ring equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevel (n : ℕ) : coefHomConstantModules l E W ⥤ scalarReductionSource l E W :=
  (coefHomEquivalence l E W).functor ⋙ (evaluation ℕᵒᵖ _).obj (op n)

/-- Level evaluation preserves addition through the constructed equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelAdditive (n : ℕ) : (coefHomLevel l E W n).Additive where
  map_add {_ _} f g :=
    congrArg (fun α ↦ α.app (op n)) ((coefHomEquivalence l E W).functor.map_add (f := f) (g := g))

/-- Exactness of the constructed level functor.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the equivalence preserves all limits and colimits. Tower evaluation computes
kernels and cokernels pointwise, so the composite preserves finite limits and colimits. -/
theorem coefHomLevel_exact (n : ℕ) :
    PreservesFiniteLimits (coefHomLevel l E W n) ∧
      PreservesFiniteColimits (coefHomLevel l E W n) := by
  change PreservesFiniteLimits
      ((coefHomEquivalence l E W).functor ⋙ (evaluation ℕᵒᵖ _).obj (op n)) ∧
    PreservesFiniteColimits
      ((coefHomEquivalence l E W).functor ⋙ (evaluation ℕᵒᵖ _).obj (op n))
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-limit witness for level evaluation.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelLimits (n : ℕ) : PreservesFiniteLimits (coefHomLevel l E W n) :=
  (coefHomLevel_exact l E W n).1

/-- The finite-colimit witness for level evaluation.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelColimits (n : ℕ) : PreservesFiniteColimits (coefHomLevel l E W n) :=
  (coefHomLevel_exact l E W n).2

private def coefHomScalarSquare {R S T U : RingCat.{r}}
    (f : R ⟶ S) (g : S ⟶ U) (h : R ⟶ T) (i : T ⟶ U)
    (he : f ≫ g = h ≫ i) (M : ModuleCat.{r} U) :
    (ModuleCat.restrictScalars f.hom).obj ((ModuleCat.restrictScalars g.hom).obj M) ≅
      (ModuleCat.restrictScalars h.hom).obj ((ModuleCat.restrictScalars i.hom).obj M) :=
  (ModuleCat.restrictScalarsComp'App f.hom g.hom (f ≫ g).hom rfl M).symm ≪≫
    ModuleCat.restrictScalarsComp'App h.hom i.hom (f ≫ g).hom
      (congrArg RingCat.Hom.hom he) M

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restrictionSquare
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {R R' : Sheaf K RingCat.{r}} {S T : Sheaf J RingCat.{r}}
    (a : R ⟶ R') (b : S ⟶ T)
    (q : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (q' : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R')
    (he : q ≫ (F.sheafPushforwardContinuous RingCat J K).map a = b ≫ q') :
    ∃! δ : SheafOfModules.restrictScalars.{r} a ⋙ SheafOfModules.pushforward q ≅
        SheafOfModules.pushforward q' ⋙ SheafOfModules.restrictScalars b,
      ∀ (M : SheafOfModules.{r} R') (U : Cᵒᵖ)
        (x : ((SheafOfModules.restrictScalars a ⋙
          SheafOfModules.pushforward q).obj M).val.obj U),
        HEq ((δ.hom.app M).val.app U x) x := by
  have hc (U : Cᵒᵖ) : q.hom.app U ≫ a.hom.app (op (F.obj U.unop)) =
      b.hom.app U ≫ q'.hom.app U := congrArg (fun f ↦ f.hom.app U) he
  let δ : SheafOfModules.restrictScalars.{r} a ⋙ SheafOfModules.pushforward q ≅
      SheafOfModules.pushforward q' ⋙ SheafOfModules.restrictScalars b :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun U ↦
          coefHomScalarSquare (q.hom.app U) (a.hom.app (op (F.obj U.unop)))
            (b.hom.app U) (q'.hom.app U) (hc U) (M.val.obj (op (F.obj U.unop))))
          (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  refine ⟨δ, ?_, ?_⟩
  · intro M U x
    rfl
  · intro ε hε
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext U x
    exact eq_of_heq (hε M U x)

/-- The ordinary restricted evaluation is fixed by identity on every section.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: both paths evaluate the quotient module at (n,U), then restrict along
R_W(U) to A_n(U). The constructed equivalence keeps those actual sections;
identity maps are linear, natural and uniquely determined by this formula. -/
theorem coefHomLevelRestriction_exists (n : ℕ) :
    ∃! δ : coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n ≅
        coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n,
      ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
        (x : ((coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n).obj M).val.obj U),
        HEq ((δ.hom.app M).val.app U x) x := by
  let j := systemSequenceVerticalRingMap
    ((Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W)) n
  let π := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat RingCat)).map (coefHomScalarMap l E W)
  let p := (sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  have he : j ≫ ((Prod.sectR n W.ProEt).sheafPushforwardContinuous
      RingCat (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))).map π = p ≫ φ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hφ : φ.hom.app U = 𝟙 _ := by
      dsimp only [φ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change 𝟙 _ ≫ p.hom.app U = p.hom.app U ≫ φ.hom.app U
    rw [hφ]
    rfl
  exact restrictionSquare (Scheme.ProEt.topology W)
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (Prod.sectR n W.ProEt)
    π p j φ he

/-- Section-normalized ordinary restricted evaluation.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevelRestriction (n : ℕ) :
    coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  (coefHomLevelRestriction_exists l E W n).choose

/-- Exact localization of the section-normalized restricted evaluation square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedLevelRestriction (n : ℕ) :
    coefHomDerivedRestriction l E W ⋙ (coefHomLevel l E W n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  (Functor.mapDerivedCategoryCompIso (coefHomOrdinaryRestriction l E W)
    (coefHomLevel l E W n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (coefHomLevelRestriction l E W n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (scalarReductionRestriction l E W n)

/-- Applying the explicit inverse and then evaluating returns I_n, by the counit.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevelComplexIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    ((coefHomLevel l E W n).mapHomologicalComplex (.up ℤ)).obj
      (coefHomSequenceComplex l E W I) ≅ I.asFunctor.obj (op n) :=
  (((evaluation ℕᵒᵖ _).obj (op n)).mapHomologicalComplex (.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex (coefHomEquivalence l E W).counitIso (.up ℤ)).app I)

/-- The actual finite representative of restricted N_n, transported by its scalar square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteTargetMap
    (N : coefficientSequenceDerived l E W)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) (n : ℕ) :
    DerivedCategory.Q.obj (I.asFunctor.obj (op n)) ⟶
      (coefficientFiniteDerivedRestriction l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) :=
  DerivedCategory.Q.map (coefHomLevelComplexIso l E W I n).inv ≫
    (coefHomLevel l E W n).mapDerivedCategoryFactors.inv.app
      (coefHomSequenceComplex l E W I) ≫
    (coefHomLevel l E W n).mapDerivedCategory.map eI.hom ≫
    (coefHomDerivedLevelRestriction l E W n).hom.app N

/-- The finite representative map uses the same replacement-normalized internal Hom
and the actual universal sections comparison, with eP and the restricted eI.
Source: Stacks 0A95, 0A96 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteRepresentativeMap
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) (n : ℕ) :
    DerivedCategory.Q.obj (((coefHomSections l E W).mapHomologicalComplex (.up ℤ)).obj
      (homComplex (R := completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n)))) ⟶ (coefHomFiniteIntegral l E W n).obj (op K, N) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  coefficientRightDerivedComparison (coefHomSections l E W)
      (homComplex (R := completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n))) ≫
    (coefHomDerivedSections l E W).map
      (coefHomInternalComparison.{t + 1, t, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P (I.asFunctor.obj (op n)) ≫
      (coefficientIntegralInternalHom l E W).map
        (Prod.mkHom eP.inv.op (coefHomFiniteTargetMap l E W N I eI n)))

/-- Finite evaluation is normalized on all resolving complexes by the actual signed
Hom tower and the finite representative map. Evaluation of that strict complex is
literally the finite Hom section complex, including its differential.
Source: Stacks 0A95, 0A96, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomEvaluationNormalization (n : ℕ)
    (γ : coefHomTower l E W ⋙ coefHomPointEvaluation l E n ≅
      coefHomFiniteIntegral l E W n) : Prop :=
  ∀ (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (_hflat : ∀ i : ℤ,
      IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective]
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N),
    (coefHomPointEvaluation l E n).map
        (DerivedCategory.Q.map (coefHomSequenceSectionsIso l E W P I).inv ≫
          coefHomRepresentativeMap l E W K N P I eP eI) ≫ γ.hom.app (op K, N) =
      ((evaluation ℕᵒᵖ _).obj (op n)).mapDerivedCategoryFactors.hom.app
        (coefHomStrictComplex l E W P I) ≫
      coefHomFiniteRepresentativeMap l E W K N P I eP eI n

/-- Full Hom-tower/scalar-adjunction comparison, natural in both derived arguments.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2; Stacks 06YS,
0A95, 0A96, 07A6, 08J9, 0D6E and 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof:
1. Use the exact constant-ring sequence equivalence and simultaneous K-injective
resolutions of towers; evaluation gives K-injective finite components.
2. Constant flat-term K-flat P stays K-flat by testing tensor acyclicity on levels.
3. The sequence slice ending at n identifies Hom(const P,I) with Hom(P,I_n),
with the actual signed differential and postcomposition transitions.
4. Hom from K-flat into K-injective is K-injective, so its ordinary global-section
tower computes derived sections and gives coefHomTower_representative.
5. Apply the recorded scalar internal-Hom adjunction on the sequence site. Its
comparison has exactly the representing bijections and restricted evaluation
normalization displayed below; no coefficient-map flatness is used.
6. The actual ordinary-section square g_R rho_W = rho_0 g_Q and the normalized
derived-pushforward composition comparison identify the two derived towers.
7. Exact evaluation gives the finite integral RHom complexes, retaining R scalars.
8. Apply the same normalized scalar internal-Hom adjunction at each completion
projection. Derived change of rings on P gives K_n; its unit is p mapped to p tensor 1.
9. All comparisons commute with precomposition and postcomposition and invert
quasi-isomorphisms, so they descend naturally in both derived variables. -/
theorem coefHomTowerScalarModel
    (S : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)}
      (coefficientSequenceTopology (Scheme.ProEt.topology W)))
    (μ : ∀ {R T : Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
        CommRingCat.{max u (t + 1)}} (a : R ⟶ T),
      ScalarHomTensorComparison.{t + 1, t, u, max (t + 2) (u + 1)} S a)
    (A : ScalarInternalHomAdjunction.{t + 1, t, u, max (t + 2) (u + 1)} S μ)
    (F : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (ν : ∀ {R T : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}}
      (a : R ⟶ T), ScalarHomTensorComparison.{t + 1, t, u, max (t + 2) (u + 1)} F a)
    (B : ScalarInternalHomAdjunction.{t + 1, t, u, max (t + 2) (u + 1)} F ν) :
    ∃ (α : coefHomTower l E W ≅ coefHomScalarTower l E W S),
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        α.inv.app (op K, N) =
          (coefHomDerivedFactorization l E W).hom.app
            ((coefficientSequenceInternalHom l E W).obj
              (op ((S.scalar (coefHomScalarMap l E W)).derived.obj
                ((coefHomDerivedConstant l E W).obj K)), N)) ≫
          (coefHomConstantDerivedSections l E W).map
            ((A.iso (coefHomScalarMap l E W)).hom.app
              (op ((coefHomDerivedConstant l E W).obj K), N))) ∧
      (∀ n : ℕ, ∃ γ : coefHomTower l E W ⋙ coefHomPointEvaluation l E n ≅
          coefHomFiniteIntegral l E W n, CoefHomEvaluationNormalization l E W n γ) ∧
      (∀ n : ℕ, ∃ β : coefHomFiniteIntegral l E W n ≅
          coefHomFiniteQuotient l E W F n,
        ∀ (K : DerivedCategory (scalarReductionSource l E W))
          (N : coefficientSequenceDerived l E W),
          β.inv.app (op K, N) = (coefHomDerivedSections l E W).map
            ((B.iso (completedIntegralCommRingProjectionUnrestricted l E W n)).hom.app
              (op K, (coefficientSequenceDerivedEvaluation l E W n).obj N))) ∧
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W)
        (T : DerivedCategory (coefHomConstantModules l E W))
        (f : T ⟶ (scalarHomSource S (coefHomScalarMap l E W)).obj
          (op ((coefHomDerivedConstant l E W).obj K), N)),
        scalarHomBijection S (coefHomScalarMap l E W) (μ (coefHomScalarMap l E W))
          T ((coefHomDerivedConstant l E W).obj K) N f =
            f ≫ (A.iso (coefHomScalarMap l E W)).hom.app
              (op ((coefHomDerivedConstant l E W).obj K), N)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        ((S.closed (coefHomConstantRing l E W)).transpose _
          ((coefHomDerivedConstant l E W).obj K)
          ((coefHomDerivedRestriction l E W).obj N)).symm
          ((A.iso (coefHomScalarMap l E W)).hom.app
            (op ((coefHomDerivedConstant l E W).obj K), N)) =
          scalarHomRestrictedEvaluation S (coefHomScalarMap l E W)
            (μ (coefHomScalarMap l E W)) ((coefHomDerivedConstant l E W).obj K) N) ∧
      (∀ (n : ℕ) (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        ((F.closed (completedIntegralCommRingSheafUnrestricted l E W)).transpose _ K
          ((coefficientFiniteDerivedRestriction l E W n).obj
            ((coefficientSequenceDerivedEvaluation l E W n).obj N))).symm
          ((B.iso (completedIntegralCommRingProjectionUnrestricted l E W n)).hom.app
            (op K, (coefficientSequenceDerivedEvaluation l E W n).obj N)) =
          scalarHomRestrictedEvaluation F (completedIntegralCommRingProjectionUnrestricted l E W n)
            (ν (completedIntegralCommRingProjectionUnrestricted l E W n)) K
              ((coefficientSequenceDerivedEvaluation l E W n).obj N)) := by
  sorry

end WeilConjectures
