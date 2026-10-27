/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Paper.IntegralReductionTowerUnrestricted
import all Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.SystemScalarCoherence
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Paper.SemilinearDerivedSections
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Paper.PrimitiveQuotientPullbackModelExistence
import Sheaf.Paper.PrimitiveQuotientScalarModelExistence

/-! # Primitive realization on simultaneous quotient complexes

Source: Stacks 099N(2),(5), 06YS, 0G7E, 0D6D and 0941; the explicit
all-ambient quotient/Roos definitions of completed pullback and scalar extension
(blueprint: lem-trf-primitive-quotient-realization-comparisons).

Natural number n denotes positive exponent n+1. The realization interfaces fix
all representative identifications and the normalized total-limit comparison.
No flatness assumption is made on a homomorphism between quotient rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe a b r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace PrimitiveOrdinary
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}

private abbrev Mod (R : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

private structure Ordinary {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) where
  E : Mod R ⥤ Mod S
  obj_eq : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M
  map_eq : ∀ {M N} (f : M ⟶ N), E.map f =
    eqToHom (obj_eq M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (obj_eq N).symm
  [additive : E.Additive]

attribute [local instance] Ordinary.additive

private def tmul {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : P.val.obj U) : (A.E.obj P).val.obj U :=
  (eqToHom (A.obj_eq P).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ P).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

private theorem adj_exists {φ : R ⟶ S} (A : Ordinary φ) :
    ∃ adj : A.E ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
      ∀ P U (x : P.val.obj U), (adj.unit.app P).val.app U x = tmul A P U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, hadj⟩ := h A.E A.obj_eq A.map_eq
  refine ⟨adj, ?_⟩
  intro P U x
  have ht := hadj P (A.E.obj P) (eqToHom (A.obj_eq P).symm) U x
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at ht
  exact ht


private def adj {φ : R ⟶ S} (A : Ordinary φ) := (adj_exists A).choose

private theorem adj_unit {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R)
    (U : Cᵒᵖ) (x : P.val.obj U) :
    ((adj A).unit.app P).val.app U x = tmul A P U 1 x :=
  (adj_exists A).choose_spec P U x

attribute [local irreducible] adj

private theorem tmul_smul {φ : R ⟶ S} (A : Ordinary φ) (P : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    tmul A P U s x = s • tmul A P U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf φ P)
  change (eqToHom (A.obj_eq P).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • (eqToHom (A.obj_eq P).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  rw [← ((eqToHom (A.obj_eq P).symm).val.app U).hom.map_smul,
    ← (η.app U).hom.map_smul]
  congr 2
  change (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
    (s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x
  rw [mul_one]

private theorem transpose {φ : R ⟶ S} (A : Ordinary φ)
    (P : Mod R) (N : Mod S) (f : A.E.obj P ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    f.val.app U (tmul A P U s x) =
      s • (show N.val.obj U from ((adj A).homEquiv P N f).val.app U x) := by
  rw [tmul_smul, ← adj_unit]
  rw [Adjunction.homEquiv_unit]
  exact (f.val.app U).hom.map_smul s _

private theorem hom_ext {φ : R ⟶ S} (A : Ordinary φ)
    (P : Mod R) (N : Mod S) (f g : A.E.obj P ⟶ N)
    (h : ∀ U x, f.val.app U (tmul A P U 1 x) =
      g.val.app U (tmul A P U 1 x)) : f = g := by
  apply ((adj A).homEquiv P N).injective
  ext U x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app U (((adj A).unit.app P).val.app U x) =
    g.val.app U (((adj A).unit.app P).val.app U x)
  rw [adj_unit]
  exact h U x

private def comp {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ) (A : Ordinary φ) (B : Ordinary ψ) (D : Ordinary γ) :
    A.E ⋙ B.E ≅ D.E :=
  Adjunction.leftAdjointUniq
    (((adj A).comp (adj B)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition φ ψ γ hγ)) (adj D)

private theorem comp_tmul {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ) (A : Ordinary φ) (B : Ordinary ψ) (D : Ordinary γ)
    (P : Mod R) (U : Cᵒᵖ) (c : T.obj.obj U) (s : S.obj.obj U) (x : P.val.obj U) :
    ((comp hγ A B D).hom.app P).val.app U (tmul B (A.E.obj P) U c (tmul A P U s x)) =
      tmul D P U (c * (ψ.hom.app U) s) x := by
  let f := (comp hγ A B D).hom.app P
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((adj A).comp (adj B)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition φ ψ γ hγ)) (adj D) P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  have hx := congrArg (fun g : P ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map γ)).obj
        (D.E.obj P) ↦ g.val.app U x) h
  change (((adj A).homEquiv P _ ((adj B).homEquiv _ _ f)).val.app U x) =
    ((adj D).unit.app P).val.app U x at hx
  change f.val.app U _ = _
  erw [transpose B, transpose A, hx, adj_unit]
  rw [tmul_smul D P U (c * (ψ.hom.app U) s) x, mul_smul]
  rfl

attribute [local irreducible] comp

private def unit {φ : R ⟶ R} (hφ : φ = 𝟙 R) (A : Ordinary φ) : A.E ≅ 𝟭 (Mod R) :=
  Adjunction.leftAdjointUniq
    ((adj A).ofNatIsoRight (SheafOfModules.systemScalarRestrictionUnit φ hφ)) Adjunction.id

private theorem unit_tmul {φ : R ⟶ R} (hφ : φ = 𝟙 R) (A : Ordinary φ)
    (P : Mod R) (U : Cᵒᵖ) (s : R.obj.obj U) (x : P.val.obj U) :
    ((unit hφ A).hom.app P).val.app U (tmul A P U s x) = s • x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((adj A).ofNatIsoRight (SheafOfModules.systemScalarRestrictionUnit φ hφ)) Adjunction.id P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hx := congrArg (fun g : P ⟶ P ↦ g.val.app U x) h
  change ((adj A).homEquiv P P ((unit hφ A).hom.app P)).val.app U x = x at hx
  erw [transpose, hx]

attribute [local irreducible] unit

private theorem map_tmul {φ : R ⟶ S} (A : Ordinary φ) {P Q : Mod R} (f : P ⟶ Q)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : P.val.obj U) :
    (A.E.map f).val.app U (tmul A P U s x) = tmul A Q U s (f.val.app U x) := by
  have hn := (adj A).unit.naturality f
  have hx := congrArg (fun g : P ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj (A.E.obj Q) ↦
        g.val.app U x) hn
  change ((adj A).unit.app Q).val.app U (f.val.app U x) =
    (A.E.map f).val.app U (((adj A).unit.app P).val.app U x) at hx
  rw [adj_unit, adj_unit] at hx
  rw [tmul_smul A P U s x, map_smul, ← hx, tmul_smul A Q U s]

private theorem flat_of_single_kFlat [EssentiallySmall.{r} C]
    (M : Mod R)
    (hM : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((CochainComplex.singleFunctor (Mod R) 0).obj M)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let S := (CochainComplex.singleFunctor (Mod R) 0).obj M
  let T := MonoidalCategory.tensorRight M
  have hp₀ : HomologicalComplex.preservesQuasiIso (koszulTensorFunctor R S) := by
    intro X Y f hf
    exact CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R S hM f hf
  have hp : HomologicalComplex.preservesQuasiIso (T.mapHomologicalComplex (.up ℤ)) :=
    (HomologicalComplex.preservesQuasiIso).prop_of_iso
      (SheafOfModules.FlatSingleDerivedNormalization.collapse R M) hp₀
  have he : exactFunctor _ _ T :=
    (Functor.exactFunctor_iff_preservesQuasiIso T (.up ℤ)
      (i₀ := 0) (i₁ := 1) rfl (by decide)).2 hp
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm he


end PrimitiveOrdinary

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]


private def reductionOrdinary (W : Scheme.{t}) (n : ℕ) :
    PrimitiveOrdinary.Ordinary.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingProjectionUnrestricted l E W n) where
  E := unrestrictedIntegralReductionFunctor l E W n
  obj_eq := (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose
  map_eq := (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose_spec.choose
  additive :=
    (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose

/-- Every finite quotient of a flat-term K-flat representative is again flat-term
K-flat, over its own quotient ring.
Source: Stacks 06YS, 0G7E
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: use lem-pc-kflat-resolution for the input representative and apply
lem-pur-kflat-change-of-rings to each actual completion projection. Its tensor
cancellation argument restricts an acyclic target complex to the source ring,
so it requires no flatness of the projection. The same cancellation proves
flatness of each extended term. This is simultaneous at every positive level. -/
theorem primitiveQuotientReductionGood (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj) ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      (((unrestrictedIntegralFiniteComplex l E W n).obj P.obj).X i) := by
  have : (unrestrictedIntegralReductionFunctor l E W n).Additive :=
    (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose
  have hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory
          (completedIntegralCommRingSheafUnrestricted l E W)) (P.obj.X i)) := fun i ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.obj.X i)) (P.property.2 i)
  obtain ⟨hK, hF⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (completedIntegralCommRingProjectionUnrestricted l E W n) P.obj
      (unrestrictedIntegralReductionFunctor l E W n)
      (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose
      (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose_spec.choose
      P.property.1 hflat
  exact ⟨hK, fun i ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso _ _).symm (hF i)⟩


variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The canonical ordinary and derived extension along a finite quotient inclusion.
The universal cochain counit determines this model up to its unique compatible
isomorphism. Source: Stacks 06YY, 0D6D
(blueprint: lem-trf-primitive-quotient-realization-comparisons). -/
def primitiveQuotientFiniteScalarModel (W : Scheme.{t}) (n : ℕ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralScalarQuotientSheafMap l E L ι W n))

private def finiteOrdinary (W : Scheme.{t}) (n : ℕ) :
    PrimitiveOrdinary.Ordinary.{t + 1, t, max u (t + 1)}
      (integralScalarQuotientSheafMap l E L ι W n) where
  E := (primitiveQuotientFiniteScalarModel l E L ι W n).E
  obj_eq := (primitiveQuotientFiniteScalarModel l E L ι W n).obj_eq
  map_eq := (primitiveQuotientFiniteScalarModel l E L ι W n).map_eq

private def scalarOrdinary (W : Scheme.{t}) (n : ℕ) :
    PrimitiveOrdinary.Ordinary.{t + 1, t, max u (t + 1)}
      (integralScalarRho l E L ι W n) where
  E := integralScalarReduction l E L ι W n
  obj_eq := integralScalarReduction_obj l E L ι W n
  map_eq := integralScalarReduction_map l E L ι W n
  additive := integralScalarReduction_additive l E L ι W n

attribute [local irreducible] integralScalarReduction

private def quotientAssociation (W : Scheme.{t}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E W n ⋙
      (primitiveQuotientFiniteScalarModel l E L ι W n).E ≅
        integralScalarReduction l E L ι W n :=
  PrimitiveOrdinary.comp (by rfl) (reductionOrdinary l E W n)
    (finiteOrdinary l E L ι W n) (scalarOrdinary l E L ι W n)

/-- The actual sheafified balanced generator b tensor x in finite extension.
Source: Stacks 03EK (blueprint: lem-trf-primitive-quotient-realization-comparisons). -/
def primitiveQuotientFiniteTensorSection (W : Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((primitiveQuotientFiniteScalarModel l E L ι W n).E.obj M).val.obj U :=
  (eqToHom ((primitiveQuotientFiniteScalarModel l E L ι W n).obj_eq M).symm).val.app U
    ((toSheafify (Scheme.ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarQuotientSheafMap l E L ι W n) M).presheaf).app U
      (b ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U,
        ((integralScalarQuotientSheafMap l E L ι W n).hom.app U).hom] x))

private theorem quotientAssociation_tmul (W : Scheme.{t}) (n : ℕ)
    (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : N.val.obj U) :
    (((quotientAssociation l E L ι W n).hom.app N).val.app U)
      (primitiveQuotientFiniteTensorSection l E L ι W n
        ((unrestrictedIntegralReductionFunctor l E W n).obj N) U b
        (unrestrictedIntegralTensorSection l E W n N U s x)) =
      integralScalarTensorSection l E L ι W n N U
        (((integralScalarQuotientSheafMap l E L ι W n).hom.app U s) * b) x := by
  have h := PrimitiveOrdinary.comp_tmul (by rfl) (reductionOrdinary l E W n)
    (finiteOrdinary l E L ι W n) (scalarOrdinary l E L ι W n) N U b s x
  exact h.trans (by
    rw [mul_comm]
    simp only [PrimitiveOrdinary.tmul, scalarOrdinary, integralScalarTensorSection,
      integralScalarReductionIso, eqToIso.inv, eqToHom_app]
    rfl)

attribute [local irreducible] quotientAssociation

/-- Generator normalization of the simultaneous association maps.
Source: Stacks 03EK, 0D6D
(blueprint: lem-trf-primitive-quotient-realization-comparisons). -/
def PrimitiveQuotientAssociation (W : Scheme.{t})
    (a : ∀ n : ℕ,
      unrestrictedIntegralReductionFunctor l E W n ⋙
        (primitiveQuotientFiniteScalarModel l E L ι W n).E ≅
          integralScalarReduction l E L ι W n) : Prop :=
      ∀ (n : ℕ) (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
        (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U),
        (((a n).hom.app M).val.app U)
          (primitiveQuotientFiniteTensorSection l E L ι W n
            ((unrestrictedIntegralReductionFunctor l E W n).obj M) U b
            (unrestrictedIntegralTensorSection l E W n M U s x)) =
          integralScalarTensorSection l E L ι W n M U
            (((integralScalarQuotientSheafMap l E L ι W n).hom.app U s) * b) x

/-- The ordinary association, including its formula on all balanced generators.
Source: Stacks 03EK, 0D6D
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: send b tensor (a tensor x) to (iota(a)b) tensor x and send b tensor x
back to b tensor (1 tensor x). Balancing proves that these maps are well-defined
and inverse. They commute with restrictions, hence sheafify, and with every
module map. Applying them degreewise gives the chain association. On quotient
transitions both paths reduce the product iota(a)b. For three fields both
associations multiply all coefficient factors in their common target; the
identity inclusion gives the same multiplication map. These are calculations
before taking any Roos complex or derived limit. -/
theorem primitiveQuotientScalarAssociation (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x)) :
    ∃! a : ∀ n : ℕ,
      unrestrictedIntegralReductionFunctor l E W n ⋙
        (primitiveQuotientFiniteScalarModel l E L ι W n).E ≅
          integralScalarReduction l E L ι W n,
      PrimitiveQuotientAssociation l E L ι W a := by
  refine ⟨quotientAssociation l E L ι W, ?_, ?_⟩
  · exact quotientAssociation_tmul l E L ι W
  · intro a ha
    funext n
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ((PrimitiveOrdinary.adj (finiteOrdinary l E L ι W n)).homEquiv _ _).injective
    apply PrimitiveOrdinary.hom_ext (reductionOrdinary l E W n)
    intro U x
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change ((a n).hom.app N).val.app U
      (((PrimitiveOrdinary.adj (finiteOrdinary l E L ι W n)).unit.app _).val.app U
        (unrestrictedIntegralTensorSection l E W n N U 1 x)) = _
    change ((a n).hom.app N).val.app U
      (((PrimitiveOrdinary.adj (finiteOrdinary l E L ι W n)).unit.app _).val.app U
        (unrestrictedIntegralTensorSection l E W n N U 1 x)) =
      ((quotientAssociation l E L ι W n).hom.app N).val.app U
        (((PrimitiveOrdinary.adj (finiteOrdinary l E L ι W n)).unit.app _).val.app U
          (unrestrictedIntegralTensorSection l E W n N U 1 x))
    let z := unrestrictedIntegralTensorSection l E W n N U 1 x
    have hu := PrimitiveOrdinary.adj_unit (finiteOrdinary l E L ι W n)
      ((unrestrictedIntegralReductionFunctor l E W n).obj N) U z
    exact (congrArg (fun y ↦ ((a n).hom.app N).val.app U y) hu).trans
      (((ha n N U 1 1 x).trans
        (quotientAssociation_tmul l E L ι W n N U 1 1 x).symm).trans
        (congrArg (fun y ↦
          ((quotientAssociation l E L ι W n).hom.app N).val.app U y) hu).symm)


private theorem sequenceExact_iff (W : Scheme.{t})
    (s : ShortComplex (coefficientSequenceModules l E W)) :
    s.Exact ↔ ∀ n : ℕ, (s.map (coefficientSequenceEvaluation l E W n)).Exact := by
  let D := (SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)).some.systems
  exact D.componentwise s

private theorem sequenceKFlat_of_evaluations (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) C := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (sequenceExact_iff l E W _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (coefficientSequenceEvaluation l E W n)
  have ht := hC n _ hZn
  exact (ht i).of_iso (coefficientEvaluationTensorIso l E W n Z C).symm


private theorem sequenceFlat_of_evaluations (W : Scheme.{t})
    (M : coefficientSequenceModules l E W)
    (hM : ∀ n : ℕ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      ((coefficientSequenceEvaluation l E W n).obj M)) :
    SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) M := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let S := (CochainComplex.singleFunctor (coefficientSequenceModules l E W) 0).obj M
  have hs : CochainComplex.IsKFlatIndependentCoefficients (R := R) S := by
    apply sequenceKFlat_of_evaluations l E W S
    intro n
    let B := integralCoefficientCommRingSheaf l E W n
    have hn := SheafOfModules.FlatSingleDerivedNormalization.single_kFlat B
      ((coefficientSequenceEvaluation l E W n).obj M) (hM n)
    exact SheafOfModules.kFlat_iso_independent B
      ((HomologicalComplex.singleMapHomologicalComplex
        (coefficientSequenceEvaluation l E W n) (.up ℤ) 0).app M).symm hn
  exact PrimitiveOrdinary.flat_of_single_kFlat M hs


/-- A simultaneous quotient presentation is K-flat on the entire ringed sequence
site. Ordinary system scalar change therefore computes its derived scalar change.
Source: Stacks 06YY, 0G7E; vertical sequence-site construction, Stacks 0941
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: evaluate the presentation at every positive level. By
primitiveQuotientReductionGood and its level isomorphisms these complexes are K-flat
with flat terms. Tensor products, kernels and sheafified cokernels on the vertical
sequence site are computed componentwise. Thus tensoring any acyclic system complex
with C remains acyclic at every level and hence as a system. The same argument for
short exact sequences gives flatness of all terms. The universal cochain counit
of lem-pur-derived-change-of-rings is invertible on a K-flat input, giving the last
clause without any flatness assumption on the quotient coefficient inclusion. -/
theorem primitiveQuotientSystemGood (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
    (_hC : CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) C ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) (C.X i)) ∧
    IsIso ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) := by
  have hn (n : ℕ) := primitiveQuotientReductionGood l E W _hlW P n
  have hk (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) :=
    SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
      (κ n).symm (hn n).1
  have hK := sequenceKFlat_of_evaluations l E W C hk
  refine ⟨hK, ?_, (integralComparisonSequenceScalarModel l E L ι W).computes C hK⟩
  intro i
  apply sequenceFlat_of_evaluations l E W (C.X i)
  intro n
  exact SheafOfModules.flatOnSite_of_iso (integralCoefficientCommRingSheaf l E W n)
    ((HomologicalComplex.eval _ (.up ℤ) i).mapIso (κ n)).symm ((hn n).2 i)


/-- The association commutes with the actual quotient transition on every generator.
Source: Stacks 03EK, 0941
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: the high-level association multiplies the two scalars. The actual transition
reduces that product. In the other order each scalar is reduced first, and the
low-level association multiplies them. A ring homomorphism preserves multiplication.
The scalar transition is characterized by this formula on sheafified tensor generators;
these generate locally, so this is the strict transition square in every degree. -/
theorem primitiveQuotientScalarTransition (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (a : ∀ n : ℕ,
      unrestrictedIntegralReductionFunctor l E W n ⋙
        (primitiveQuotientFiniteScalarModel l E L ι W n).E ≅
          integralScalarReduction l E L ι W n)
    (_ha : PrimitiveQuotientAssociation l E L ι W a)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (i : ℤ)
    (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W (n + 1)).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W (n + 1)).obj.obj U)
    (x : (P.X i).val.obj U) :
    (((integralScalarTransition l E L ι W n).app P).f i).val.app U
      ((((a (n + 1)).hom.app (P.X i)).val.app U)
        (primitiveQuotientFiniteTensorSection l E L ι W (n + 1)
          ((unrestrictedIntegralReductionFunctor l E W (n + 1)).obj (P.X i)) U b
          (unrestrictedIntegralTensorSection l E W (n + 1) (P.X i) U s x))) =
      (((a n).hom.app (P.X i)).val.app U)
        (primitiveQuotientFiniteTensorSection l E L ι W n
          ((unrestrictedIntegralReductionFunctor l E W n).obj (P.X i)) U
          ((integralCoefficientSheafTransition l L W n).hom.app U b)
          (unrestrictedIntegralTensorSection l E W n (P.X i) U
            ((integralCoefficientSheafTransition l E W n).hom.app U s) x)) := by
  rw [_ha (n + 1), _ha n]
  unfold integralScalarTransition
  rw [(integralScalarTransition_existsUnique l E L ι W n).exists.choose_spec]
  congr 1
  rw [map_mul]
  congr 1
  have hs := integralScalarQuotientSheafMap_transition l E L ι W n
  exact congrArg (fun a ↦ a.hom.app U s) hs


private theorem finiteScalarComp
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (W : Scheme.{t}) (n : ℕ) :
    integralScalarQuotientSheafMap l E M (j.comp ι) W n =
      integralScalarQuotientSheafMap l E L ι W n ≫
        integralScalarQuotientSheafMap l L M j W n := by
  unfold integralScalarQuotientSheafMap
  rw [← Functor.map_comp]
  apply congrArg _
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

/-- The two associations for three coefficient fields are the same natural map,
before taking a Roos cone. The intermediate maps are fixed on every tensor generator.
Source: Stacks 03EK, 0D6D
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: construct the finite associator and the mixed completion-to-finite associator
by balanced multiplication, with inverses inserting 1. Both paths around the displayed
square send c tensor (b tensor (s tensor x)) to (j(iota(s)b)c) tensor x.
Associativity of multiplication makes the results equal. These local formulas sheafify,
are natural in the module, and hence hold degreewise for every complex. The transition
calculation in primitiveQuotientScalarTransition applies to each factor. -/
theorem primitiveQuotientScalarTriple
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x)) :
    ∃ (aEL : ∀ n : ℕ,
        unrestrictedIntegralReductionFunctor l E W n ⋙
          (primitiveQuotientFiniteScalarModel l E L ι W n).E ≅
            integralScalarReduction l E L ι W n)
      (aEM : ∀ n : ℕ,
        unrestrictedIntegralReductionFunctor l E W n ⋙
          (primitiveQuotientFiniteScalarModel l E M (j.comp ι) W n).E ≅
            integralScalarReduction l E M (j.comp ι) W n)
      (c : ∀ n : ℕ,
        (primitiveQuotientFiniteScalarModel l E L ι W n).E ⋙
          (primitiveQuotientFiniteScalarModel l L M j W n).E ≅
            (primitiveQuotientFiniteScalarModel l E M (j.comp ι) W n).E)
      (b : ∀ n : ℕ,
        integralScalarReduction l E L ι W n ⋙
          (primitiveQuotientFiniteScalarModel l L M j W n).E ≅
            integralScalarReduction l E M (j.comp ι) W n),
      PrimitiveQuotientAssociation l E L ι W aEL ∧
      PrimitiveQuotientAssociation l E M (j.comp ι) W aEM ∧
      (∀ (n : ℕ) (N : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
        (v : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
        (w : (integralCoefficientCommRingSheaf l M W n).obj.obj U) (x : N.val.obj U),
        (((c n).hom.app N).val.app U)
          (primitiveQuotientFiniteTensorSection l L M j W n
            ((primitiveQuotientFiniteScalarModel l E L ι W n).E.obj N) U w
            (primitiveQuotientFiniteTensorSection l E L ι W n N U v x)) =
          primitiveQuotientFiniteTensorSection l E M (j.comp ι) W n N U
            (((integralScalarQuotientSheafMap l L M j W n).hom.app U v) * w) x) ∧
      (∀ (n : ℕ) (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (v : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
        (w : (integralCoefficientCommRingSheaf l M W n).obj.obj U) (x : N.val.obj U),
        (((b n).hom.app N).val.app U)
          (primitiveQuotientFiniteTensorSection l L M j W n
            ((integralScalarReduction l E L ι W n).obj N) U w
            (integralScalarTensorSection l E L ι W n N U v x)) =
          integralScalarTensorSection l E M (j.comp ι) W n N U
            (((integralScalarQuotientSheafMap l L M j W n).hom.app U v) * w) x) ∧
      ∀ n : ℕ,
        Functor.associator (unrestrictedIntegralReductionFunctor l E W n)
            (primitiveQuotientFiniteScalarModel l E L ι W n).E
            (primitiveQuotientFiniteScalarModel l L M j W n).E ≪≫
          Functor.isoWhiskerLeft (unrestrictedIntegralReductionFunctor l E W n) (c n) ≪≫
          aEM n =
        Functor.isoWhiskerRight (aEL n)
            (primitiveQuotientFiniteScalarModel l L M j W n).E ≪≫ b n := by
  let aEL := quotientAssociation l E L ι W
  let aEM := quotientAssociation l E M (j.comp ι) W
  let c (n : ℕ) := PrimitiveOrdinary.comp (finiteScalarComp l E L ι M j W n)
    (finiteOrdinary l E L ι W n) (finiteOrdinary l L M j W n)
    (finiteOrdinary l E M (j.comp ι) W n)
  let b (n : ℕ) :=
    Functor.isoWhiskerRight (aEL n).symm (primitiveQuotientFiniteScalarModel l L M j W n).E ≪≫
      Functor.associator (unrestrictedIntegralReductionFunctor l E W n)
        (primitiveQuotientFiniteScalarModel l E L ι W n).E
        (primitiveQuotientFiniteScalarModel l L M j W n).E ≪≫
      Functor.isoWhiskerLeft (unrestrictedIntegralReductionFunctor l E W n) (c n) ≪≫ aEM n
  refine ⟨aEL, aEM, c, b, quotientAssociation_tmul l E L ι W,
    quotientAssociation_tmul l E M (j.comp ι) W, ?_, ?_, ?_⟩
  · intro n N U v w x
    exact (PrimitiveOrdinary.comp_tmul (finiteScalarComp l E L ι M j W n)
      (finiteOrdinary l E L ι W n) (finiteOrdinary l L M j W n)
      (finiteOrdinary l E M (j.comp ι) W n) N U w v x).trans
        (by rw [mul_comm]; rfl)
  · intro n N U v w x
    have ha := quotientAssociation_tmul l E L ι W n N U 1 v x
    rw [map_one, one_mul] at ha
    have hi : ((aEL n).inv.app N).val.app U
        (integralScalarTensorSection l E L ι W n N U v x) =
      primitiveQuotientFiniteTensorSection l E L ι W n
        ((unrestrictedIntegralReductionFunctor l E W n).obj N) U v
        (unrestrictedIntegralTensorSection l E W n N U 1 x) := by
      rw [← ha]
      change (((aEL n).hom.app N ≫ (aEL n).inv.app N).val.app U) _ = _
      rw [Iso.hom_inv_id_app]
      rfl
    change ((aEM n).hom.app N).val.app U
      (((c n).hom.app _).val.app U
        (((finiteOrdinary l L M j W n).E.map ((aEL n).inv.app N)).val.app U
          (PrimitiveOrdinary.tmul (finiteOrdinary l L M j W n)
            ((integralScalarReduction l E L ι W n).obj N) U w
            (integralScalarTensorSection l E L ι W n N U v x)))) = _
    have hm := PrimitiveOrdinary.map_tmul (finiteOrdinary l L M j W n)
      ((aEL n).inv.app N) U w (integralScalarTensorSection l E L ι W n N U v x)
    have hm' := congrArg (fun y ↦ ((aEM n).hom.app N).val.app U
      (((c n).hom.app _).val.app U y)) hm
    apply hm'.trans
    have hi' := congrArg (fun y ↦ ((aEM n).hom.app N).val.app U
      (((c n).hom.app _).val.app U
        (PrimitiveOrdinary.tmul (finiteOrdinary l L M j W n)
          ((unrestrictedIntegralReductionFunctor l E W n ⋙
            (finiteOrdinary l E L ι W n).E).obj N) U w y))) hi
    apply hi'.trans
    have hc := PrimitiveOrdinary.comp_tmul (finiteScalarComp l E L ι M j W n)
      (finiteOrdinary l E L ι W n) (finiteOrdinary l L M j W n)
      (finiteOrdinary l E M (j.comp ι) W n)
      ((unrestrictedIntegralReductionFunctor l E W n).obj N) U w v
      (unrestrictedIntegralTensorSection l E W n N U 1 x)
    apply (congrArg (fun y ↦ ((aEM n).hom.app N).val.app U y) hc).trans
    have hq := quotientAssociation_tmul l E M (j.comp ι) W n N U 1
      (w * (integralScalarQuotientSheafMap l L M j W n).hom.app U v) x
    rw [map_one, one_mul] at hq
    exact hq.trans (congrArg
      (fun z ↦ integralScalarTensorSection l E M (j.comp ι) W n N U z x) (mul_comm _ _))
  · intro n
    apply Iso.ext
    apply NatTrans.ext
    funext N
    dsimp only [b, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app]
    simp only [Category.id_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]
    have hid := ((primitiveQuotientFiniteScalarModel l L M j W n).E).map_id
      (((unrestrictedIntegralReductionFunctor l E W n) ⋙
        (primitiveQuotientFiniteScalarModel l E L ι W n).E).obj N)
    exact (Category.id_comp _).symm.trans ((congrArg (fun k ↦ k ≫
      (c n).hom.app ((unrestrictedIntegralReductionFunctor l E W n).obj N) ≫
        (aEM n).hom.app N) hid).symm)


private theorem finiteScalarId (W : Scheme.{t}) (n : ℕ) :
    integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n =
      𝟙 (integralCoefficientCommRingSheaf l E W n) := by
  have hq : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n = RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  unfold integralScalarQuotientSheafMap
  erw [hq]
  have hid : CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((RingHom.id _).comp (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)) =
      𝟙 (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) := by
    ext x
    rfl
  erw [hid]
  exact (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map_id _

private theorem finiteScalarId_apply (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) :
    (integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n).hom.app U s = s := by
  rw [finiteScalarId]
  rfl

/-- Equal coefficient fields use multiplication, including the unit square with
ordinary quotient reduction. This does not identify ambient completion with identity.
Source: Stacks 03EK, 0D6D
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof: multiplication sends s tensor x to sx, with inverse x to 1 tensor x.
The completion-to-finite identity map is ordinary reduction, so its unit comparison
sends s tensor x to the same quotient tensor. Both sides of the square multiply
the two finite coefficients. Balancing proves equality, naturally and in each degree. -/
theorem primitiveQuotientScalarUnit (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x)) :
    ∃ (a : ∀ n : ℕ,
        unrestrictedIntegralReductionFunctor l E W n ⋙
          (primitiveQuotientFiniteScalarModel l E E (AlgHom.id ℚ_[l] E) W n).E ≅
            integralScalarReduction l E E (AlgHom.id ℚ_[l] E) W n)
      (v : ∀ n : ℕ,
        (primitiveQuotientFiniteScalarModel l E E (AlgHom.id ℚ_[l] E) W n).E ≅
          𝟭 (integralOperationsFiniteModules l E W n))
      (w : ∀ n : ℕ,
        integralScalarReduction l E E (AlgHom.id ℚ_[l] E) W n ≅
          unrestrictedIntegralReductionFunctor l E W n),
      PrimitiveQuotientAssociation l E E (AlgHom.id ℚ_[l] E) W a ∧
      (∀ (n : ℕ) (N : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : N.val.obj U),
        (((v n).hom.app N).val.app U)
          (primitiveQuotientFiniteTensorSection l E E (AlgHom.id ℚ_[l] E) W n N U s x) =
            s • x) ∧
      (∀ (n : ℕ) (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : N.val.obj U),
        (((w n).hom.app N).val.app U)
          (integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) W n N U s x) =
            unrestrictedIntegralTensorSection l E W n N U s x) ∧
      ∀ n : ℕ, a n ≪≫ w n =
        Functor.isoWhiskerLeft (unrestrictedIntegralReductionFunctor l E W n) (v n) ≪≫
          Functor.rightUnitor (unrestrictedIntegralReductionFunctor l E W n) := by
  let a := quotientAssociation l E E (AlgHom.id ℚ_[l] E) W
  let v (n : ℕ) := PrimitiveOrdinary.unit (finiteScalarId l E W n)
    (finiteOrdinary l E E (AlgHom.id ℚ_[l] E) W n)
  let z (n : ℕ) :=
    Functor.isoWhiskerLeft (unrestrictedIntegralReductionFunctor l E W n) (v n) ≪≫
      Functor.rightUnitor (unrestrictedIntegralReductionFunctor l E W n)
  let w (n : ℕ) := (a n).symm ≪≫ z n
  refine ⟨a, v, w, quotientAssociation_tmul l E E (AlgHom.id ℚ_[l] E) W, ?_, ?_, ?_⟩
  · intro n N U s x
    exact PrimitiveOrdinary.unit_tmul (finiteScalarId l E W n)
      (finiteOrdinary l E E (AlgHom.id ℚ_[l] E) W n) N U s x
  · intro n N U s x
    have ha := quotientAssociation_tmul l E E (AlgHom.id ℚ_[l] E) W n N U s 1 x
    rw [finiteScalarId_apply, mul_one] at ha
    rw [← ha]
    change (((a n).hom.app N ≫ (w n).hom.app N).val.app U) _ = _
    have hw : (a n).hom.app N ≫ (w n).hom.app N = (z n).hom.app N := by
      dsimp only [w, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hw]
    change ((v n).hom.app _).val.app U
      (PrimitiveOrdinary.tmul (finiteOrdinary l E E (AlgHom.id ℚ_[l] E) W n)
        ((unrestrictedIntegralReductionFunctor l E W n).obj N) U 1
          (unrestrictedIntegralTensorSection l E W n N U s x)) = _
    dsimp only [v]
    exact (PrimitiveOrdinary.unit_tmul (finiteScalarId l E W n)
      (finiteOrdinary l E E (AlgHom.id ℚ_[l] E) W n) _ U 1
      (unrestrictedIntegralTensorSection l E W n N U s x)).trans (one_smul _ _)
  · intro n
    exact Iso.self_symm_id_assoc (a n) (z n)


/-- Primitive realization isomorphisms on the entire ambient derived categories,
with the fixed normalized Roos comparison and every simultaneous quotient
presentation. These are the interfaces whose `realization` fields are alpha
and beta; their normalization fields specify rho and rho composed with the
inverse of the strict association, respectively.

Source: Stacks 099N(2),(5), 06YS, 0G7E, 0D6D, 0941
(blueprint: lem-trf-primitive-quotient-realization-comparisons).
Proof:
1. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Change of
   rings preserves those properties at every quotient by
   lem-pur-kflat-change-of-rings. The calculus's reductionModel supplies one
   strict quotient presentation with the actual maps for all m greater than n.
2. Finite constant-coefficient inverse image is exact by
   prop-weil-pbc-proetale-constant-exact. By lem-coef-semilinear-derived-sections
   it computes whole-system inverse image termwise. Restrict the resulting
   tower to completed coefficients. The defining completed pullback is its
   Roos cone, so apply the fixed rho to this very tower. No infinite product
   passes through inverse image.
3. Construct the balanced association and inverse as in
   primitiveQuotientScalarAssociation. They commute with differentials and
   quotient transitions, giving one strict-system chain isomorphism.
4. The system tensor is componentwise on the vertical sequence site; therefore
   the levelwise K-flat reduction system is K-flat as a whole system. Its
   ordinary scalar extension computes derived extension. The association
   identifies its restricted tower with integralScalarTowerFunctor. Apply H
   to its inverse and then the fixed rho. This is beta with the orientation
   specified in IsIntegralComparisonScalarNormalized.
5. For E to L to M both associations multiply the same three coefficients;
   for equal fields use multiplication with inverse insertion of 1. All
   transitions are the actual reductions, so these identities are strict.
6. The formulas commute with every cochain map. Quotient tensors preserve
   quasi-isomorphisms of good inputs, and exact inverse image preserves them.
   Apply lem-pur-flat-roos-functor-descent and the fixed strict Roos comparison.
   This gives natural isomorphisms on all derived morphisms, independent of
   representatives through the specified comparisons. Exact countable
   products are lem-weil-proetale-countable-products-exact. -/
-- STATEMENT-DISPUTED: CoefficientReductionPresentation determines e only after finite
-- derived evaluations. These are conservative, but do not detect equality of morphisms.
-- Replacing e by reduction of a nontrivial automorphism with identity reductions preserves
-- the hypothesis and the generator-normalized q, but changes the required limit equation.
-- See report.md for the derived-complete, nonseparated Z_p-module counterexample.
theorem primitiveQuotientRealizationComparisons
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) ∧
      Nonempty (IntegralComparisonScalarModel l E L ι W SW ρW) := by
  exact ⟨primitiveQuotientPullbackModelExistence l E f _hlX _hlY SY ρX,
    primitiveQuotientScalarModelExistence l E L ι W _hlW SW ρW⟩

end WeilConjectures
