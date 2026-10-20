/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.PbcCompletedPullbackActual
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.KFlatRingedToposPullback
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.SystemLevelLeftExtension
/-!
# Derived extension from a coefficient level
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Indices in this module are Zheng's nonnegative indices: `n` denotes the paper node's
positive level `n + 1`. No normalization or cartesianness is imposed on a system.
The auxiliary declarations construct the actual strict systems and their evaluations;
the final package records the constructions, universal properties and all coherence laws.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
/-- The constant quotient coefficient sheaf. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientQuotientSheaf (O : Type w) [CommRing O] (ell : O) (n : ℕ) :
    Sheaf J CommRingCat.{w} :=
  (constantSheaf J CommRingCat.{w}).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))
/-- The quotient-induced map, with no arbitrary ring-sheaf map parameter.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientQuotientMap (O : Type w) [CommRing O] (ell : O)
    {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientSheaf (J := J) O ell m ⟶ coefficientQuotientSheaf (J := J) O ell n :=
  (constantSheaf J CommRingCat.{w}).map
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))))
/-- Modules at level `n+1`, using the recorded general ringed-site category.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientLevelModules (O : Type w) [CommRing O] (ell : O) (n : ℕ) :=
  ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      (coefficientQuotientSheaf (J := J) O ell n))
/-- Scalar restriction along the actual coefficient quotient.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03CZ
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientRestriction (O : Type w) [CommRing O] (ell : O)
    {m n : ℕ} (h : n ≤ m) :
    coefficientLevelModules (J := J) O ell n ⥤ coefficientLevelModules (J := J) O ell m :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (coefficientQuotientMap (J := J) O ell h))
/-- Strict semilinear systems; only successive transitions are data.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientSystem (O : Type w) [CommRing O] (ell : O) where
  level : ∀ n : ℕ, coefficientLevelModules (J := J) O ell n
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (coefficientRestriction (J := J) O ell (Nat.le_succ n)).obj (level n)
variable {O : Type w} [CommRing O] {ell : O}
/-- Componentwise morphisms commuting with all transitions.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientSystem.Hom (M N : CoefficientSystem (J := J) O ell) where
  app : ∀ n : ℕ, M.level n ⟶ N.level n
  comm : ∀ n : ℕ, app (n + 1) ≫ N.transition n =
    M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map (app n)
/-- Identity families commute with transitions. Source: Zheng, Construction 4.1, p. 21.
Proof: the two composites are the same transition, by the identity laws and functoriality
of scalar restriction (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_id_comm (M : CoefficientSystem (J := J) O ell) (n : ℕ) :
    𝟙 (M.level (n + 1)) ≫ M.transition n =
      M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map (𝟙 _) := by
  have := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  have := ‹HasSheafify J AddCommGrpCat.{w}›
  simp
/-- Composable compatible families remain compatible. Source: Zheng, Construction 4.1, p. 21.
Proof: substitute the two commuting squares, then use associativity and preservation
of composition by restriction (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_comp_comm {M N P : CoefficientSystem (J := J) O ell}
    (f : M.Hom N) (g : N.Hom P) (n : ℕ) :
    (f.app (n + 1) ≫ g.app (n + 1)) ≫ P.transition n =
      M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map
        (f.app n ≫ g.app n) := by
  have := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  have := ‹HasSheafify J AddCommGrpCat.{w}›
  rw [Category.assoc, g.comm, ← Category.assoc, f.comm]
  simp only [Category.assoc, Functor.map_comp]
/-- Componentwise identity. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.identity (M : CoefficientSystem (J := J) O ell) : M.Hom M :=
  ⟨fun _n ↦ 𝟙 _, coefficientSystem_id_comm M⟩
/-- Componentwise composition. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.Hom.compose {M N P : CoefficientSystem (J := J) O ell}
    (f : M.Hom N) (g : N.Hom P) : M.Hom P :=
  ⟨fun n ↦ f.app n ≫ g.app n, coefficientSystem_comp_comm f g⟩
/-- Category laws for the displayed componentwise operations.
Source: Zheng, Construction 4.1, p. 21.
Proof: equality of these structures is equality of their components; identity and
associativity hold in each module category. Proof fields are irrelevant
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_category_laws :
    (∀ (M N : CoefficientSystem (J := J) O ell) (f : M.Hom N),
      M.identity.compose f = f ∧ f.compose N.identity = f) ∧
    (∀ (M N P Q : CoefficientSystem (J := J) O ell)
      (f : M.Hom N) (g : N.Hom P) (h : P.Hom Q),
      (f.compose g).compose h = f.compose (g.compose h)) := by
  have ext {M N : CoefficientSystem (J := J) O ell} (f g : M.Hom N)
      (h : f.app = g.app) : f = g := by
    cases f
    cases g
    cases h
    rfl
  constructor
  · intro M N f
    constructor
    · apply ext
      funext n
      exact Category.id_comp (f.app n)
    · apply ext
      funext n
      exact Category.comp_id (f.app n)
  · intro M N P Q f g h
    apply ext
    funext n
    exact Category.assoc (f.app n) (g.app n) (h.app n)
/-- The category with precisely the declared objects and componentwise maps.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
instance coefficientSystemCategory : Category (CoefficientSystem (J := J) O ell) where
  Hom := CoefficientSystem.Hom
  id := CoefficientSystem.identity
  comp := CoefficientSystem.Hom.compose
  id_comp := fun f ↦ (coefficientSystem_category_laws.1 _ _ f).1
  comp_id := fun f ↦ (coefficientSystem_category_laws.1 _ _ f).2
  assoc := fun f g h ↦ coefficientSystem_category_laws.2 _ _ _ _ f g h
/-- Exact level evaluation, on its actual object and morphism data.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientEvaluation (n : ℕ) :
    CoefficientSystem (J := J) O ell ⥤ coefficientLevelModules (J := J) O ell n where
  obj M := M.level n
  map f := f.app n
/-- The additive structure is normalized by the jointly faithful evaluations.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.AbelianNormalized
    (a : Abelian (CoefficientSystem (J := J) O ell)) : Prop :=
  @id Prop (by
    letI := a
    exact ∀ n : ℕ, (coefficientEvaluation (J := J) (O := O) (ell := ell) n).Additive)
/-- The unique componentwise abelian structure.
Source: Zheng, Construction 4.1, p. 21.
Proof: add morphisms componentwise; restriction is additive so compatibility is preserved.
Take kernels and sheafified cokernels at each level; their universal properties induce
successive transitions and the componentwise universal properties. Finite biproducts
are componentwise, and monos and epis are normal at each level. This gives an abelian
category. Joint faithfulness of evaluation fixes addition; all remaining abelian fields
are properties, so the normalized structure is unique
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_abelian_exists :
    ∃! a : Abelian (CoefficientSystem (J := J) O ell),
      CoefficientSystem.AbelianNormalized a := by
  sorry
/-- The uniquely determined componentwise abelian structure, not an unspecified object.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
instance coefficientSystemAbelian : Abelian (CoefficientSystem (J := J) O ell) :=
  coefficientSystem_abelian_exists.exists.choose
/-- Evaluation is additive. Source: Zheng, Construction 4.1, p. 21.
Proof: apply the normalization in the unique abelian-structure theorem
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientEvaluation_additive (n : ℕ) :
    (coefficientEvaluation (J := J) (O := O) (ell := ell) n).Additive := by
  exact coefficientSystem_abelian_exists.exists.choose_spec n
attribute [instance] coefficientEvaluation_additive
/-- Evaluation is exact. Source: Zheng, Construction 4.1, p. 21.
Proof: kernels and cokernels in the constructed abelian category are componentwise;
finite biproducts and hence finite limits and colimits are componentwise as well
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) ∧
      PreservesFiniteColimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) := by
  sorry
variable [EssentiallySmall.{w} C]
variable {R R' : Sheaf J CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension respects identities. Source: Stacks Tag 03EK.
Proof: the sectionwise tensor map of the identity is the identity on every pure tensor;
sheafification preserves identity maps
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_map_id (φ : R ⟶ R')
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    changeOfRingsHom (φ) F (𝟙 F) =
      𝟙 (changeOfRings (φ) F) := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  unfold changeOfRingsHom changeOfRings
  convert (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R').obj)).map_id
      (changeOfRingsPresheaf φ F) using 1
  congr 1
  ext U x
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalars (φ.hom.app U).hom).map_id (F.val.obj U)) x

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension respects composition. Source: Stacks Tag 03EK.
Proof: on a tensor generator both composites apply the two module maps successively;
sheafify that equality (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_map_comp (φ : R ⟶ R')
    {F G H : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (f
      : F ⟶ G) (g : G ⟶ H) :
    changeOfRingsHom (φ) F (f ≫ g) =
      changeOfRingsHom (φ) F f ≫
        changeOfRingsHom (φ) G g := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  unfold changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  ext U x
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalars (φ.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)) x

/-- The recorded sheafified sectionwise scalar extension, on objects and maps.
Source: Stacks Tag 03EK; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteCoefficientTensor (φ : R ⟶ R') :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R') where
  obj := changeOfRings (φ)
  map := changeOfRingsHom (φ) _
  map_id := siteCoefficientTensor_map_id φ
  map_comp := siteCoefficientTensor_map_comp φ

set_option backward.isDefEq.respectTransparency false in
/-- The tensor functor is additive. Source: Stacks Tag 03EK.
Proof: the tensor map is additive in the module-map variable before sheafification, and
module sheafification is additive
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_additive (φ : R ⟶ R') :
    (siteCoefficientTensor (J := J) φ).Additive := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  have hscalar (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R').obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  constructor
  intro F G f g
  dsimp only [siteCoefficientTensor, changeOfRingsHom]
  rw [← CategoryTheory.Functor.map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add (f := f.val.app U) (g := g.val.app U)

attribute [instance] siteCoefficientTensor_additive

/-- The canonical tensor Hom correspondence is evaluated on the sheafification image of
`1 tensor x`. Source: Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def SiteCoefficientTensorAdjunctionNormalized (φ : R ⟶ R')
    (a : siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) : Prop :=
  ∀ (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (G : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R'))
    (f : (siteCoefficientTensor (J := J) φ).obj F ⟶ G) (U : Cᵒᵖ) (x : F.val.obj
      U),
    ((a.homEquiv F G) f).val.app U x = f.val.app U
      ((toSheafify J
        (changeOfRingsPresheaf (φ) F).presheaf).app U
          (((ModuleCat.extendRestrictScalarsAdj
            ((φ).hom.app U).hom).unit.app
              (F.val.obj U)) x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor adjunction, uniquely fixed by its action on local tensor generators.
Source: Stacks Tag 03D7.
Proof: take the ordinary sectionwise tensor/restriction Hom bijections and then the module
sheafification Hom bijection. Their composite has exactly the displayed normalization.
They are natural in both variables and mutually inverse. Pure tensors generate, and
sheafification is universal, so this normalization determines the adjunction uniquely
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensorAdj_exists (φ : R ⟶ R') :
    ∃! a : siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ),
        SiteCoefficientTensorAdjunctionNormalized φ a := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R'))
  obtain ⟨_, _, h⟩ := sheafRingDerivedCoefficientAdjunction φ
  obtain ⟨a, ha, _⟩ := h (siteCoefficientTensor φ) (fun _ ↦ rfl) (by
    intro F G f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  have hn : SiteCoefficientTensorAdjunctionNormalized φ a := by
    intro F G f U x
    have hx := ha F G f U x
    simp only [eqToHom_refl, Category.id_comp] at hx
    convert hx using 1
    rfl
  refine ⟨a, hn, ?_⟩
  intro b hb
  apply Adjunction.ext
  ext F U x
  have he : b.homEquiv F ((siteCoefficientTensor φ).obj F) (𝟙 _) =
      a.homEquiv F ((siteCoefficientTensor φ).obj F) (𝟙 _) := by
    ext V y
    rw [hb, hn]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at he
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) he) x

/-- The specified tensor/restriction adjunction, not a choice of an arbitrary map.
Source: Stacks Tag 03D7 (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteCoefficientTensorAdj (φ : R ⟶ R') :
    siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) :=
  (siteCoefficientTensorAdj_exists (J := J) φ).exists.choose

/-- Specialize the canonical site tensor functor to the actual coefficient quotient map.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03EK
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientTensor {m n : ℕ} (h : n ≤ m) :=
  siteCoefficientTensor (coefficientQuotientMap (J := J) O ell h)

/-- Specialize the normalized tensor adjunction to the coefficient quotient map.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientTensorAdj {m n : ℕ} (h : n ≤ m) :=
  siteCoefficientTensorAdj (coefficientQuotientMap (J := J) O ell h)

/-- Forgetting scalars after scalar restriction leaves the underlying additive sheaf
literally unchanged. This uses Mathlib's existing `toSheaf` and `restrictScalars`.
Source: Stacks Tag 03CZ (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteScalarUnderlyingIso (φ : R ⟶ R') :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) ⋙
      SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ≅
    SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R') :=
  Iso.refl _

/-- The underlying additive-sheaf map of the canonical scalar-extension unit.
Source: Stacks Tag 03D7 (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteTensorUnitUnderlying (φ : R ⟶ R')
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    (SheafOfModules.toSheaf _).obj F ⟶
      (SheafOfModules.toSheaf _).obj ((siteCoefficientTensor φ).obj F) :=
  (SheafOfModules.toSheaf _).map ((siteCoefficientTensorAdj φ).unit.app F) ≫
    (siteScalarUnderlyingIso φ).hom.app ((siteCoefficientTensor φ).obj F)

/-- A strict transition on the underlying additive sheaves, without coefficient-action
casts. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientTransitionUnderlying {m n : ℕ} (h : n ≤ m)
    (t : coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
      coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
        coefficientRestriction (J := J) O ell h)
    (M : CoefficientSystem (J := J) O ell) :
    (SheafOfModules.toSheaf _).obj (M.level m) ⟶
      (SheafOfModules.toSheaf _).obj (M.level n) :=
  (SheafOfModules.toSheaf _).map (t.app M) ≫
    (siteScalarUnderlyingIso (coefficientQuotientMap (J := J) O ell h)).hom.app (M.level n)

/-- Iterated transitions are fixed by the actual successor maps, identity and composition.
The forgetful functors are faithful, so these are equations of the actual transitions.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTransitionsNormalized
    (t : ∀ {m n : ℕ} (h : n ≤ m),
      coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
        coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
          coefficientRestriction (J := J) O ell h) : Prop :=
  (∀ n M, coefficientTransitionUnderlying (Nat.le_refl n) (t (Nat.le_refl n)) M = 𝟙 _) ∧
  (∀ n (M : CoefficientSystem (J := J) O ell),
    (t (Nat.le_succ n)).app M = M.transition n) ∧
  (∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
    coefficientTransitionUnderlying (h₂.trans h₁) (t (h₂.trans h₁)) M =
      coefficientTransitionUnderlying h₁ (t h₁) M ≫ coefficientTransitionUnderlying h₂ (t h₂) M)

/-- The tensor unit is the inverse of the canonical scalar-extension unit, on underlying
additive sheaves (faithful forgetting). Source: Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTensorUnitNormalized
    (tensorUnit : ∀ n, coefficientTensor (J := J) (O := O) (ell := ell) (Nat.le_refl n) ≅
      𝟭 (coefficientLevelModules (J := J) O ell n)) : Prop :=
  ∀ n F,
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell (Nat.le_refl n)) F ≫
      (SheafOfModules.toSheaf _).map ((tensorUnit n).hom.app F) = 𝟙 _

/-- The balanced associator is fixed on the generating scalar-extension units.
The scalar-unit formula above identifies this equation with the tensor-generator formula.
Source: Stacks Tags 03EK and 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTensorAssocNormalized
    (tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
      coefficientTensor (J := J) (O := O) (ell := ell) h₁ ⋙
        coefficientTensor (J := J) (O := O) (ell := ell) h₂ ≅
          coefficientTensor (J := J) (O := O) (ell := ell) (h₂.trans h₁)) : Prop :=
  ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) F,
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell h₁) F ≫
      siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell h₂)
        ((coefficientTensor (J := J) (O := O) (ell := ell) h₁).obj F) ≫
      (SheafOfModules.toSheaf _).map ((tensorAssoc h₁ h₂).hom.app F) =
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell (h₂.trans h₁)) F

section GeneralInterfaces

universe a b c a' b' c'

variable {A : Type a} {B : Type b} [Category.{a'} A] [Category.{b'} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]

/-- Universal scalar extension and its normalized derived adjunction for fixed functors.
The specialization below fixes these functors to the actual coefficient tensor and
restriction, and fixes K-flatness to the recorded sheaf tensor predicate.
Source: Stacks Tags 06YY and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure DerivedCoefficientScalarExtension (T : A ⥤ B) (R : B ⥤ A)
    [T.Additive] [R.Additive] (adj : T ⊣ R) (KFlat : CochainComplex A ℤ → Prop) where
  derived : DerivedCategory A ⥤ DerivedCategory B
  counit : DerivedCategory.Q ⋙ derived ⟶
    T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  isDerived : derived.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  computes : ∀ P, KFlat P → IsIso (counit.app P)
  restriction : DerivedCategory B ⥤ DerivedCategory A
  restrictionFactors : DerivedCategory.Q ⋙ restriction ≅
    R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  derivedAdj : derived ⊣ restriction
  transpose : ∀ P K (f : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ K),
    derivedAdj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (counit.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          P K f) ≫ restrictionFactors.inv.app K

variable {S : Type c} [Category.{c'} S] [Abelian S] [HasDerivedCategory.{d} S]
  {M : ℕ → Type a} [∀ n, Category.{a'} (M n)] [∀ n, Abelian (M n)]
  [∀ n, HasDerivedCategory.{d} (M n)]
  (e : ∀ n, S ⥤ M n) [∀ n, (e n).Additive]
  (r : ∀ {m n : ℕ}, n ≤ m → M n ⥤ M m) [∀ m n (h : n ≤ m), (r h).Additive]
  (T : ∀ {m n : ℕ}, n ≤ m → M m ⥤ M n) [∀ m n (h : n ≤ m), (T h).Additive]
  (aTensor : ∀ {m n : ℕ} (h : n ≤ m), T h ⊣ r h)
  (KFlat : ∀ n, CochainComplex (M n) ℤ → Prop) (Flat : ∀ n, M n → Prop)
  (TransitionsNormalized : (∀ {m n : ℕ} (h : n ≤ m), e m ⟶ e n ⋙ r h) → Prop)
  (TensorUnitNormalized : (∀ n, T (Nat.le_refl n) ≅ 𝟭 (M n)) → Prop)
  (TensorAssocNormalized :
    (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m), T h₁ ⋙ T h₂ ≅ T (h₂.trans h₁)) → Prop)

/-- The complete extension, strict representative, index coherence and mate equations.
The parameters are specialized to concrete coefficient systems in
`CoefficientEvaluationDerivedPackage`; they are not hypotheses of the final theorem.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientEvaluationExtensionData where
  strictTransition : ∀ {m n : ℕ} (h : n ≤ m),
    e m ⟶
      e n ⋙
        r h
  transitionsNormalized : TransitionsNormalized strictTransition
  scalar : ∀ {m n : ℕ} (h : n ≤ m), DerivedCoefficientScalarExtension (T h) (r h) (aTensor h)
    (KFlat m)
  extension : ∀ n, M n ⥤ S
  [extensionAdditive : ∀ n, (extension n).Additive]
  adj : ∀ n, extension n ⊣ e n
  below : ∀ {n q} (h : q ≤ n), extension n 
    ⋙ e q ≅ (T h)
  above : ∀ n q, n < q → ∀ F, IsZero ((e q).obj ((extension n).obj F))
  hom_formula : ∀ {n q} (h : q ≤ n) F M (f : (extension n).obj F ⟶ M),
    ((aTensor h).homEquiv F ((e q).obj M)) ((below
      h).inv.app F ≫ (e q).map f) =
      ((adj n).homEquiv F M f) ≫ (strictTransition h).app M
  evaluation : ∀ n, DerivedCategory (S) ⥤
    DerivedCategory (M n)
  evaluationFactors : ∀ n, DerivedCategory.Q ⋙ evaluation n ≅
    (e n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  derivedExtension : ∀ n, DerivedCategory (M n) ⥤
    DerivedCategory (S)
  counit : ∀ n, DerivedCategory.Q ⋙ derivedExtension n ⟶
    (extension n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  isDerived : ∀ n, (derivedExtension n).IsLeftDerivedFunctor (counit n)
    (HomologicalComplex.quasiIso (M n)
      (ComplexShape.up ℤ))
  computes : ∀ n P,
    KFlat n P →
    (∀ i, Flat n (P.X i)) →
      IsIso ((counit n).app P)
  derivedAdj : ∀ n, derivedExtension n ⊣ evaluation n
  transpose : ∀ n P K
      (f : ((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ K),
    (derivedAdj n).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      ((counit n).app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map (((adj n).mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          P K f) ≫ (evaluationFactors n).inv.app K
  derivedBelow : ∀ {n q} (h : q ≤ n),
    derivedExtension n ⋙ evaluation q ≅ (scalar h).derived
  derivedAbove : ∀ n q, n < q → ∀ N, IsZero ((evaluation q).obj ((derivedExtension n).obj N))
  transition : ∀ {m n} (h : n ≤ m),
    evaluation m ⟶ evaluation n ⋙ (scalar h).restriction
  transition_rep : ∀ {m n} (h : n ≤ m) K,
    (transition h).app (DerivedCategory.Q.obj K) ≫
      (scalar h).restriction.map ((evaluationFactors n).hom.app K) ≫
      (scalar h).restrictionFactors.hom.app
        (((e n).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (evaluationFactors m).hom.app K ≫
        DerivedCategory.Q.map
          (((strictTransition h).mapHomologicalComplex (ComplexShape.up ℤ)).app K)
  sigma : ∀ {m n} (h : n ≤ m),
    (scalar h).derived ⋙ derivedExtension n ⟶ derivedExtension m
  mate : ∀ {m n} (h : n ≤ m) N M (f : (derivedExtension m).obj N ⟶ M),
    (derivedAdj n).homEquiv ((scalar h).derived.obj N) M ((sigma h).app N ≫ f) =
      (scalar h).derived.map ((derivedAdj m).homEquiv N M f) ≫
        ((scalar h).derivedAdj.homEquiv ((evaluation m).obj M) ((evaluation n).obj M)).symm
          ((transition h).app M)
  tensorUnit : ∀ n, (T (Nat.le_refl n)) ≅ 𝟭 _
  tensorUnit_normalized : TensorUnitNormalized tensorUnit
  tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (T h₁) ⋙ (T h₂) ≅ (T (h₂.trans h₁))
  tensorAssoc_normalized : TensorAssocNormalized tensorAssoc
  strictSigma : ∀ {m n} (h : n ≤ m),
    (T h) ⋙ extension n ⟶ extension m
  strictSigma_below : ∀ {m n q} (h : n ≤ m) (hq : q ≤ n) F,
    (below hq).inv.app ((T h).obj F) ≫
      (e q).map ((strictSigma h).app F) ≫ (below (hq.trans h)).hom.app F =
        (tensorAssoc h hq).hom.app F
  strictSigma_above : ∀ {m n q} (h : n ≤ m) (_hq : n < q) F,
    (e q).map ((strictSigma h).app F) = 0
  strictSigmaComplex : ∀ {m n} (h : n ≤ m) P,
    ((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((T h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    ((extension m).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  strictSigmaComplex_f : ∀ {m n} (h : n ≤ m) P i,
    (strictSigmaComplex h P).f i = (strictSigma h).app (P.X i)
  sigma_rep : ∀ {m n} (h : n ≤ m) P,
    KFlat m P →
    (∀ i, Flat m (P.X i)) →
    (sigma h).app (DerivedCategory.Q.obj P) ≫ (counit m).app P =
      (derivedExtension n).map ((scalar h).counit.app P) ≫
        (counit n).app (((T h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strictSigmaComplex h P)
  tensorUnitComplex : ∀ n P,
    ((T (Nat.le_refl n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ≅ P
  tensorUnitComplex_f : ∀ n P i,
    ((tensorUnitComplex n P).hom).f i = (tensorUnit n).hom.app (P.X i)
  tensorAssocComplex : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    ((T h₂).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj
      (((T h₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
    ((T (h₂.trans h₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
  tensorAssocComplex_f : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P i,
    ((tensorAssocComplex h₁ h₂ P).hom).f i = (tensorAssoc h₁ h₂).hom.app (P.X i)
  derivedUnit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _
  derivedUnit_rep : ∀ n P,
    KFlat n P →
    (derivedUnit n).hom.app (DerivedCategory.Q.obj P) =
      (scalar (Nat.le_refl n)).counit.app P ≫
        DerivedCategory.Q.map (tensorUnitComplex n P).hom
  derivedAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (scalar h₁).derived ⋙ (scalar h₂).derived ≅ (scalar (h₂.trans h₁)).derived
  derivedAssoc_rep : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    KFlat l P →
    (∀ i, Flat l (P.X i)) →
    (derivedAssoc h₁ h₂).hom.app (DerivedCategory.Q.obj P) ≫
      (scalar (h₂.trans h₁)).counit.app P =
    (scalar h₂).derived.map ((scalar h₁).counit.app P) ≫
      (scalar h₂).counit.app
        (((T h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (tensorAssocComplex h₁ h₂ P).hom
  sigma_id : ∀ n N, (sigma (Nat.le_refl n)).app N =
    (derivedExtension n).map ((derivedUnit n).hom.app N)
  sigma_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) N,
    (sigma h₂).app ((scalar h₁).derived.obj N) ≫ (sigma h₁).app N =
      (derivedExtension n).map ((derivedAssoc h₁ h₂).hom.app N) ≫
        (sigma (h₂.trans h₁)).app N
  belowComplex : ∀ {n q} (h : q ≤ n) P,
    ((e q).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
    ((T h).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj P
  belowComplex_f : ∀ {n q} (h : q ≤ n) P i,
    ((belowComplex h P).hom).f i = (below h).hom.app (P.X i)
  derivedBelow_rep : ∀ {n q} (h : q ≤ n) P,
    (derivedBelow h).inv.app (DerivedCategory.Q.obj P) ≫
      (evaluation q).map ((counit n).app P) ≫
      (evaluationFactors q).hom.app
        (((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (belowComplex h P).hom = (scalar h).counit.app P
end GeneralInterfaces

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

/-- Specialize every ambient object and functor in the coherence interface to the
actual constant quotient rings, strict systems, scalar functors and recorded flatness
predicates. There are no arbitrary category, tensor or transition inputs.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev CoefficientEvaluationDerivedPackage :=
  CoefficientEvaluationExtensionData
    (coefficientEvaluation (J := J) (O := O) (ell := ell))
    (fun {_ _} h ↦ coefficientRestriction (J := J) O ell h)
    (fun {_ _} h ↦ coefficientTensor (J := J) (O := O) (ell := ell) h)
    (fun {_ _} h ↦ coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
    (fun n ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell n))
    (fun n ↦ IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell n))
    (CoefficientTransitionsNormalized (J := J) (O := O) (ell := ell))
    (CoefficientTensorUnitNormalized (J := J) (O := O) (ell := ell))
    (CoefficientTensorAssocNormalized (J := J) (O := O) (ell := ell))

/-- Derived extension from a single varying-coefficient level, with strict models,
coherent truncation maps, and their specified adjunction mates.
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Proof plan, following the seven steps of the node:
1. The strict systems are modules over the inverse coefficient-ring sheaf on the
projective-system topos. Kernels, cokernels and cohomology are componentwise, so a chain
map is a quasi-isomorphism exactly when all evaluated chain maps are quasi-isomorphisms
(lem-pur-system-level-left-extension). No normalization is imposed.
2. Define E_n by scalar extension below n and zero above n. From h:F→M_n, at q≤n use
the tensor-adjoint of the iterated transition composed with h, and above n use the unique
map from zero. Balanced tensor relations and the transition equations show these are
system maps. Conversely their component at n determines all components, giving the
natural inverse Hom bijections (lem-weil-pbc-ringed-topoi-module-adjunction). Units send
x to 1 tensor x and counits are the displayed transition-adjoints.
3. E_n is additive and acts termwise on differentials and maps. It preserves homotopies,
shifts and mapping cones. Resolve by flat-term K-flat complexes (lem-pc-kflat-resolution).
Termwise scalar extension preserves quasi-isomorphisms between them
(lem-pur-derived-change-of-rings); the evaluated zero complexes above n do too. Apply
lem-pur-left-derived-from-kflat-class to obtain the universal left derived pair and
its invertible comparison on this class. Evaluation gives the canonical derived tensor
below n and zero above n, with the comparison equation recorded in derivedBelow_rep.
4. Exact evaluation and scalar restriction have termwise derived functors
(lem-weil-pbc-exact-functor-derived-functor). Apply lem-pc-derived-adjoint-functors.
Normalize its bijection using lem-pc-pre-derived-adjoint-functors-general and
lem-weil-pbc-termwise-adjunction-homotopy: on a strict chain map its transpose is the
ordinary transpose followed by exact derived evaluation. Essential constancy and the
pointwise Kan bridge identify this with the universal comparison from step 3
(lem-pur-quasi-isos-saturated-triangulated,
lem-pur-resolving-class-essential-constancy,
lem-pur-left-derived-defined-pointwise-kan-bridge). The same argument normalizes the
derived scalar adjunction, including the unit x→1 tensor x and counit a tensor x→a h(x).
5. Define sigma by transposing the derived unit followed by the system transition,
first under scalar extension/restriction and then under LE_n/e_n. On a flat-term K-flat
representative, scalar extension is again flat-term K-flat
(lem-weil-pbc-ringed-pullback-preserves-kflat). The two transposes give the strict map
whose q-component is the balanced tensor associator for q≤n and zero for q>n. These
maps commute with differentials and transitions, including at q=n,n+1. The universal
comparison equation sigma_rep identifies the derived map with that actual chain map.
6. The unit tensor isomorphism inserts or removes 1. The associator sends
(c tensor (b tensor x)) to (c times the image of b) tensor x. These formulas are fixed
by tensorUnit_normalized and tensorAssoc_normalized. Thus the identity truncation map
is the identity. For three indices, the successive strict maps and the direct map
send every tensor generator to the same product of reduced coefficients. Above the
smallest index both sources are zero. The same computation with four coefficients
proves associator coherence. Pass through the universal comparisons to obtain sigma_id
and sigma_comp, with the canonical derived tensor unit and associator specified on
these representatives. No flatness of quotient-ring maps is used.
7. For f:LE_m N→M and its adjunct h, transpose f sigma twice. Naturality of the derived
system transition gives tau_M h. Its scalar transpose is C(h) followed by the transpose
of tau_M. This is exactly mate, for all derived morphisms, including fractions.
-/
theorem coefficientEvaluationDerivedLeftAdjoint
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O] :
    Nonempty (CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)) := by
  sorry
end SheafOfModules
