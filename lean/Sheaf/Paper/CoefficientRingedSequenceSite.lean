/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.CoefficientHomZeroClass
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntegralReductionTower
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.TowerEvaluationKInjective

/-! # The coefficient ringed sequence site and canonical functors

Source: Stacks Project, Tags 0941, 06YY, 079P and 07A6
(blueprint: def-coef-ringed-sequence-site).

## Main definitions

- `coefficientSequenceTopology`: the product sequence site with vertical covers.
- `coefficientSequenceCommRingSheaf`: the actual quotient coefficient ring sheaf.
- `coefficientSequenceModules`: module sheaves on this ringed site.
- `coefficientSequenceEvaluation`: exact restriction to the nth vertical slice.
- `coefficientSequenceLimit`: total derived limit after exact scalar restriction.
- `coefficientSequenceProjection`: its canonical, resolution-normalized projections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The vertical covering condition for a sequence site.
Source: Stacks 0941, sequence-site construction
(blueprint: def-coef-ringed-sequence-site). -/
def coefficientSequenceCovering {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (X : ℕ × C) (S : Sieve X) : Prop :=
  S.functorPullback (Prod.sectR X.1 C) ∈ J X.2

/-- The vertical covering condition satisfies the topology axioms.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the slice of the maximal sieve is maximal. For pullback along (h,f), the
vertical slice contains the pullback along f of the old vertical slice, so covering
stability and upward closure apply. For local character, test the supplied condition
on every vertical arrow in the covering slice and apply local character in J. -/
theorem coefficientSequenceTopologyAxioms {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (∀ X : ℕ × C, coefficientSequenceCovering J X ⊤) ∧
    (∀ {X Y : ℕ × C} {S : Sieve X} (f : Y ⟶ X),
      coefficientSequenceCovering J X S → coefficientSequenceCovering J Y (S.pullback f)) ∧
    (∀ {X : ℕ × C} {S : Sieve X}, coefficientSequenceCovering J X S →
      ∀ R : Sieve X,
        (∀ {Y : ℕ × C} {f : Y ⟶ X}, S f →
          coefficientSequenceCovering J Y (R.pullback f)) →
        coefficientSequenceCovering J X R) := by
  sorry

/-- The actual sequence topology, with covering determined by the vertical slice.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
def coefficientSequenceTopology {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) : GrothendieckTopology (ℕ × C) where
  sieves X := {S | coefficientSequenceCovering J X S}
  top_mem' := (coefficientSequenceTopologyAxioms J).1
  pullback_stable' := fun {_ _ _} f h ↦ (coefficientSequenceTopologyAxioms J).2.1 f h
  transitive' := fun {_ _} h R hh ↦
    (coefficientSequenceTopologyAxioms J).2.2 h R (fun {_ _} hf ↦ hh hf)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The same quotient transition with its commutative structure retained.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingTransition (n : ℕ) :
    integralCoefficientCommRingSheaf l E W (n + 1) ⟶
      integralCoefficientCommRingSheaf l E W n where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom
        ((integralCoefficientSheafTransition l E W n).hom.app U).hom
      naturality := fun {_ _} f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((integralCoefficientSheafTransition l E W n).hom.naturality f) }

/-- The commutative coefficient sequence, with precisely the recorded quotient maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingSystem :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (coefficientSequenceCommRingTransition l E W)

/-- The actual sectionwise commutative ring presheaf on the sequence site.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingPresheaf :
    (ℕ × W.ProEt)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} :=
  (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor ⋙ Functor.uncurry.obj
    (coefficientSequenceCommRingSystem l E W ⋙
      sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)})

/-- The commutative sequence ring is a sheaf for the vertical topology.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: glue in the recorded finite coefficient sheaves:
use the vertical covering slice to glue in B_n, then use separatedness on its
pullbacks to verify compatibility with every horizontal arrow. All ring operations
are preserved because they are preserved by the recorded coefficient restrictions. -/
theorem coefficientSequenceCommRingPresheaf_isSheaf :
    Presheaf.IsSheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingPresheaf l E W) := by
  sorry

/-- The same sequence ring sheaf with commutativity retained.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingSheaf :
    Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      CommRingCat.{max u (t + 1)} :=
  ⟨coefficientSequenceCommRingPresheaf l E W,
    coefficientSequenceCommRingPresheaf_isSheaf l E W⟩

/-- Strict semilinear systems as modules over the actual commutative sequence ring.
The vertical sheaf condition is exactly the component sheaf condition; horizontal
restrictions are quotient-linear transition maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceModules :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E W))

/-- The unchanged sequence site fits in the coefficient universe.
Source: the size convention, Stacks 0941
(blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEssentiallySmall :
    EssentiallySmall.{max u (t + 1)} (ℕ × W.ProEt) := essentiallySmallSelf _

/-- The ordinary unbounded localization of strict coefficient systems.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceDerived :=
  @DerivedCategory (coefficientSequenceModules l E W) _ _ (HasDerivedCategory.standard _)

/-- The standard localization instance for strict coefficient-system modules.
Source: Stacks 05RU, 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceHasDerived :
    HasDerivedCategory (coefficientSequenceModules l E W) := HasDerivedCategory.standard _

/-- The standard localization at each finite coefficient ring.
Source: Stacks 05RU (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientFiniteHasDerived (n : ℕ) :
    HasDerivedCategory (SheafOfModules.{max u (t+1)}
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat RingCat)).obj (integralCoefficientCommRingSheaf l E W n))) :=
  HasDerivedCategory.standard _

/-- The recorded derived scalar extension with its finite-category codomain displayed.
Source: Stacks 06YY, 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteDerivedExtension (n : ℕ) :
    DerivedCategory (scalarReductionSource l E W) ⥤ normalizedDVRDerived l E W n :=
  scalarReductionDerivedExtension l E W n

/-- The recorded derived restriction with its finite-category domain displayed.
Source: Stacks 03CZ, 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteDerivedRestriction (n : ℕ) :
    normalizedDVRDerived l E W n ⥤ DerivedCategory (scalarReductionSource l E W) :=
  scalarReductionDerivedRestriction l E W n

/-- The existing scalar adjunction with its specified K-flat unit normalization.
Source: Stacks 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteAdjunction (n : ℕ) :
    coefficientFiniteDerivedExtension l E W n ⊣ coefficientFiniteDerivedRestriction l E W n :=
  (derivedScalarExtensionRestrictionAdjunction l E W n).choose

/-- Derived internal Hom taken on the actual sequence site before evaluation.
Source: Stacks 0A95 and 0941
(blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceInternalHom :
    (coefficientSequenceDerived l E W)ᵒᵖ × coefficientSequenceDerived l E W ⥤
      coefficientSequenceDerived l E W :=
  @derivedInternalHomOfUniverses.{t + 1, t, u}
    _ _ (coefficientSequenceTopology (Scheme.ProEt.topology W)) _ _
      (coefficientSequenceCommRingSheaf l E W) (HasDerivedCategory.standard _)

/-- The vertical inclusion is continuous, so restriction is coefficient evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: a sequence sheaf restricts to a sheaf on every vertical slice, by the defining
covering condition. The product-site sheaf condition checked above applies to set
sheaves as well as ring sheaves; this is exactly continuity. -/
theorem coefficientSequenceEvaluationContinuous (n : ℕ) :
    (Prod.sectR n W.ProEt).IsContinuous (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) := by
  sorry

/-- The canonical continuity structure on evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluationContinuousInstance (n : ℕ) :
    (Prod.sectR n W.ProEt).IsContinuous (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) :=
  coefficientSequenceEvaluationContinuous W n

/-- Evaluation of the actual sequence ring is the recorded finite coefficient sheaf.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the object at (n,U) is B_n(U). Its vertical restriction is B_n(f), since the
horizontal quotient along the identity is the identity. Functor extensionality
identifies the underlying presheaves; sheaf-condition proofs are irrelevant. -/
theorem coefficientSequenceEvaluationRing_eq (n : ℕ) :
    ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (Scheme.ProEt.topology W) (coefficientSequenceTopology (Scheme.ProEt.topology W))).obj
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (coefficientSequenceCommRingSheaf l E W)) = integralCoefficientSheaf l E W n := by
  sorry

/-- Evaluation of a strict coefficient system, with the canonical ring identification.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceEvaluation (n : ℕ) :
    coefficientSequenceModules l E W ⥤ normalizedDVRModules l E W n :=
  SheafOfModules.pushforward (F := Prod.sectR n W.ProEt)
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)

/-- Componentwise exactness of coefficient evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: kernels of module presheaves are sectionwise; cokernels are their sectionwise
cokernels followed by sheafification. Vertical gluing computes the same sheafification
at each level. Hence both kernel and cokernel comparisons are isomorphisms at every
level, and the additive evaluation functor preserves finite limits and colimits. -/
theorem coefficientSequenceEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientSequenceEvaluation l E W n) ∧
      PreservesFiniteColimits (coefficientSequenceEvaluation l E W n) := by
  sorry

/-- The finite-limit part of componentwise exact evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientSequenceEvaluation l E W n) :=
  (coefficientSequenceEvaluation_exact l E W n).1

/-- The finite-colimit part of componentwise exact evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientSequenceEvaluation l E W n) :=
  (coefficientSequenceEvaluation_exact l E W n).2

/-- Evaluation is additive because addition of module maps is componentwise.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: both sides of preservation of addition have at (n,U) the sum of the same
underlying linear maps. Module-sheaf morphism extensionality gives equality. -/
theorem coefficientSequenceEvaluation_additive (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).Additive := by
  sorry

/-- The additive structure of canonical evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_additiveInstance (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).Additive :=
  coefficientSequenceEvaluation_additive l E W n

/-- Ordinary derived evaluation descended from exact sequence evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceDerivedEvaluation (n : ℕ) :
    coefficientSequenceDerived l E W ⥤ normalizedDVRDerived l E W n :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  (coefficientSequenceEvaluation l E W n).mapDerivedCategory

/-- Evaluation retains the actual underlying abelian section object.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: unfold the continuous module pushforward. Scalar restriction changes the
module action only, so forgetting the action gives exactly the section at (n,U). -/
theorem coefficientSequenceEvaluationAb_eq
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    ((coefficientSequenceEvaluation l E W n).obj M).val.presheaf.obj U =
      M.val.presheaf.obj (op (n, U.unop)) := by
  sorry

/-- Restricting a finite evaluation retains the same underlying abelian sections.
Source: Stacks 0941, 03CZ (blueprint: def-coef-ringed-sequence-site).
Proof: the finite quotient restriction leaves the abelian presheaf unchanged.
Then apply the preceding evaluation equality. -/
theorem coefficientSequenceRestrictedEvaluationAb_eq
    (M : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ) :
    ((normalizedDVRModuleRes l E W h).obj
      ((coefficientSequenceEvaluation l E W n).obj M)).val.presheaf.obj U =
        M.val.presheaf.obj (op (n, U.unop)) := by
  sorry

/-- The actual quotient transition, characterized on every section of every system.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the horizontal restriction in the module presheaf is linear over B_m with
its target action restricted by B_m→B_n. Its site naturality gives a module-sheaf
map, and naturality in the input module gives the displayed transformation.
Extensionality on all sections proves uniqueness. -/
theorem coefficientSequenceTransition_exists {m n : ℕ} (h : n ≤ m) :
    ∃! τ : coefficientSequenceEvaluation l E W m ⟶
      coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h,
      ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ),
        eqToHom (coefficientSequenceEvaluationAb_eq l E W M m U).symm ≫
          (forget₂ (ModuleCat.{max u (t+1)}
            ((integralCoefficientSheaf l E W m).obj.obj U))
              AddCommGrpCat.{max u (t+1)}).map ((τ.app M).val.app U) ≫
          eqToHom (coefficientSequenceRestrictedEvaluationAb_eq l E W M h U) =
        M.val.presheaf.map
          ((Prod.mkHom (homOfLE h) (𝟙 U.unop) : (n, U.unop) ⟶ (m, U.unop))).op := by
  sorry

/-- The canonical quotient transition, chosen by its unique actual restriction formula.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceTransition {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceEvaluation l E W m ⟶
      coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h :=
  (coefficientSequenceTransition_exists l E W h).exists.choose

/-- The same transition descended to the ordinary derived system category.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceDerivedTransition {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedEvaluation l E W m ⟶
      coefficientSequenceDerivedEvaluation l E W n ⋙ normalizedDVRRes l E W h :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W m)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (ComplexShape.up ℤ))
    _ _ (coefficientSequenceEvaluation l E W m).mapDerivedCategory
    ((coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h).mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (ComplexShape.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (normalizedDVRModuleRes l E W h)).hom

/-- Normalization of an actual derived semilinear system, using the dependency's
universal derived tensor/restriction criterion for its specified transitions.
Source: Stacks 0941, normalized coefficient systems
(blueprint: def-coef-ringed-sequence-site). -/
def IsNormalizedCoefficientSequence (N : coefficientSequenceDerived l E W) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (P : normalizedDVRDerived l E W n),
    Function.Bijective
      (fun f : (coefficientSequenceDerivedEvaluation l E W n).obj N ⟶ P ↦
        (coefficientSequenceDerivedTransition l E W h).app N ≫
          (normalizedDVRRes l E W h).map f)

/-- Exact restriction of scalars as an actual strict tower, with unchanged sections.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: restrict the action at n by the actual completed coefficient projection.
The limit cone equations make every horizontal restriction completed-linear.
Use the original module-presheaf restrictions for the tower arrows and original
component maps for morphisms. Their functor equations are those of the presheaves.
Extensionality on objects and section maps proves uniqueness of this functor. -/
theorem coefficientSequenceRestriction_exists :
    ∃! U : coefficientSequenceModules l E W ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource l E W),
      (∀ (M : coefficientSequenceModules l E W) (n : ℕ),
        (U.obj M).obj (op n) = (scalarReductionRestriction l E W n).obj
          ((coefficientSequenceEvaluation l E W n).obj M)) ∧
      (∀ (M : coefficientSequenceModules l E W) (m n : ℕ) (h : n ≤ m)
        (V : W.ProEtᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op m)).val.obj V ↦
          (((U.obj M).map (homOfLE h).op).val.app V) x)
          (fun x : M.val.obj (op (m, V.unop)) ↦
            M.val.map
        (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x)) ∧
      (∀ {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ)
        (V : W.ProEtᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op n)).val.obj V ↦
          (((U.map f).app (op n)).val.app V) x)
          (fun x : M.val.obj (op (n, V.unop)) ↦ f.val.app (op (n, V.unop)) x)) := by
  sorry

/-- Termwise restriction is fixed by the actual quotient projections and section maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceRestriction : coefficientSequenceModules l E W ⥤
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  (coefficientSequenceRestriction_exists l E W).exists.choose

/-- Exactness of termwise restriction: underlying abelian sheaves do not change.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: kernels and cokernels are computed levelwise in the system category and
in the constant-coefficient tower category. Restriction changes only the scalar
action, so preserves these computations and componentwise addition. -/
theorem coefficientSequenceRestriction_exact :
    (coefficientSequenceRestriction l E W).Additive ∧
      PreservesFiniteLimits (coefficientSequenceRestriction l E W) ∧
      PreservesFiniteColimits (coefficientSequenceRestriction l E W) := by
  sorry

/-- Additivity of exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_additive :
    (coefficientSequenceRestriction l E W).Additive :=
  (coefficientSequenceRestriction_exact l E W).1

/-- Finite-limit preservation for exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_limits :
    PreservesFiniteLimits (coefficientSequenceRestriction l E W) :=
  (coefficientSequenceRestriction_exact l E W).2.1

/-- Finite-colimit preservation for exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_colimits :
    PreservesFiniteColimits (coefficientSequenceRestriction l E W) :=
  (coefficientSequenceRestriction_exact l E W).2.2

/-- The standard unbounded derived category of completed-coefficient towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceRestrictedDerived :=
  @DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E W) _ _ (HasDerivedCategory.standard _)

/-- The exact functor U_W on ordinary unbounded derived system categories.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceDerivedRestriction :
    coefficientSequenceDerived l E W ⥤ coefficientSequenceRestrictedDerived l E W :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  (coefficientSequenceRestriction l E W).mapDerivedCategory


/-- Constant-coefficient towers have simultaneous K-injective resolutions.
Source: Stacks 079P and 0941
(blueprint: def-coef-ringed-sequence-site).
Proof: identify towers with modules over the constant ring on the sequence site.
The vertical sheaf condition gives this equivalence sectionwise. Apply the
Grothendieck module-sheaf theorem and transport functorial K-injective resolutions
through the exact equivalence. -/
theorem coefficientConstantTowers_haveKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ scalarReductionSource l E W) := by
  sorry

/-- The simultaneous resolution instance for the actual constant-coefficient towers.
Source: Stacks 079P and 0941
(blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientConstantTowersKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  coefficientConstantTowers_haveKInjectives l E W

/-- The standard unbounded localization of constant coefficient towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientConstantTowerDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  HasDerivedCategory.standard _

/-- Inverse limit is additive.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: its limit projection at every level sends a sum of tower maps to the sum
of the corresponding module maps. The projections jointly determine the limit map. -/
theorem coefficientConstantTowerLimit_additive :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).Additive := by
  sorry

/-- The additive structure on the ordinary inverse-limit functor.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientConstantTowerLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).Additive :=
  coefficientConstantTowerLimit_additive l E W

/-- Canonical total inverse limit of strict completed-coefficient towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerLimit :
    coefficientSequenceRestrictedDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).rightDerivedFunctor

/-- The specified total limit after exact termwise scalar restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceLimit :
    coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerLimit l E W

/-- The exact evaluation of a constant-coefficient derived tower.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerEvaluation (n : ℕ) :
    coefficientSequenceRestrictedDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory

/-- The localization comparison for exact constant-tower evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientConstantTowerEvaluationFactors (n : ℕ) :=
  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategoryFactors

/-- Actual total-limit projections, characterized on simultaneous K-injective towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: apply the ordinary limit projection to a K-injective tower resolution.
Exact evaluation identifies its localization with the derived evaluation. The
right-derived universal property descends these natural chain maps; every object
has a K-injective representative, so the normalization determines the map uniquely. -/
theorem coefficientConstantTowerProjection_exists (n : ℕ) :
    ∃! π : coefficientConstantTowerLimit l E W ⟶ coefficientConstantTowerEvaluation l E W n,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective],
        π.app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I =
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (ComplexShape.up ℤ)).app I) := by
  sorry

/-- Canonical total-limit projection, not a lift selected after evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerProjection (n : ℕ) :=
  (coefficientConstantTowerProjection_exists l E W n).choose

/-- The actual derived global sections on completed coefficients, with displayed categories.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralSections :
    DerivedCategory (scalarReductionSource l E W) ⥤
      @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  coefficientGlobalSections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- The actual derived global sections at a positive finite coefficient level.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteSections (n : ℕ) :
    normalizedDVRDerived l E W n ⥤
      @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  coefficientGlobalSections.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)

/-- Integral global derived Hom, retaining the full mapping complex.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralGlobalHom :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      DerivedCategory (scalarReductionSource l E W) ⥤
        @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
      (completedIntegralCommRingSheafUnrestricted l E W) (HasDerivedCategory.standard _) ⋙
    coefficientIntegralSections l E W

/-- Finite global derived Hom, retaining the full mapping complex.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteGlobalHom (n : ℕ) :
    (normalizedDVRDerived l E W n)ᵒᵖ × normalizedDVRDerived l E W n ⥤
        @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (integralCoefficientCommRingSheaf l E W n)))
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
      (integralCoefficientCommRingSheaf l E W n) (HasDerivedCategory.standard _) ⋙
    coefficientFiniteSections l E W n

/-- The integral derived internal-Hom bifunctor used in the calculus.
Source: Stacks 0A95 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralInternalHom :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      DerivedCategory (scalarReductionSource l E W) ⥤
        DerivedCategory (scalarReductionSource l E W) :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
    (completedIntegralCommRingSheafUnrestricted l E W) (HasDerivedCategory.standard _)

/-- The finite derived internal-Hom bifunctor used in the calculus.
Source: Stacks 0A95 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteInternalHom (n : ℕ) :
    (normalizedDVRDerived l E W n)ᵒᵖ × normalizedDVRDerived l E W n ⥤
      normalizedDVRDerived l E W n :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
    (integralCoefficientCommRingSheaf l E W n) (HasDerivedCategory.standard _)

/-- Restriction followed by evaluation agrees with actual scalar restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the object equality is the first characterization of coefficientSequenceRestriction.
The morphism equality is its sectionwise characterization. Module-sheaf extensionality
and functor extensionality give the asserted equality, including the specified maps. -/
theorem coefficientSequenceRestriction_evaluation (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
    coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n := by
  sorry

/-- The canonical derived identification of restricted evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientRestrictedEvaluationIso (n : ℕ) :
    coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerEvaluation l E W n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := (scalarReductionRestriction_exact l E W n).1
  letI := (scalarReductionRestriction_exact l E W n).2
  (Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (scalarReductionRestriction l E W n)

/-- The actual projection L N to the restricted nth coefficient component.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceProjection (n : ℕ) :
    coefficientSequenceLimit l E W ⟶
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceDerivedRestriction l E W)
    (coefficientConstantTowerProjection l E W n) ≫
    (coefficientRestrictedEvaluationIso l E W n).hom

end WeilConjectures
