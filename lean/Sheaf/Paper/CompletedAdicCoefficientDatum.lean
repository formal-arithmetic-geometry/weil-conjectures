/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.CompleteCoefficientDatum
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Completed adic coefficient datum

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1239,
node def-weil-pbc-adic-coefficient-datum; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The finite coefficient sheaves are exactly the recorded sheafifications of continuous
functions on connected components. The ambient ring is their inverse limit. In particular,
no identification with the discrete constant coefficient category is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The Noetherian adic datum, including finiteness of every positive quotient.
The inherited fields give finite generation, additive torsion of A/I and perfectness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicCoefficientDatum (A : Type t) [CommRing A] extends CompleteCoefficientDatum A where
  quotientFinite : ∀ n : ℕ, Finite (A ⧸ ideal ^ (n + 1))

variable {A : Type t} [CommRing A]

/-- The positive quotient in the site's coefficient universe; n denotes exponent n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicQuotient (d : AdicCoefficientDatum A) (n : ℕ) :=
  ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))

/-- Quotient coefficients are finite, by the datum, also after changing universe.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_finite (d : AdicCoefficientDatum A) (n : ℕ) :
    Finite (completedAdicQuotient d n) :=
  letI := d.quotientFinite n
  inferInstance

/-- Each finite quotient has the discrete topology specified by the datum.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_topology (d : AdicCoefficientDatum A) (n : ℕ) :
    TopologicalSpace (completedAdicQuotient d n) := ⊥

/-- The quotient topology is discrete.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicQuotient_discrete (d : AdicCoefficientDatum A) (n : ℕ) :
    DiscreteTopology (completedAdicQuotient d n) := ⟨rfl⟩

/-- The actual finite coefficient sheaf from the recorded continuous-functions construction.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  ProEtale.finiteCoefficientRingSheaf T (completedAdicQuotient d n)

/-- Postcomposition by the quotient homomorphism on the coefficient presheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFinitePresheafStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d (n + 1)) ⟶
      ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d n) where
  app U := RingCat.ofHom
    ((RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))).compLeftContinuous
      (ConnectedComponents U.unop.left) (continuous_of_discreteTopology))
  naturality _ _ _ := by ext s; rfl

/-- Sheafify the specified postcomposition maps, retaining their actual formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicFiniteRing T d (n + 1) ⟶ completedAdicFiniteRing T d n :=
  (presheafToSheaf (ProEt.topology T) RingCat.{t + 1}).map
    (completedAdicFinitePresheafStep T d n)

/-- The strict inverse sequence of finite coefficient sheaves, with all longer composites.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicRingSystem (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  Functor.ofOpSequence (completedAdicFiniteStep T d)

/-- The completed coefficient ring sheaf A_T, the actual sheaf limit of the finite quotients.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    Sheaf (ProEt.topology T) RingCat.{t + 1} :=
  limit (completedAdicRingSystem T d)

/-- The coordinate projections of the completed coefficient sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicProjection (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicRing T d ⟶ completedAdicFiniteRing T d n :=
  limit.π (completedAdicRingSystem T d) (op n)

/-- The limit ring sheaf is commutative on sections.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: continuous functions into the commutative quotient rings commute pointwise;
sheafification preserves that equation locally. Each limit projection therefore identifies
the images of xy and yx. Evaluate the limit on U: its projections are jointly injective,
so xy=yx. This argument includes the zero ring and the empty site object. -/
theorem completedAdicRing_mul_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (U : T.ProEtᵒᵖ) (x y : (completedAdicRing T d).obj.obj U) : x * y = y * x := by
  sorry

/-- Retain the actual ring data of the limit and supply only its commutativity proof.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicCommRingStructure (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (U : T.ProEtᵒᵖ) : CommRing ((completedAdicRing T d).obj.obj U) :=
  { RingCat.ring _ with mul_comm := completedAdicRing_mul_comm T d U }

/-- The same completed coefficient presheaf with commutativity retained.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommPresheaf (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    T.ProEtᵒᵖ ⥤ CommRingCat.{t + 1} where
  obj U := @CommRingCat.of ((completedAdicRing T d).obj.obj U)
    (completedAdicCommRingStructure T d U)
  map {U V} f :=
    letI := completedAdicCommRingStructure T d U
    letI := completedAdicCommRingStructure T d V
    CommRingCat.ofHom ((completedAdicRing T d).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicRing T d).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicRing T d).obj.map_comp f g)

/-- The commutative ring sheaf with precisely the completed limit's underlying ring sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  ⟨completedAdicCommPresheaf T d,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (completedAdicRing T d).property⟩

/-- Module sheaves over A_T, with Mathlib's actual abelian structure.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev CompletedAdicModules (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  SheafOfModules.{t + 1} (completedAdicRing T d)

/-- The sheaf tensor structure over the completed commutative ring, not the constant ring.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicModules_monoidal (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    MonoidalCategory (CompletedAdicModules T d) :=
  SheafOfModules.monoidalCategory (completedAdicCommRing T d)

/-- Standard localization of the completed-coefficient module category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicModules_hasDerived (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    HasDerivedCategory (CompletedAdicModules T d) := HasDerivedCategory.standard _

/-- The category of strict inverse towers of A_T-module sheaves; index n means n+1.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev CompletedAdicTowers (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  ℕᵒᵖ ⥤ CompletedAdicModules T d

/-- Standard localization of the abelian category of strict towers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicTowers_hasDerived (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    HasDerivedCategory (CompletedAdicTowers T d) := HasDerivedCategory.standard _

/-- The coefficient module (P_(n+1))_T restricted along the actual limit projection.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteModule (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    CompletedAdicModules T d :=
  (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)).obj
    (SheafOfModules.unit (completedAdicFiniteRing T d n))

/-- The quotient ring map defines a unique A_T-linear map on the restricted unit modules.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: use q on every section. The limit cone identity pi_n=q*pi_(n+1) makes it linear;
its restrictions commute by naturality of q. Equality of all section functions determines
a sheaf morphism uniquely. -/
theorem completedAdicFiniteModuleStep_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) : ∃! q : completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n,
      ∀ (U : T.ProEtᵒᵖ) (s : (completedAdicFiniteRing T d (n + 1)).obj.obj U),
        q.val.app U s = (completedAdicFiniteStep T d n).hom.app U s := by
  sorry

/-- The canonically normalized transition of restricted quotient modules.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteModuleStep (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n :=
  (completedAdicFiniteModuleStep_exists T d n).exists.choose

/-- Ordinary tensor reductions as one strict tower-valued functor. Its transitions are
exactly tensor with the quotient maps, not independent choices at each level.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicOrdinaryTower (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    CompletedAdicModules T d ⥤ CompletedAdicTowers T d :=
  (Functor.ofOpSequence
    (X := fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.obj
      (completedAdicFiniteModule T d n))
    (fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.map
      (completedAdicFiniteModuleStep T d n))).flip

/-- The strict tensor tower is additive.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor is additive in the original module variable and addition of tower maps is
componentwise, so the assertion follows by evaluating at every level. -/
theorem completedAdicOrdinaryTower_additive (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    (completedAdicOrdinaryTower T d).Additive := by
  sorry

attribute [instance] completedAdicOrdinaryTower_additive

/-- Existence of the universal left derived reduction-tower pair, computed on K-flat models.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor distributes over the finite cone summands and respects shifts, so the
ordinary tower gives an exact functor on homotopy categories. Resolve every complex by
lem-pc-kflat-resolution. A quasi-isomorphism between K-flat complexes stays a
quasi-isomorphism after tensor with each quotient (lem-pur-derived-change-of-rings).
Tower cohomology is levelwise, so the entire tower map is a quasi-isomorphism. Apply
lem-pur-left-derived-from-kflat-class. Its counit is invertible on K-flat representatives,
which fixes the comparison with the stated strict quotient tower. -/
theorem completedAdicReduction_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃ (F : DerivedCategory (CompletedAdicModules T d) ⥤
        DerivedCategory (CompletedAdicTowers T d))
      (ε : DerivedCategory.Qh ⋙ F ⟶
        (completedAdicOrdinaryTower T d).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh),
      F.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (CompletedAdicModules T d) ℤ,
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

section DerivedReductionModels

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive] (P : CochainComplex B ℤ → Prop)

/-- A left derived functor, its counit, and its computation on the resolving class.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
structure DerivedReductionModelData where
  reduction : DerivedCategory B ⥤ DerivedCategory C
  counit : DerivedCategory.Qh ⋙ reduction ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  isLeftDerived : reduction.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso B (.up ℤ))
  isIso_counit : ∀ K : CochainComplex B ℤ, P K →
    IsIso (counit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))

/-- Retain the universally specified pair in one record, without changing either choice.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def derivedReductionModelDataOfExists
    (h : ∃ (LF : DerivedCategory B ⥤ DerivedCategory C)
      (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ)) ∧
        ∀ K : CochainComplex B ℤ, P K →
          IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))) :
    DerivedReductionModelData F P where
  reduction := h.choose
  counit := h.choose_spec.choose
  isLeftDerived := h.choose_spec.choose_spec.1
  isIso_counit := h.choose_spec.choose_spec.2

variable {F P}

/-- The comparison on complexes, including the localization factor isomorphisms.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def DerivedReductionModelData.complexCounit (D : DerivedReductionModelData F P)
    (K : CochainComplex B ℤ) :
    D.reduction.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  D.reduction.map ((DerivedCategory.quotientCompQhIso B).inv.app K) ≫
    D.counit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)

/-- Computation of the complex comparison on the resolving class.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data).
Proof: the homotopy counit is invertible by the computation law, and every other
factor is an image of a localization isomorphism. -/
theorem DerivedReductionModelData.complexCounit_isIso (D : DerivedReductionModelData F P)
    (K : CochainComplex B ℤ) (hK : P K) : IsIso (D.complexCounit K) := by
  have := D.isIso_counit K hK
  unfold DerivedReductionModelData.complexCounit
  infer_instance

/-- The right-derived comparison on a complex, with the localization factors retained.
Source: Stacks Tag 0941 (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def derivedLimitComplexComparison (L : C ⥤ B) [L.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (P : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      RF.obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((L).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((L).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app P) ≫
    δ.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (RF).map ((DerivedCategory.quotientCompQhIso _).hom.app P)


/-- The normalized completion unit on a resolving complex.
Source: Stacks Tags 06YY and 0941 (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def derivedCompletionModelUnit (D : DerivedReductionModelData F P)
    (L : C ⥤ B) [L.Additive] (RF : DerivedCategory C ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (u : 𝟭 B ⟶ F ⋙ L) (K : CochainComplex B ℤ) (hK : P K) :
    DerivedCategory.Q.obj K ⟶ RF.obj (D.reduction.obj (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app K) ≫
    derivedLimitComplexComparison L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      RF.map (@inv _ _ _ _ (D.complexCounit K) (D.complexCounit_isIso K hK))

end DerivedReductionModels

/-- The universal strict reduction pair over the completed coefficients.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
abbrev CompletedAdicReductionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  DerivedReductionModelData (completedAdicOrdinaryTower T d)
    (CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d))

/-- Bundle the already chosen universal pair. Its universal property determines it
up to its unique compatible isomorphism.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-reduction-model-data). -/
def completedAdicReductionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    CompletedAdicReductionData T d :=
  derivedReductionModelDataOfExists (completedAdicOrdinaryTower T d)
    (CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d))
    (completedAdicReduction_exists T d)

/-- The reduction tower functor, chosen from its universal derived pair. The universal
property and invertible K-flat counit determine it up to its unique comparison.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicReduction (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    DerivedCategory (CompletedAdicModules T d) ⥤ DerivedCategory (CompletedAdicTowers T d) :=
  (completedAdicReductionData T d).reduction

/-- Exact derived evaluation of strict towers, with every transition retained.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicEvaluation (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (CompletedAdicTowers T d) ⥤ DerivedCategory (CompletedAdicModules T d) :=
  ((CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj (op n)).mapDerivedCategory

/-- Derived finite reduction, regarded as an A_T-module by restriction of scalars.
It is evaluation of the universal strict reduction tower, hence computed by tensor on
K-flat representatives. Source: blueprint order 1239
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteReduction (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (CompletedAdicModules T d) ⥤ DerivedCategory (CompletedAdicModules T d) :=
  completedAdicReduction T d ⋙ completedAdicEvaluation T d n

/-- The finite coefficient sheaf has commutative sections.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: continuous functions into the commutative quotient ring commute pointwise.
The same equation holds locally after sheafification, and the sheaf's separatedness
makes it hold globally on each object. -/
theorem completedAdicFiniteRing_mul_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x y : (completedAdicFiniteRing T d n).obj.obj U) :
    x * y = y * x := by
  sorry

/-- Commutativity on the finite coefficient sheaf, with unchanged underlying ring data.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedAdicFiniteCommRingStructure (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) : CommRing ((completedAdicFiniteRing T d n).obj.obj U) :=
  { RingCat.ring _ with mul_comm := completedAdicFiniteRing_mul_comm T d n U }

/-- The existing finite coefficient presheaf with commutativity retained.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteCommPresheaf (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    T.ProEtᵒᵖ ⥤ CommRingCat.{t + 1} where
  obj U := @CommRingCat.of ((completedAdicFiniteRing T d n).obj.obj U)
    (completedAdicFiniteCommRingStructure T d n U)
  map {U V} f :=
    letI := completedAdicFiniteCommRingStructure T d n U
    letI := completedAdicFiniteCommRingStructure T d n V
    CommRingCat.ofHom ((completedAdicFiniteRing T d n).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicFiniteRing T d n).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedAdicFiniteRing T d n).obj.map_comp f g)

/-- The finite coefficient sheaf, now as commutative rings, with the same ring sheaf.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicFiniteCommRing (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  ⟨completedAdicFiniteCommPresheaf T d n,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (completedAdicFiniteRing T d n).property⟩

/-- The limit projection with commutativity retained, without changing its section maps.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicCommProjection (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicCommRing T d ⟶ completedAdicFiniteCommRing T d n where
  hom :=
    { app := fun U ↦
        letI := completedAdicCommRingStructure T d U
        letI := completedAdicFiniteCommRingStructure T d n U
        CommRingCat.ofHom ((completedAdicProjection T d n).hom.app U).hom
      naturality := fun _ _ f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((completedAdicProjection T d n).hom.naturality f) }

set_option linter.defProp false in
/-- The full normalized scalar-extension witness along a map of coefficient sheaves.
Its object and map equalities fix ordinary tensor; its universal counit fixes the derived
functor. Source: blueprint order 1239; Stacks Tag 06YY
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChangeData (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) R))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) S))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t} φ

/-- Ordinary scalar extension, fixed on objects and morphisms by the tensor witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (completedAdicChangeData T φ).choose

/-- Additivity from the actual ordinary scalar-extension witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicChange_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (completedAdicChange T φ).Additive :=
  (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose

/-- Derived scalar extension, chosen with its universal comparison and K-flat computation.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- K tensor^L_(A_T) (P_(n+1))_T with its quotient coefficient action retained.
The main reduction functor is its scalar restriction; no constant coefficient category
is identified with the completed category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicQuotientReduction (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  completedAdicDerivedChange T (completedAdicCommProjection T d n)

/-- Restriction from each quotient coefficient sheaf is exact.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: restriction changes only the ring action. Its underlying abelian sheaf and maps
are unchanged, hence it preserves kernels and sheafified cokernels, and finite limits
and colimits. This also holds for the zero quotient ring. -/
theorem completedAdicRestriction_exact (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)) := by
  sorry

/-- Derived scalar restriction along the coefficient projection, computed termwise.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicDerivedRestriction (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (completedAdicFiniteRing T d n))
  letI := (completedAdicRestriction_exact T d n).1
  letI := (completedAdicRestriction_exact T d n).2
  (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)).mapDerivedCategory

/-- The two coefficient presentations of finite reduction are naturally isomorphic.
No isomorphism is chosen from this assertion: the already defined functors retain their
universal comparisons. Source: blueprint order 1239
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: on a K-flat representative both sides are its ordinary tensor with the quotient,
with scalars restricted via the limit projection. Ordinary balancing identifies the
section tensors, and the respective derived counits are invertible. Their composites
give the comparison, natural for maps of K-flat models and independent of resolutions
by the universal properties of the derived pairs. -/
theorem completedAdicFiniteReduction_comparison (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) : Nonempty (completedAdicFiniteReduction T d n ≅
      completedAdicQuotientReduction T d n ⋙ completedAdicDerivedRestriction T d n) := by
  sorry

/-- A sheafified pure tensor in the normalized ordinary scalar-extension functor.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicChangeTensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((completedAdicChange T φ).obj M).val.obj U :=
  (eqToHom ((completedAdicChangeData T φ).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

/-- Balancing is uniquely fixed on pure tensors, including its inverse.
Source: blueprint order 1239, normalization calculation
(blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the relation chi=psi*phi makes (s tensor r) tensor x map to
s*psi(r) tensor x a balanced trilinear map. It commutes with restrictions and
with the differentials of P, so sheafification gives a chain map. Its inverse
sends s tensor x to s tensor (1 tensor x). The balanced relations make both
composites identities. The formula on local pure tensors uniquely determines
a sheaf map in each degree and therefore uniquely determines the chain map. -/
theorem completedAdicBalance_exists (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((completedAdicChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((completedAdicChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((completedAdicChange T χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (completedAdicChangeTensor T ψ _ U s (completedAdicChangeTensor T φ _ U z x)) =
        completedAdicChangeTensor T χ _ U (s * (ψ.hom.app U z)) x := by
  sorry

/-- The canonical balancing chain map; no isomorphism is chosen without its tensor formula.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicBalance (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :=
  (completedAdicBalance_exists T φ ψ χ h P).exists.choose

/-- Invertibility is the first property of the uniquely normalized balancing witness.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance completedAdicBalance_isIso (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) : IsIso (completedAdicBalance T φ ψ χ h P) :=
  (completedAdicBalance_exists T φ ψ χ h P).exists.choose_spec.1

/-- The quotient map between any two positive levels, including the identity level.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicQuotientCommMap (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (b a : ℕ) (h : a ≤ b) :
    completedAdicFiniteCommRing T d b ⟶ completedAdicFiniteCommRing T d a where
  hom :=
    { app := fun U ↦
        letI := completedAdicFiniteCommRingStructure T d b U
        letI := completedAdicFiniteCommRingStructure T d a U
        CommRingCat.ofHom
          (((completedAdicRingSystem T d).map (homOfLE h).op).hom.app U).hom
      naturality := fun _ _ f ↦ (forget₂ CommRingCat RingCat).map_injective
        (((completedAdicRingSystem T d).map (homOfLE h).op).hom.naturality f) }

/-- The projections and quotient maps have their actual limit-cone compatibility.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: forget commutativity and apply the naturality identity of the limit cone to
the arrow op b -> op a. The forgetful functor is faithful. -/
theorem completedAdicCommProjection_comp (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (b a : ℕ) (h : a ≤ b) :
    completedAdicCommProjection T d b ≫ completedAdicQuotientCommMap T d b a h =
      completedAdicCommProjection T d a := by
  sorry

/-- The specified quotient normalization on a K-flat computation (indeed on any complex).
Its local formula is (s tensor z) tensor x ↦ s*q(z) tensor x, with inverse inserting 1.
Localizing this map on K-flat models gives the normalization of the quotient-coefficient
objects; the universal derived counits supply their canonical identifications with those
models. Naturality and the quotient cocycle follow from the same formula: for three
quotients both composites multiply the same three residue factors. Equal indices give
the ordinary unit map, so the identity case is included.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicNormalizationOnModel (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) (b a : ℕ) (h : a ≤ b) :=
  completedAdicBalance T (completedAdicCommProjection T d b)
    (completedAdicQuotientCommMap T d b a h) (completedAdicCommProjection T d a)
    (completedAdicCommProjection_comp T d b a h) P

end AlgebraicGeometry.Scheme
