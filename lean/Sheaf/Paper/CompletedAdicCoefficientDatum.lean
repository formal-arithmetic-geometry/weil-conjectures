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
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

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

universe t uC vC r

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

private theorem finiteRing_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x y : (completedAdicFiniteRing T d n).obj.obj U) :
    x * y = y * x := by
  let J := ProEt.topology T
  let F := ProEtale.finiteCoefficientPresheaf T (completedAdicQuotient d n)
  let R := completedAdicFiniteRing T d n
  let η : F ⟶ R.obj := toSheafify J F
  have hs := (isSheaf_iff_isSheaf_of_type J
      (R.obj ⋙ CategoryTheory.forget RingCat.{t + 1})).1
    ((sheafCompose J (CategoryTheory.forget RingCat.{t + 1})).obj R).property
  apply (hs.isSeparated _ (J.intersection_covering
    (Presheaf.imageSieve_mem J η x) (Presheaf.imageSieve_mem J η y))).ext
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  change R.obj.map f.op (x * y) = R.obj.map f.op (y * x)
  rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul]
  change C(ConnectedComponents V.left, completedAdicQuotient d n) at a b
  exact congrArg (η.app (op V)) (mul_comm a b)

/-- The limit ring sheaf is commutative on sections.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: continuous functions into the commutative quotient rings commute pointwise;
sheafification preserves that equation locally. Each limit projection therefore identifies
the images of xy and yx. Evaluate the limit on U: its projections are jointly injective,
so xy=yx. This argument includes the zero ring and the empty site object. -/
theorem completedAdicRing_mul_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (U : T.ProEtᵒᵖ) (x y : (completedAdicRing T d).obj.obj U) : x * y = y * x := by
  let D := completedAdicRingSystem T d
  let ev := sheafToPresheaf (ProEt.topology T) RingCat.{t + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ RingCat.{t + 1}).obj U
  apply Concrete.isLimit_ext (D ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit D)) (x * y) (y * x)
  intro j
  change ((limit.π D j).hom.app U) (x * y) = ((limit.π D j).hom.app U) (y * x)
  rw [map_mul, map_mul]
  exact finiteRing_comm T d j.unop U _ _

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
  have hw : completedAdicProjection T d (n + 1) ≫ completedAdicFiniteStep T d n =
      completedAdicProjection T d n := by
    simpa only [completedAdicProjection, completedAdicRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ] using
      limit.w (completedAdicRingSystem T d) (homOfLE (Nat.le_succ n)).op
  let q : completedAdicFiniteModule T d (n + 1) ⟶ completedAdicFiniteModule T d n :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (completedAdicFiniteModule T d (n + 1)).val.obj U)
            (Y := (completedAdicFiniteModule T d n).val.obj U)
            { toFun := (completedAdicFiniteStep T d n).hom.app U
              map_add' := map_add _
              map_smul' := by
                intro r s
                change (completedAdicRing T d).obj.obj U at r
                change (completedAdicFiniteRing T d (n + 1)).obj.obj U at s
                change (completedAdicFiniteStep T d n).hom.app U
                    ((completedAdicProjection T d (n + 1)).hom.app U r * s) =
                  (completedAdicProjection T d n).hom.app U r *
                    (completedAdicFiniteStep T d n).hom.app U s
                rw [map_mul]
                have h := ConcreteCategory.congr_hom
                  (congrArg (fun f ↦ f.hom.app U) hw) r
                exact congrArg (fun z ↦ z * (completedAdicFiniteStep T d n).hom.app U s) h }
          naturality := by
            intro U V f
            ext s
            exact ConcreteCategory.congr_hom
              ((completedAdicFiniteStep T d n).hom.naturality f) s } }
  refine ⟨q, fun _ _ ↦ rfl, ?_⟩
  intro q' hq'
  ext U s
  exact hq' U s

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
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (tensorRight (completedAdicFiniteModule T d n.unop)).map (f + g) =
    (tensorRight (completedAdicFiniteModule T d n.unop)).map f +
      (tensorRight (completedAdicFiniteModule T d n.unop)).map g
  exact (tensorRight (completedAdicFiniteModule T d n.unop)).map_add

attribute [instance] completedAdicOrdinaryTower_additive

set_option backward.isDefEq.respectTransparency false in
private theorem tensorKFlat_of_acyclic
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [HasColimitsOfSize.{0, 0} C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (K : CochainComplex C ℤ)
    (hK : ∀ F : CochainComplex C ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F K (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨F, rfl⟩ := Z.quotient_obj_surjective
  have hF := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).1 hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor F K (curriedTensor C))).2 (hK F hF)
  exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRight_quasiIso_of_models
    {C : Type uC} [Category.{vC} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [HasColimitsOfSize.{0, 0} C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (res : ∀ G : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (f : K ⟶ G),
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K ∧ QuasiIso f)
    (Q : C) {P₁ P₂ : CochainComplex C ℤ} (f : P₁ ⟶ P₂) (hf : QuasiIso f)
    (h₁ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P₂) :
    QuasiIso (((tensorRight Q).mapHomologicalComplex (.up ℤ)).map f) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let Z := (HomologicalComplex.single C (.up ℤ) 0).obj Q
  obtain ⟨Z', g, hZ', hg⟩ := res Z
  have hg' : W g := hg
  have h : W (f ▷ Z) := by
    rw [← W.precomp_iff _ _ (h₁.whiskerLeft hg'), whisker_exchange f g]
    exact W.comp_mem _ _ (hZ'.whiskerRight hf) (h₂.whiskerLeft hg')
  exact (W.arrow_mk_iso_iff
    (Arrow.isoOfNatIso (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) Q)
      (Arrow.mk f))).1 h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let : SymmetricCategory (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesSymmetric (completedAdicCommRing T d)
  let : ∀ M : CompletedAdicModules T d,
      PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    fun M ↦ SheafOfModules.cochainTensorLeftPreservesColimits (completedAdicCommRing T d) M
  let : ∀ M : CompletedAdicModules T d,
      PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    fun M ↦ SheafOfModules.cochainTensorRightPreservesColimits (completedAdicCommRing T d) M
  have hk (P : CochainComplex (CompletedAdicModules T d) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (.up ℤ)).kFlat P :=
    tensorKFlat_of_acyclic P hP
  have hmodels (G : CochainComplex (CompletedAdicModules T d) ℤ) :
      ∃ (P : CochainComplex (CompletedAdicModules T d) ℤ) (s : P ⟶ G),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P ∧
          QuasiIso s := by
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionGeneral
        (R := completedAdicCommRing T d) G
    exact ⟨P, s, hP, hs⟩
  have hinv {P Q : CochainComplex (CompletedAdicModules T d) ℤ} (a : P ⟶ Q)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P)
      (hQ : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) Q)
      (ha : QuasiIso a) :
      QuasiIso (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).map a) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    change QuasiIso
      (((tensorRight (completedAdicFiniteModule T d n.unop)).mapHomologicalComplex
        (.up ℤ)).map a)
    apply tensorRight_quasiIso_of_models _ _ a ha (hk P hP) (hk Q hQ)
    intro G
    obtain ⟨K, s, hK, hs⟩ := hmodels G
    exact ⟨K, s, hk K hK, hs⟩
  let F := (completedAdicOrdinaryTower T d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory (CompletedAdicModules T d) (.up ℤ)) :=
    { X | ∃ P : CochainComplex (CompletedAdicModules T d) ℤ,
      CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P ∧
        (HomotopyCategory.quotient _ (.up ℤ)).obj P = X }
  have hres : ∀ X : HomotopyCategory (CompletedAdicModules T d) (.up ℤ),
      ∃ (X' : HomotopyCategory (CompletedAdicModules T d) (.up ℤ)) (s : X' ⟶ X),
        X' ∈ S ∧ HomotopyCategory.quasiIso _ _ s := by
    intro X
    obtain ⟨G, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨P, s, hP, hs⟩ := hmodels G
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨P, hP, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinvS : ∀ (X Y : HomotopyCategory (CompletedAdicModules T d) (.up ℤ))
      (s : X ⟶ Y), X ∈ S → Y ∈ S → HomotopyCategory.quasiIso _ _ s →
        IsIso (F.map s) := by
    intro X Y s hX hY hs
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨Q, hQ, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hEa := hinv a hP hQ ha
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  obtain ⟨_, LF, ε, hLF, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass _ _ F S hres hinvS
  exact ⟨LF, ε, hLF, fun P hP ↦ hε _ ⟨P, hP, rfl⟩⟩

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
  exact finiteRing_comm T d n U x y

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
  let F := SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)
  let U := SheafOfModules.toSheaf.{t + 1} (completedAdicRing T d)
  have : PreservesFiniteLimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{t + 1} (completedAdicFiniteRing T d n)))
  have : PreservesFiniteColimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{t + 1} (completedAdicFiniteRing T d n)))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesFiniteColimits_of_reflects_of_preserves F U⟩

/-- Derived scalar restriction along the coefficient projection, computed termwise.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def completedAdicDerivedRestriction (T : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (completedAdicFiniteRing T d n))
  letI := (completedAdicRestriction_exact T d n).1
  letI := (completedAdicRestriction_exact T d n).2
  (SheafOfModules.restrictScalars.{t + 1} (completedAdicProjection T d n)).mapDerivedCategory

namespace CompletedTensorComparisonProof

open SheafOfModules

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionTensorIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O))
    (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X ≅
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X := by
  let e : (((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X) ≃ₗ[O.obj.obj X]
      ((((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def presheafTensorIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O)) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M) ≅
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val :=
  PresheafOfModules.isoMk (sectionTensorIso φ M) (by
    intro X Y f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      change changeOfRingsMap φ M f (s ⊗ₜ m) = _
      rw [show changeOfRingsMap φ M f (s ⊗ₜ m) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ M f) s m]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

private noncomputable def changePresheafHom
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
  { app := fun X ↦ (ModuleCat.extendScalars (φ.hom.app X).hom).map (a.val.app X)
    naturality := changeOfRingsHom_naturality φ M a }

set_option backward.isDefEq.respectTransparency false in
private lemma presheafTensorIso_naturality
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        (changePresheafHom φ a) ≫ (presheafTensorIso φ N).hom =
      (presheafTensorIso φ M).hom ≫
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit (𝓡 O'))).val ◁ a.val := by
  ext X x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O : Sheaf J CommRingCat.{r}}
    (S : SheafOfModules.{r} (𝓡 O)) {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    letI := monoidalCategory O
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).map (S.val ◁ a.val) ≫
      (tensorObjIsoSheafification S N).inv =
    (tensorObjIsoSheafification S M).inv ≫ S ◁ a := by
  let := monoidalCategory O
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).counit
  let c (M : SheafOfModules.{r} (𝓡 O)) := ε.app M
  apply (cancel_mono (tensorObjIsoSheafification S N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorObjIsoSheafification S M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change ((c S).inv ⊗ₘ (c M).inv) ≫
      Functor.LaxMonoidal.μ A S.val M.val ≫ A.map (S.val ◁ a.val) =
    S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) ≫
      Functor.LaxMonoidal.μ A S.val N.val
  rw [← Functor.LaxMonoidal.μ_natural_right]
  have hn : (c M).inv ≫ A.map a.val = a ≫ (c N).inv :=
    (ε.inv.naturality a).symm
  have h : ((c S).inv ⊗ₘ (c M).inv) ≫
      (A.obj S.val ◁ A.map a.val) =
      S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) := by
    calc
      _ = (c S).inv ⊗ₘ ((c M).inv ≫ A.map a.val) := by
        have ht := CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom
          (c S).inv (c M).inv (𝟙 (A.obj S.val)) (A.map a.val)
        erw [CategoryTheory.MonoidalCategory.id_tensorHom, Category.comp_id] at ht
        exact ht
      _ = (c S).inv ⊗ₘ (a ≫ (c N).inv) :=
        congrArg (fun f ↦ (c S).inv ⊗ₘ f) hn
      _ = _ := by
        simpa only [Category.id_comp,
          CategoryTheory.MonoidalCategory.id_tensorHom] using
          (CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom
            (𝟙 S) a (c S).inv (c N).inv).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f ↦ f ≫ Functor.LaxMonoidal.μ A S.val N.val) h) |>.trans
      (Category.assoc _ _ _)


section RestrictionSheafification
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ B₀ : Sheaf J RingCat.{r}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{r}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance


omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
set_option backward.isDefEq.respectTransparency false in
private theorem restrictionSheafificationComparison_naturality
    (α : R₀ ⟶ B₀) {P Q : PresheafOfModules.{r} B₀.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).map
        ((PresheafOfModules.restrictScalars α.hom).map f) ≫
        restrictionSheafificationComparison α Q =
      restrictionSheafificationComparison α P ≫
        (restrictScalars α).map ((PresheafOfModules.sheafification (𝟙 B₀.obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [adj, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    restrictionSheafificationComparison, Equiv.apply_symm_apply]
  have h := congrArg (PresheafOfModules.restrictScalars α.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.naturality f)
  simp only [Functor.map_comp] at h
  ext V x
  exact congrArg (fun k ↦ k.app V x) h

end RestrictionSheafification

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedChangeTensorIso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (E : SheafOfModules.{r} (𝓡 R) ⥤ SheafOfModules.{r} (𝓡 S))
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ changeOfRingsHom φ M a ≫ eqToHom (h N).symm) :
    letI := monoidalCategory R
    Nonempty (E ⋙ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      tensorRight ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj (unit (𝓡 S)))) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let α := (sheafCompose J (forget₂ CommRingCat RingCat)).map φ
  let U := restrictScalars α
  let B := U.obj (unit (𝓡 S))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  let c (M : SheafOfModules.{r} (𝓡 R)) := by
    have := restrictionSheafificationComparison_isIso α (changeOfRingsPresheaf φ M)
    exact asIso (restrictionSheafificationComparison α (changeOfRingsPresheaf φ M))
  let e (M : SheafOfModules.{r} (𝓡 R)) : U.obj (changeOfRings φ M) ≅ B ⊗ M :=
    (c M).symm ≪≫ A.mapIso (presheafTensorIso φ M) ≪≫
      (tensorObjIsoSheafification B M).symm
  have he {M N : SheafOfModules.{r} (𝓡 R)} (a : M ⟶ N) :
      U.map (changeOfRingsHom φ M a) ≫ (e N).hom = (e M).hom ≫ B ◁ a := by
    have hr := restrictionSheafificationComparison_naturality α (changePresheafHom φ a)
    change A.map ((PresheafOfModules.restrictScalars α.hom).map
      (changePresheafHom φ a)) ≫ (c N).hom =
      (c M).hom ≫ U.map (changeOfRingsHom φ M a) at hr
    have hc : U.map (changeOfRingsHom φ M a) ≫ (c N).inv =
        (c M).inv ≫ A.map ((PresheafOfModules.restrictScalars α.hom).map
          (changePresheafHom φ a)) := by
      apply (cancel_epi (c M).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hp := congrArg A.map (presheafTensorIso_naturality φ a)
    simp only [Functor.map_comp] at hp
    have ht := tensorComparison_naturality B a
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, hc]
    simp only [Category.assoc]
    rw [reassoc_of% hp, ht]
  let e' : E ⋙ U ≅ tensorLeft B := NatIso.ofComponents
    (fun M ↦ U.mapIso (eqToIso (h M)) ≪≫ e M) (by
      intro M N a
      change U.map (E.map a) ≫ _ = _
      rw [hm]
      simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
        Category.assoc]
      simp only [← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl]
      simp only [Category.comp_id, Functor.map_comp, Category.assoc]
      rw [he]
      rfl)
  exact ⟨e' ≪≫ BraidedCategory.tensorLeftIsoTensorRight B⟩

end CompletedTensorComparisonProof

set_option backward.isDefEq.respectTransparency false in
private theorem nonemptyIsoOfResolvingModels
    (C D : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (S : Set (HomotopyCategory C (.up ℤ)))
    (hres : ∀ X, ∃ (Y : HomotopyCategory C (.up ℤ)) (s : Y ⟶ X),
      Y ∈ S ∧ HomotopyCategory.quasiIso C (.up ℤ) s)
    (L₁ L₂ : DerivedCategory C ⥤ DerivedCategory D)
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F)
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F)
    (h₁ : ∀ X, X ∈ S → IsIso (α₁.app X))
    (h₂ : ∀ X, X ∈ S → IsIso (α₂.app X)) : Nonempty (L₁ ≅ L₂) := by
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have hinv : ∀ X Y (f : X ⟶ Y), X ∈ S → Y ∈ S → W f → IsIso (F.map f) := by
    intro X Y f hX hY hf
    have := h₁ X hX
    have := h₁ Y hY
    have : IsIso (DerivedCategory.Qh.map f) := Localization.inverts _ W f hf
    have hh := α₁.naturality f
    change L₁.map (DerivedCategory.Qh.map f) ≫ α₁.app Y = α₁.app X ≫ F.map f at hh
    exact IsIso.of_isIso_fac_left hh.symm
  obtain ⟨_, L, ε, hL, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) F S hres hinv
  let := hL
  have compare (L' : DerivedCategory C ⥤ DerivedCategory D)
      (α : DerivedCategory.Qh ⋙ L' ⟶ F)
      (hα : ∀ X, X ∈ S → IsIso (α.app X)) : Nonempty (L' ≅ L) := by
    let δ := L.leftDerivedLift ε W L' α
    have hδ (X : HomotopyCategory C (.up ℤ)) (hX : X ∈ S) :
        IsIso (δ.app (DerivedCategory.Qh.obj X)) := by
      have := hα X hX
      have := hε X hX
      exact IsIso.of_isIso_fac_right (Functor.leftDerived_fac_app L ε W L' α X)
    have hδall (X : DerivedCategory C) : IsIso (δ.app X) := by
      let X₀ := DerivedCategory.Qh.objPreimage X
      obtain ⟨Y, f, hY, hf⟩ := hres X₀
      have : IsIso (DerivedCategory.Qh.map f) := Localization.inverts _ W f hf
      let e : DerivedCategory.Qh.obj Y ≅ X :=
        asIso (DerivedCategory.Qh.map f) ≪≫ DerivedCategory.Qh.objObjPreimageIso X
      exact (NatTrans.isIso_app_iff_of_iso δ e).1 (hδ Y hY)
    have : IsIso δ := NatIso.isIso_of_isIso_app δ
    exact ⟨asIso δ⟩
  obtain ⟨e₁⟩ := compare L₁ α₁ h₁
  obtain ⟨e₂⟩ := compare L₂ α₂ h₂
  exact ⟨e₁ ≪≫ e₂.symm⟩

section FiniteReductionComparison

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compareExactReductions
    {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
    [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    [Category C₃] [Abelian C₃] [HasDerivedCategory C₃]
    [Category C₄] [Abelian C₄] [HasDerivedCategory C₄]
    (O : C₁ ⥤ C₂) [O.Additive] (E : C₁ ⥤ C₃) [E.Additive]
    (V : C₂ ⥤ C₄) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (U : C₃ ⥤ C₄) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : E ⋙ U ≅ O ⋙ V)
    (L₁ : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (L₂ : DerivedCategory C₁ ⥤ DerivedCategory C₃)
    (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶ O.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P Q : CochainComplex C₁ ℤ → Prop)
    (hres : ∀ X : CochainComplex C₁ ℤ,
      ∃ (Y : CochainComplex C₁ ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s)
    (hPQ : ∀ K, P K → Q K)
    (h₁ : ∀ K, P K → IsIso (ε₁.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
    (h₂ : ∀ K, Q K → IsIso (ε₂.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    Nonempty (L₁ ⋙ V.mapDerivedCategory ≅ L₂ ⋙ U.mapDerivedCategory) := by
  let eH : E.mapHomotopyCategory (.up ℤ) ⋙ U.mapHomotopyCategory (.up ℤ) ≅
      O.mapHomotopyCategory (.up ℤ) ⋙ V.mapHomotopyCategory (.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso (F := E) (G := U) e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (F := O) (G := V)
        (Iso.refl (O ⋙ V)) (.up ℤ)).symm
  let F := (O.mapHomotopyCategory (.up ℤ) ⋙ V.mapHomotopyCategory (.up ℤ)) ⋙
    DerivedCategory.Qh
  let k₁ : (O.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ V.mapDerivedCategory ≅
      F :=
    Functor.associator (O.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      V.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (O.mapHomotopyCategory (.up ℤ)) V.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator (O.mapHomotopyCategory (.up ℤ))
        (V.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).symm
  let k₂ : (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ U.mapDerivedCategory ≅
      F :=
    Functor.associator (E.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      U.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (E.mapHomotopyCategory (.up ℤ)) U.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator (E.mapHomotopyCategory (.up ℤ))
        (U.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight eH DerivedCategory.Qh
  let α₁ : DerivedCategory.Qh ⋙ (L₁ ⋙ V.mapDerivedCategory) ⟶ F :=
    (Functor.associator DerivedCategory.Qh L₁ V.mapDerivedCategory).inv ≫
      Functor.whiskerRight ε₁ V.mapDerivedCategory ≫ k₁.hom
  let α₂ : DerivedCategory.Qh ⋙ (L₂ ⋙ U.mapDerivedCategory) ⟶ F :=
    (Functor.associator DerivedCategory.Qh L₂ U.mapDerivedCategory).inv ≫
      Functor.whiskerRight ε₂ U.mapDerivedCategory ≫ k₂.hom
  let S : Set (HomotopyCategory C₁ (.up ℤ)) :=
    { X | ∃ K : CochainComplex C₁ ℤ,
      P K ∧ (HomotopyCategory.quotient _ (.up ℤ)).obj K = X }
  have hres' : ∀ X : HomotopyCategory C₁ (.up ℤ),
      ∃ (Y : HomotopyCategory C₁ (.up ℤ)) (s : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso C₁ (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨L, s, hL, hs⟩ := hres K
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  apply nonemptyIsoOfResolvingModels C₁ C₄ F S hres'
    (L₁ ⋙ V.mapDerivedCategory) (L₂ ⋙ U.mapDerivedCategory) α₁ α₂
  · rintro X ⟨K, hK, rfl⟩
    have := h₁ K hK
    dsimp only [α₁, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  · rintro X ⟨K, hK, rfl⟩
    have := h₂ K (hPQ K hK)
    dsimp only [α₂, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedOrdinaryRestrictionComparison (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    letI := SheafOfModules.cochainModulesMonoidal R
    Nonempty (completedAdicChange T φ ⋙ SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ≅
      tensorRight ((SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).obj
          (SheafOfModules.unit
            ((sheafCompose (ProEt.topology T)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))) := by
  exact CompletedTensorComparisonProof.restrictedChangeTensorIso φ (completedAdicChange T φ)
    (completedAdicChangeData T φ).choose_spec.choose
    (fun f ↦ (completedAdicChangeData T φ).choose_spec.choose_spec.choose f)

private abbrev completedChangeModels (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  let h := (completedAdicChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  h.choose_spec

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) (completedAdicFiniteCommRing T d n)))
  let sourceDerived : HasDerivedCategory (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) (completedAdicCommRing T d))) :=
    completedAdicModules_hasDerived T d
  let φ := completedAdicCommProjection T d n
  let E := completedAdicChange T φ
  let U := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  have hULim : PreservesFiniteLimits U := (completedAdicRestriction_exact T d n).1
  have hUColim : PreservesFiniteColimits U := (completedAdicRestriction_exact T d n).2
  let V := (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules T d)).obj (op n)
  let O := completedAdicOrdinaryTower T d
  have hOAdd : O.Additive := inferInstance
  have hEAdd : E.Additive := inferInstance
  have hUAdd : U.Additive := inferInstance
  have hVAdd : V.Additive := inferInstance
  have hVLim : PreservesFiniteLimits V := inferInstance
  have hVColim : PreservesFiniteColimits V := inferInstance
  obtain ⟨e₀⟩ := completedOrdinaryRestrictionComparison T φ
  let e : E ⋙ U ≅ O ⋙ V := e₀
  obtain ⟨ε₂, hUniv, hShift, hε₂⟩ := completedChangeModels T φ
  have hres (G : CochainComplex (CompletedAdicModules T d) ℤ) :
      ∃ (P : CochainComplex (CompletedAdicModules T d) ℤ) (s : P ⟶ G),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P ∧
          QuasiIso s := by
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionGeneral (R := completedAdicCommRing T d) G
    exact ⟨P, s, hP, hs⟩
  let L₁ := completedAdicReduction T d
  let L₂ := completedAdicDerivedChange T φ
  let ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
      O.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (completedAdicReductionData T d).counit
  change DerivedCategory.Qh ⋙ L₂ ⟶
    E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh at ε₂
  let P := CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d)
  let Q := CochainComplex.IsKFlatIndependentCoefficients (R := completedAdicCommRing T d)
  have hPQ : ∀ K, P K → Q K := fun K hK ↦
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
      (R := completedAdicCommRing T d) K).2 hK
  have h₁ : ∀ K, P K →
      IsIso (ε₁.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) :=
    (completedAdicReductionData T d).isIso_counit
  change ∀ K, Q K → IsIso (ε₂.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) at hε₂
  change ∀ G, ∃ Y s, P Y ∧ QuasiIso s at hres
  change Nonempty (L₁ ⋙ V.mapDerivedCategory ≅ L₂ ⋙ U.mapDerivedCategory)
  clear hUniv hShift
  clear_value e ε₁ L₁ L₂
  clear e₀
  clear_value O E V U φ P Q
  as_aux_lemma =>
    exact @compareExactReductions
      (CompletedAdicModules T d) (CompletedAdicTowers T d)
      (SheafOfModules.{t + 1}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
          (ProEt.topology T) (completedAdicFiniteCommRing T d n)))
      (CompletedAdicModules T d)
      inferInstance inferInstance (completedAdicModules_hasDerived T d)
      inferInstance inferInstance (completedAdicTowers_hasDerived T d)
      inferInstance inferInstance (HasDerivedCategory.standard _)
      inferInstance inferInstance (completedAdicModules_hasDerived T d)
      O hOAdd E hEAdd V hVAdd hVLim hVColim U hUAdd hULim hUColim
      e L₁ L₂ ε₁ ε₂ P Q hres hPQ h₁ hε₂

end FiniteReductionComparison

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

private abbrev completedRestriction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)

set_option backward.isDefEq.respectTransparency false in
private theorem completedAdjunction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ a : completedAdicChange T φ ⊣ completedRestriction T φ,
      ∀ (M : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
        (N : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
        (f : (completedAdicChange T φ).obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.homEquiv M N f).val.app U x =
          f.val.app U (completedAdicChangeTensor T φ M U 1 x) := by
  let h := (completedAdicChangeData T φ).choose_spec.choose
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, hnorm⟩ := ha (completedAdicChange T φ) h
    (fun f ↦ (completedAdicChangeData T φ).choose_spec.choose_spec.choose f)
  refine ⟨a, ?_⟩
  intro M N f U x
  have he := hnorm M N (eqToHom (h M).symm ≫ f) U x
  have hh : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hh] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    (h : N = SheafOfModules.changeOfRings φ M)
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s • (eqToHom h.symm).val.app U
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
  let e := eqToHom h.symm
  change e.val.app U (η ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom s z x
  have hη := η.hom.map_smul s (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul s
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)


set_option backward.isDefEq.respectTransparency false in
private theorem completedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    completedAdicChangeTensor T φ M U (s * z) x =
      s • completedAdicChangeTensor T φ M U z x := by
  exact normalizedTensor_smul T φ M _
    ((completedAdicChangeData T φ).choose_spec.choose M) U s z x

private def completedRestrictCompIso (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) :
    completedRestriction T (φ ≫ ψ) ≅ completedRestriction T ψ ⋙ completedRestriction T φ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem balancing_from_adjunctions (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V)
    (E1 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    [E1.Additive]
    (τ1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      S.obj.obj U → M.val.obj U → (E1.obj M).val.obj U)
    (a1 : E1 ⊣ completedRestriction T φ)
    (h1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
      (f : E1.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a1.homEquiv M N f).val.app U x = f.val.app U (τ1 M U 1 x))
    (hs1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : S.obj.obj U)
      (x : M.val.obj U), τ1 M U (s * z) x = s • τ1 M U z x)
    (E2 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E2.Additive]
    (τ2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E2.obj M).val.obj U)
    (a2 : E2 ⊣ completedRestriction T ψ)
    (h2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E2.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a2.homEquiv M N f).val.app U x = f.val.app U (τ2 M U 1 x))
    (hs2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ2 M U (s * z) x = s • τ2 M U z x)
    (E3 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E3.Additive]
    (τ3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E3.obj M).val.obj U)
    (a3 : E3 ⊣ completedRestriction T (φ ≫ ψ))
    (h3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E3.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a3.homEquiv M N f).val.app U x = f.val.app U (τ3 M U 1 x))
    (hs3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ3 M U (s * z) x = s • τ3 M U z x)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((E2).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((E1).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((E3).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (τ2 _ U s (τ1 _ U z x)) =
        τ3 _ U (s * (ψ.hom.app U z)) x := by
  let a := (a1.comp a2).ofNatIsoRight (completedRestrictCompIso T φ ψ).symm
  let e := a.leftAdjointUniq a3
  have hcomp (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : ((E1) ⋙ E2).obj M ⟶ N)
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (a.homEquiv M N f).val.app U x =
        f.val.app U (τ2 _ U 1
          (τ1 M U 1 x)) := by
    dsimp only [a]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change (a1.homEquiv M _ (a2.homEquiv _ N f)).val.app U x = _
    exact (h1 M _ (a2.homEquiv _ N f) U x).trans
      (h2 _ N f U (τ1 M U 1 x))
  clear_value a
  have hunit (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U 1
        (τ1 M U 1 x)) =
      τ3 M U 1 x := by
    have he := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a a3 M)
    rw [hcomp] at he
    rw [← a3.homEquiv_id M, h3] at he
    exact he
  clear_value e
  have hformula (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U s
        (τ1 M U z x)) =
      τ3 M U (s * ψ.hom.app U z) x := by
    have hz := hs1 M U z 1 x
    rw [mul_one] at hz
    have hs := hs2 ((E1).obj M) U s 1
      (τ1 M U z x)
    rw [mul_one] at hs
    erw [hs, map_smul, ← h2, hz, map_smul]
    change s • (ψ.hom.app U z •
      (show (E3.obj M).val.obj U from
        (a2.homEquiv _ _ (e.hom.app M)).val.app U (τ1 M U 1 x))) = _
    erw [h2, hunit, ← mul_smul]
    have ht := hs3 M U (s * ψ.hom.app U z) 1 x
    simpa only [mul_one] using ht.symm
  let f := ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
  refine ⟨f, ⟨by dsimp [f]; infer_instance, ?_⟩, ?_⟩
  · intro p U s z x
    exact hformula (P.X p) U s z x
  · intro g hg
    apply HomologicalComplex.Hom.ext
    funext p
    apply (a.homEquiv _ _).injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rw [hcomp, hcomp]
    exact (hg.2 p U 1 1 x).trans (hformula (P.X p) U 1 1 x).symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  subst χ
  obtain ⟨a1, h1⟩ := completedAdjunction T φ
  obtain ⟨a2, h2⟩ := completedAdjunction T ψ
  obtain ⟨a3, h3⟩ := completedAdjunction T (φ ≫ ψ)
  exact balancing_from_adjunctions T φ ψ _ (completedAdicChangeTensor T φ) a1 h1
    (completedTensor_smul T φ) _ (completedAdicChangeTensor T ψ) a2 h2
    (completedTensor_smul T ψ) _ (completedAdicChangeTensor T (φ ≫ ψ)) a3 h3
    (completedTensor_smul T (φ ≫ ψ)) P

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
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map_injective
  change completedAdicProjection T d b ≫
    (completedAdicRingSystem T d).map (homOfLE h).op = completedAdicProjection T d a
  exact limit.w _ _

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
