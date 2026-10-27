/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation
public import Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.CochainComplexPlus
import Sheaf.CategoryTheory.DerivedAdjunctionCochainUnit
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Derived-unit representatives and cross-site signed total squares

Source: Stacks Project, proetale.tex, Tag 09A2; derived.tex, Tags 0DVC and 09T5;
sites-cohomology.tex, Tag 0D6E, with the explicit cross-site restriction calculation.
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).

## Main definitions

* `restriction`: the unique chain map with the actual cross-site summand formula.
* `transpose`: the ordinary adjunction transpose of the chosen resolution lift.
* `derivedSectionMap`: the actual derived unit and canonical composition comparison.

## Main statements

* `comparison`, `unit_representative`, `sections_representative`: resolution normalization.
* `augmentation_square`, `coefficient_homotopy`: strict and signed homotopy squares.
* `coefficient_naturality`, `refinement_naturality`, `restriction_comp`, `restriction_id`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.HypercoverUnit

/-- Termwise ordinary module pullback. Source: Stacks, Tags 03D2 and 09T5
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
abbrev pull {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) :=
  (proEtaleRingModulePullback h R S c).mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary direct image. Source: Stacks, Tags 03D1 and 09T5
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
abbrev push {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) :=
  (proEtaleRingModuleDirectImage h R S c).mapHomologicalComplex (.up ℤ)

/-- The given signed module total, forgetting only its scalar action. The action is
retained on each summand; this permits maps over different global coefficient rings.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
abbrev total (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :=
  ProEt.hypercoverTotal X R W U ⋙
    (forget₂ (ModuleCat.{u + 1} (R.obj.obj (op W)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)

/-- Inclusion of an actual section in bidegree (p,q) into the prescribed total.
Source: Stacks, Tag 09A2, signed coproduct total
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def summand (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W))
    (E : CochainComplex (proEtaleRingModules X R) ℤ) (p : ℕ) (q n : ℤ)
    (hpq : (p : ℤ) + q = n) (x : (E.X q).val.obj (op (U _⦋p⦌).left)) :
    ((total X R W U).obj E).X n :=
  (HomologicalComplex₂.flip
    (((ProEt.hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj E)).ιTotal
      (.up ℤ) p q n hpq
        (((((AlgebraicTopology.alternatingCofaceMapComplex _).obj
          ((ProEt.hypercoverSections X R W U).obj (E.X q))).extendXIso
            ComplexShape.embeddingUpNat (i := p) rfl).inv) x)

/-- Cross-site restriction is the specified ordinary unit followed by site restriction.
Source: Stacks, Tag 09A2 and Modules on Sites, lemma-adjoint-push-pull-modules
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def restrictSection {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules X R) (A : X.ProEt) (B : Y.ProEt)
    (g : B ⟶ (proEtaleBaseChange h).obj A) (x : M.val.obj (op A)) :
    ((proEtaleRingModulePullback h R S c).obj M).val.obj (op B) :=
  ((proEtaleRingModulePullback h R S c).obj M).val.map g.op
    (((proEtaleRingModuleAdjunction h R S c).unit.app M).val.app (op A) x)

/-- A total map has the prescribed component formula, including a coefficient map b.
This property determines the entire map by the coproduct universal property.
Source: Stacks, Tag 09A2, the explicit cross-site section formula
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def RestrictionFormula {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over W'))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (E : CochainComplex (proEtaleRingModules X R) ℤ)
    (F : CochainComplex (proEtaleRingModules Y S) ℤ) (b : (pull h R S c).obj E ⟶ F)
    (G : (total X R W U).obj E ⟶ (total Y S W' V).obj F) : Prop :=
  ∀ (p : ℕ) (q n : ℤ) (hpq : (p : ℤ) + q = n)
    (x : (E.X q).val.obj (op (U _⦋p⦌).left)),
    G.f n (summand X R W U E p q n hpq x) =
      summand Y S W' V F p q n hpq
        ((b.f q).val.app (op (V _⦋p⦌).left)
          (restrictSection h R S c (E.X q) _ _ (g.app (op ⦋p⦌)) x))

/-- The degreewise restriction formula defines exactly one chain map on signed totals.
Source: Stacks, Tag 09A2, explicit restriction calculation
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: take the coproduct map with the displayed component on each nonnegative
simplicial summand, using the zero map on the negative summands, which are zero
objects. Naturality of the unit, of b and of g makes it commute with every coface
and coefficient differential, hence with delta + (-1)^p d. The coproduct universal
property proves uniqueness degree by degree. No covering assumption is used. -/
theorem restriction_existsUnique {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over W'))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (E : CochainComplex (proEtaleRingModules X R) ℤ)
    (F : CochainComplex (proEtaleRingModules Y S) ℤ) (b : (pull h R S c).obj E ⟶ F) :
    ∃! G : (total X R W U).obj E ⟶ (total Y S W' V).obj F,
      RestrictionFormula h R S c W W' U V g E F b G := by
  sorry

/-- The universal-property construction of restriction followed by b on each summand.
Its defining theorem determines all its data up to equality, not just existence.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def restriction {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over W'))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (E : CochainComplex (proEtaleRingModules X R) ℤ)
    (F : CochainComplex (proEtaleRingModules Y S) ℤ) (b : (pull h R S c).obj E ⟶ F) :=
  Classical.choose (restriction_existsUnique h R S c W W' U V g E F b)

/-- Evaluation as an abelian group, retaining the prescribed module evaluation.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
abbrev sections (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) :=
  SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W) ⋙
    forget₂ (ModuleCat.{u + 1} (R.obj.obj (op W))) AddCommGrpCat.{u + 1}

/-- Section evaluation preserves addition of coefficient maps.
Source: Stacks, Tags 03D1 and 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: evaluation and forgetting a scalar action leave the underlying additive
map unchanged, so the equality holds on every section by definition. -/
theorem sections_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt) :
    (sections X R W).Additive := by
  constructor
  intro M N f g
  ext x
  rfl

attribute [instance] sections_additive

/-- The actual augmentation of the module total, viewed on underlying abelian groups.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def augmentation (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W))
    (E : CochainComplex (proEtaleRingModules X R) ℤ) :
    ((sections X R W).mapHomologicalComplex (.up ℤ)).obj E ⟶
      (total X R W U).obj E :=
  ((forget₂ (ModuleCat.{u + 1} (R.obj.obj (op W)))
    AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).map
      ((ProEt.hypercoverAugmentation X R W U).app E)

/-- The ordinary transpose a = eta_I followed by h_*b, on complexes.
Source: Stacks, Tag 09T5 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def transpose {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    {I : CochainComplex (proEtaleRingModules X R) ℤ}
    {J : CochainComplex (proEtaleRingModules Y S) ℤ} (b : (pull h R S c).obj I ⟶ J) :
    I ⟶ (push h R S c).obj J :=
  ((proEtaleRingModuleAdjunction h R S c).mapHomologicalComplex (.up ℤ)).unit.app I ≫
    (push h R S c).map b

/-- The literal sectionwise direct-image identification, not a chosen isomorphism.
Source: Stacks, Tags 03D1 and 0D6E
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def directImageSections {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt) :
    proEtaleRingModuleDirectImage h R S c ⋙ sections X R W ≅
      sections Y S ((proEtaleBaseChange h).obj W) :=
  Iso.refl _

variable [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]

/-- The canonical derived direct-image composition comparison. Its normalization is
fixed by the universal derived units, so on h_*J it uses the identity resolution.
Source: Stacks, Tag 0D6E (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def derivedSectionsComposition {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt) :=
  letI := (proEtaleRingModuleAdjunction h R S c).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso'
    (proEtaleRingModuleDirectImage h R S c) (sections X R W)
      (directImageSections h R S c W)

/-- The canonical unit-induced derived section map, using the actual adjunction.
Source: Stacks, Tags 09T5 and 0D6E
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def derivedSectionMap {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :=
  (sections X R W).rightDerivedFunctor.map
      ((proEtaleRingDerivedAdjunction h R S c).unit.app K) ≫
    (derivedSectionsComposition h R S c W).hom.app
      ((proEtaleRingDerivedPullback h R S c).obj K)

/-- A comparison b exists and its homotopy class is uniquely specified by b h^*i ~ j.
Source: Stacks, Tag 09T5 and the K-injective comparison principle
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: strictly bounded-below termwise-injective J is K-injective. Exactness of
h^* makes h^*i a quasi-isomorphism. Precomposition with it is a bijection on Hom
in the homotopy category with target J. Lift [j] along this bijection and choose
a chain representative. Injectivity of the same bijection proves uniqueness. -/
theorem comparison {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (E I : CochainComplex.Plus (proEtaleRingModules X R))
    (J : CochainComplex.Plus (proEtaleRingModules Y S))
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) (hJ : ∀ n : ℤ, Injective (J.obj.X n))
    (i : E.obj ⟶ I.obj) (j : (pull h R S c).obj E.obj ⟶ J.obj)
    [QuasiIso i] [QuasiIso j] :
    (∃ b : (pull h R S c).obj I.obj ⟶ J.obj,
      Nonempty (Homotopy ((pull h R S c).map i ≫ b) j)) ∧
    (∀ b b' : (pull h R S c).obj I.obj ⟶ J.obj,
      Nonempty (Homotopy ((pull h R S c).map i ≫ b) j) →
      Nonempty (Homotopy ((pull h R S c).map i ≫ b') j) →
      Nonempty (Homotopy b b')) := by
  have _ := hI
  have _ := (inferInstance : HasDerivedCategory.{w} AddCommGrpCat.{u + 1})
  obtain ⟨n, hn⟩ := J.property
  let := hn
  let : ∀ n : ℤ, Injective (J.obj.X n) := hJ
  let := CochainComplex.isKInjective_of_injective J.obj n
  let q := HomotopyCategory.quotient (proEtaleRingModules Y S) (.up ℤ)
  have bij := CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
    ((pull h R S c).map i) J.obj
  constructor
  · obtain ⟨β, hβ⟩ := bij.surjective (q.map j)
    refine ⟨β.out, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    simpa only [Functor.map_comp, HomotopyCategory.quotient_map_out] using hβ
  · intro b b' ⟨s⟩ ⟨s'⟩
    refine ⟨HomotopyCategory.homotopyOfEq _ _ (bij.injective ?_)⟩
    simpa only [Functor.map_comp] using
      (HomotopyCategory.eq_of_homotopy _ _ s).trans
        (HomotopyCategory.eq_of_homotopy _ _ s').symm

/-- The transpose represents the actual derived unit with its canonical resolution
comparisons. The equation avoids hiding either resolution identification in notation.
Source: Stacks, Tags 0DVC, 09T5 and 0D6E
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: I and J are K-injective by bounded-below injectivity. For acyclic A, exactness
of h^* and the homotopy adjunction identify Hom_K(A,h_*J) with Hom_K(h^*A,J)=0.
Naturality of eta and the given homotopy give ai ~ eta_E h_*j. Evaluate the canonical
derived Hom bijection defining the published derived adjunction at the identity
resolution of J and at the identity exact-pullback representative of E. The ordinary
transpose of eta_E h_*j is j by the triangle identity. Hence the displayed resolved
map is the actual unit, with the universal right-derived unit at J as comparison. -/
theorem unit_representative {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (E I : CochainComplex.Plus (proEtaleRingModules X R))
    (J : CochainComplex.Plus (proEtaleRingModules Y S))
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) (hJ : ∀ n : ℤ, Injective (J.obj.X n))
    (i : E.obj ⟶ I.obj) (j : (pull h R S c).obj E.obj ⟶ J.obj)
    [QuasiIso i] [QuasiIso j] (b : (pull h R S c).obj I.obj ⟶ J.obj)
    (s : Homotopy ((pull h R S c).map i ≫ b) j) :
    I.obj.IsKInjective ∧ J.obj.IsKInjective ∧
    CochainComplex.IsKInjective ((push h R S c).obj J.obj) ∧
    Nonempty (Homotopy (i ≫ transpose h R S c b) (transpose h R S c j)) ∧
    DerivedCategory.Q.map i ≫ DerivedCategory.Q.map (transpose h R S c b) ≫
        (proEtaleRingModuleDirectImage h R S c).rightDerivedFunctorUnitQ J.obj =
      (proEtaleRingDerivedAdjunction h R S c).unit.app (DerivedCategory.Q.obj E.obj) ≫
        (proEtaleRingDerivedDirectImage h R S c).map
          ((proEtaleRingDerivedPullbackFactors h R S c).hom.app E.obj ≫
            DerivedCategory.Q.map j) := by
  have _ := (inferInstance : HasDerivedCategory.{w} AddCommGrpCat.{u + 1})
  obtain ⟨nI, hnI⟩ := I.property
  obtain ⟨nJ, hnJ⟩ := J.property
  let := hnI
  let := hnJ
  let : ∀ n : ℤ, Injective (I.obj.X n) := hI
  let : ∀ n : ℤ, Injective (J.obj.X n) := hJ
  let := CochainComplex.isKInjective_of_injective I.obj nI
  let := CochainComplex.isKInjective_of_injective J.obj nJ
  let := (proEtaleRingModuleAdjunction h R S c).preservesKInjectiveComplexes
  let adj := (proEtaleRingModuleAdjunction h R S c).mapHomologicalComplex (.up ℤ)
  have hs : Homotopy (i ≫ transpose h R S c b) (transpose h R S c j) :=
    (Homotopy.ofEq (by
      dsimp only [transpose]
      have hn : i ≫ adj.unit.app I.obj = adj.unit.app E.obj ≫
          (push h R S c).map ((pull h R S c).map i) := adj.unit.naturality i
      rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp])).trans
      (((proEtaleRingModuleDirectImage h R S c).mapHomotopy s).compLeft
        (adj.unit.app E.obj))
  refine ⟨inferInstance, inferInstance, inferInstance, ⟨hs⟩, ?_⟩
  rw [← DerivedCategory.Q.map_comp_assoc, DerivedCategory.Q_map_eq_of_homotopy _ hs]
  dsimp only [transpose]
  rw [Functor.map_comp, Category.assoc,
    Functor.rightDerivedFunctorUnitQ_naturality]
  rw [← Category.assoc, ← derived_unit_cochain (proEtaleRingModuleAdjunction h R S c)]
  simp only [Functor.map_comp, Category.assoc, proEtaleRingDerivedAdjunction,
    proEtaleRingDerivedPullbackFactors, proEtaleRingDerivedDirectImage]

omit [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] in
private theorem derived_comp_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (M : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj M) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app M) ≫
        (Functor.rightDerivedFunctorCompIso' F G (Iso.refl _)).hom.app
          (DerivedCategory.Qh.obj M) =
      (F ⋙ G).rightDerivedFunctorUnit.app M := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app M
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  have hc := Functor.rightDerivedNatTrans_app
    (F ⋙ G).rightDerivedFunctor (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) M
  change (F ⋙ G).rightDerivedFunctorUnit.app M ≫
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj M) = _ at hc
  simp only [NatTrans.id_app, Category.id_comp] at hc
  have hcomp : (Functor.rightDerivedFunctorCompUnit F G).app M =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj M) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app M) := by
    simp [Functor.rightDerivedFunctorCompUnit, hi]
  rw [← Category.assoc, ← hcomp, ← hc]
  simp only [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.rightDerivedNatTrans_app, Functor.whiskerRight_app]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]

omit [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] in
private theorem derived_comp_unitQ
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (J : CochainComplex C ℤ) :
    G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnitQ J) ≫
        (Functor.rightDerivedFunctorCompIso' F G (Iso.refl _)).hom.app
          (DerivedCategory.Q.obj J) =
      (F ⋙ G).rightDerivedFunctorUnitQ J := by
  let κ := (Functor.rightDerivedFunctorCompIso' F G (Iso.refl _)).hom
  have hn := κ.naturality ((DerivedCategory.quotientCompQhIso C).hom.app J)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.map_comp, Category.assoc]
  rw [← G.rightDerivedFunctor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [G.rightDerivedFunctor.map_id, Category.id_comp]
  rw [hn]
  have he : (DerivedCategory.quotientCompQhIso E).inv.app
      (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj J) = 𝟙 _ := rfl
  rw [he]
  erw [Category.id_comp]
  have hh := congrArg (fun z ↦ z ≫
    (F ⋙ G).rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J))
    (derived_comp_unit F G ((HomotopyCategory.quotient C (.up ℤ)).obj J))
  simp only [Category.assoc] at hh
  convert hh using 1 <;> first | rfl | exact Category.id_comp _

/-- On K-injectives the canonical composition comparison is computed by the identity
resolution of h_*J. This is the normalization needed for the section representative.
Source: Stacks, Tag 0D6E (blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: naturality of the right-derived unit transports Gamma(a) to R Gamma(Qa).
The composition comparison is the unique one preserving these units. At J the
ordinary comparison is the literal equality of section functors. Since h_*J is
K-injective its identity is a valid resolution, giving exactly the equation below. -/
theorem sections_composition_representative {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (J : CochainComplex (proEtaleRingModules Y S) ℤ)
    (a : I ⟶ (push h R S c).obj J) :
    DerivedCategory.Q.map
        (((sections X R W).mapHomologicalComplex (.up ℤ)).map a) ≫
        (sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctorUnitQ J =
      (sections X R W).rightDerivedFunctorUnitQ I ≫
        (sections X R W).rightDerivedFunctor.map (DerivedCategory.Q.map a) ≫
        (sections X R W).rightDerivedFunctor.map
          ((proEtaleRingModuleDirectImage h R S c).rightDerivedFunctorUnitQ J) ≫
        (derivedSectionsComposition h R S c W).hom.app (DerivedCategory.Q.obj J) := by
  let := (proEtaleRingModuleAdjunction h R S c).preservesKInjectiveComplexes
  have hc := derived_comp_unitQ (proEtaleRingModuleDirectImage h R S c)
    (sections X R W) J
  change (sections X R W).rightDerivedFunctorUnitQ ((push h R S c).obj J) ≫
      (sections X R W).rightDerivedFunctor.map
        ((proEtaleRingModuleDirectImage h R S c).rightDerivedFunctorUnitQ J) ≫
      (derivedSectionsComposition h R S c W).hom.app (DerivedCategory.Q.obj J) =
    (sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctorUnitQ J at hc
  rw [← hc, ← Category.assoc, ← Category.assoc,
    Functor.rightDerivedFunctorUnitQ_naturality]
  simp only [Category.assoc]

/-- Thus Gamma(a), between the two given injective resolutions, represents the
canonical unit-induced derived section map. Isomorphism of the comparisons records
that this is a representative, not merely an equality after a noninvertible map.
Source: Stacks, Tags 09T5, 09A2 and 0D6E
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: apply derived sections to unit_representative and use the preceding
identity-resolution composition equation. The evaluation-derived units at I and J
are invertible because both complexes are K-injective; Q(i) and Q(j) are invertible
because i and j are quasi-isomorphisms. Cancel these canonical comparisons. -/
theorem sections_representative {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt)
    (E I : CochainComplex.Plus (proEtaleRingModules X R))
    (J : CochainComplex.Plus (proEtaleRingModules Y S))
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) (hJ : ∀ n : ℤ, Injective (J.obj.X n))
    (i : E.obj ⟶ I.obj) (j : (pull h R S c).obj E.obj ⟶ J.obj)
    [QuasiIso i] [QuasiIso j] (b : (pull h R S c).obj I.obj ⟶ J.obj)
    (s : Homotopy ((pull h R S c).map i ≫ b) j) :
    IsIso ((sections X R W).rightDerivedFunctorUnitQ I.obj) ∧
    IsIso ((sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctorUnitQ J.obj) ∧
    DerivedCategory.Q.map (((sections X R W).mapHomologicalComplex (.up ℤ)).map
          (transpose h R S c b)) ≫
        (sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctorUnitQ J.obj =
      (sections X R W).rightDerivedFunctorUnitQ I.obj ≫
        inv ((sections X R W).rightDerivedFunctor.map (DerivedCategory.Q.map i)) ≫
        derivedSectionMap h R S c W (DerivedCategory.Q.obj E.obj) ≫
        (sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctor.map
          ((proEtaleRingDerivedPullbackFactors h R S c).hom.app E.obj ≫
            DerivedCategory.Q.map j) := by
  obtain ⟨hKI, hKJ, _, _, hu⟩ := unit_representative h R S c E I J hI hJ i j b s
  let := hKI
  let := hKJ
  have hXI : IsIso ((sections X R W).rightDerivedFunctorUnitQ I.obj) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hYJ : IsIso ((sections Y S ((proEtaleBaseChange h).obj W)).rightDerivedFunctorUnitQ
      J.obj) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  refine ⟨hXI, hYJ, ?_⟩
  rw [sections_composition_representative]
  congr 1
  let G := (sections X R W).rightDerivedFunctor
  apply (cancel_epi (G.map (DerivedCategory.Q.map i))).mp
  simp only [G, IsIso.hom_inv_id_assoc]
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, hu, G.map_comp]
  dsimp only [derivedSectionMap]
  rw [Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, G, Category.assoc,
    proEtaleRingDerivedDirectImage] using congrArg (fun z ↦ G.map
    ((proEtaleRingDerivedAdjunction h R S c).unit.app (DerivedCategory.Q.obj E.obj)) ≫ z)
      ((derivedSectionsComposition h R S c W).hom.naturality
        ((proEtaleRingDerivedPullbackFactors h R S c).hom.app E.obj ≫
          DerivedCategory.Q.map j))

/-- The strict augmentation square for every b. The equation on g is precisely
commutativity with the augmentations, with no cartesian or covering hypothesis.
Source: Stacks, Tag 09A2, actual restriction augmentations
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: both composites land only in the (0,q) summands. Naturality of the ordinary
unit with restriction and the augmentation equation identify their sections before b;
naturality of b identifies their sections afterwards. All other summands are zero. -/
theorem augmentation_square {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S) (W : X.ProEt)
    (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over ((proEtaleBaseChange h).obj W)))
    (g : V ⋙ Over.forget _ ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (hg : ∀ n : SimplexCategoryᵒᵖ,
      g.app n ≫ (proEtaleBaseChange h).map (U.obj n).hom = (V.obj n).hom)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (J : CochainComplex (proEtaleRingModules Y S) ℤ) (b : (pull h R S c).obj I ⟶ J) :
    augmentation X R W U I ≫
        restriction h R S c W ((proEtaleBaseChange h).obj W) U V g I J b =
      ((sections X R W).mapHomologicalComplex (.up ℤ)).map (transpose h R S c b) ≫
        augmentation Y S ((proEtaleBaseChange h).obj W) V J := by
  sorry

/-- The coefficient square is homotopic, with the specified sign on every bidegree.
Source: Stacks, Tag 09A2, signed-total coefficient homotopy calculation
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: on (p,q) put H=(-1)^p s^q r_p. In DH+HD the horizontal contributions cancel
because their signs are (-1)^p and (-1)^(p+1). The vertical contributions have sign
(-1)^(2p)=1 and sum to (b h^*i-j)r_p. Naturality of restriction in i gives the
asserted difference of total maps. The bounded-below terms make each effective
sum finite. The component formula also uniquely determines the homotopy. -/
theorem coefficient_homotopy {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over W'))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (E I : CochainComplex.Plus (proEtaleRingModules X R))
    (J : CochainComplex.Plus (proEtaleRingModules Y S))
    (i : E.obj ⟶ I.obj) (j : (pull h R S c).obj E.obj ⟶ J.obj)
    (b : (pull h R S c).obj I.obj ⟶ J.obj)
    (s : Homotopy ((pull h R S c).map i ≫ b) j) :
    ∃ H : Homotopy
      ((total X R W U).map i ≫ restriction h R S c W W' U V g I.obj J.obj b)
      (restriction h R S c W W' U V g E.obj ((pull h R S c).obj E.obj) (𝟙 _) ≫
        (total Y S W' V).map j),
      ∀ (p : ℕ) (q n m : ℤ) (hpq : (p : ℤ) + q = n)
        (hpm : (p : ℤ) + (q - 1) = m)
        (x : (E.obj.X q).val.obj (op (U _⦋p⦌).left)),
        H.hom n m (summand X R W U E.obj p q n hpq x) =
          (-1 : ℤ) ^ p • summand Y S W' V J.obj p (q - 1) m hpm
            ((s.hom q (q - 1)).val.app (op (V _⦋p⦌).left)
              (restrictSection h R S c (E.obj.X q) _ _ (g.app (op ⦋p⦌)) x)) := by
  sorry

/-- Strict coefficient naturality of c_g. Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: naturality of the ordinary unit and restriction identifies the component
maps after a coefficient chain map in every (p,q). Coproduct extensionality then
gives equality of the chain maps themselves. -/
theorem coefficient_naturality {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U : SimplicialObject (Over W))
    (V : SimplicialObject (Over W'))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (E F : CochainComplex (proEtaleRingModules X R) ℤ) (t : E ⟶ F) :
    (total X R W U).map t ≫
        restriction h R S c W W' U V g F ((pull h R S c).obj F) (𝟙 _) =
      restriction h R S c W W' U V g E ((pull h R S c).obj E) (𝟙 _) ≫
        (total Y S W' V).map ((pull h R S c).map t) := by
  sorry

/-- The universal-property formula for an ordinary simplicial refinement.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def RefinementFormula (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U U' : SimplicialObject (Over W)) (r : U' ⟶ U)
    (E : CochainComplex (proEtaleRingModules X R) ℤ)
    (f : (total X R W U).obj E ⟶ (total X R W U').obj E) : Prop :=
  ∀ (p : ℕ) (q n : ℤ) (hpq : (p : ℤ) + q = n)
    (x : (E.X q).val.obj (op (U _⦋p⦌).left)),
    f.f n (summand X R W U E p q n hpq x) =
      summand X R W U' E p q n hpq
        ((E.X q).val.map (r.app (op ⦋p⦌)).left.op x)

/-- Refinement by actual sheaf restrictions gives exactly one total chain map.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: the coproduct universal property constructs each degree map from restriction
on its summands. The simplicial and coefficient naturality equations imply
commutation with both signed differentials. The same universal property gives uniqueness. -/
theorem refinement_existsUnique (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U U' : SimplicialObject (Over W)) (r : U' ⟶ U)
    (E : CochainComplex (proEtaleRingModules X R) ℤ) :
    ∃! f : (total X R W U).obj E ⟶ (total X R W U').obj E,
      RefinementFormula X R W U U' r E f := by
  sorry

/-- Refinement, constructed by its unique summand formula.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def refinement (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U U' : SimplicialObject (Over W)) (r : U' ⟶ U)
    (E : CochainComplex (proEtaleRingModules X R) ℤ) :=
  Classical.choose (refinement_existsUnique X R W U U' r E)

/-- Strict compatibility with a commuting square of augmented refinements.
Source: Stacks, Tag 09A2 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: the equation on g, g', r and s equates the composite degree-p site arrows.
Functoriality of the restriction of each coefficient sheaf then equates the
summand maps. Coproduct extensionality gives strict equality on the totals. -/
theorem refinement_naturality {X Y : Scheme.{u}} (h : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (W : X.ProEt) (W' : Y.ProEt) (U U' : SimplicialObject (Over W))
    (V V' : SimplicialObject (Over W')) (r : U' ⟶ U) (s : V' ⟶ V)
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (g' : V' ⋙ Over.forget W' ⟶ U' ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (hcomm : ∀ n : SimplexCategoryᵒᵖ,
      (s.app n).left ≫ g.app n =
        g'.app n ≫ (proEtaleBaseChange h).map (r.app n).left)
    (E : CochainComplex (proEtaleRingModules X R) ℤ) :
    refinement X R W U U' r E ≫
        restriction h R S c W W' U' V' g' E ((pull h R S c).obj E) (𝟙 _) =
      restriction h R S c W W' U V g E ((pull h R S c).obj E) (𝟙 _) ≫
        refinement Y S W' V V' s ((pull h R S c).obj E) := by
  sorry

/-- Consecutive cross-site diagrams compose using the canonical base-change pasting.
Source: Stacks, Tags 03D8 and 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def compositeDiagram {X Y Z : Scheme.{u}} (h : Y ⟶ X) (k : Z ⟶ Y)
    (W : X.ProEt) (W' : Y.ProEt) (W'' : Z.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over W'))
    (L : SimplicialObject (Over W''))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (g' : L ⋙ Over.forget W'' ⟶ V ⋙ Over.forget W' ⋙ proEtaleBaseChange k) :
    L ⋙ Over.forget W'' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange (k ≫ h) :=
  g' ≫ Functor.whiskerRight g (proEtaleBaseChange k) ≫
    Functor.whiskerLeft (U ⋙ Over.forget W) (MorphismProperty.Over.pullbackComp k h).inv

/-- The section formula for the ordinary comparison: two restrictions equal the
composite restriction after the prescribed coefficient and module comparisons.
Source: Stacks, Tag 03D8, lemma-push-pull-composition-modules
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: the conjugate of compositionIso is fixed by fibre-product pasting on sections.
The mate unit equation therefore identifies the successive units with the composite
unit followed by compositionIso. Evaluate at A and restrict along g' and k^*g.
The pasting section formula gives precisely the displayed equality. -/
theorem restriction_comp_section {X Y Z : Scheme.{u}} (h : Y ⟶ X) (k : Z ⟶ Y)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T)
    (M : proEtaleRingModules X R) (A : X.ProEt) (B : Y.ProEt) (C : Z.ProEt)
    (g : B ⟶ (proEtaleBaseChange h).obj A)
    (g' : C ⟶ (proEtaleBaseChange k).obj B) (x : M.val.obj (op A)) :
    restrictSection k S T d ((proEtaleRingModulePullback h R S c).obj M) B C g'
        (restrictSection h R S c M A B g x) =
      ((AcyclicHypercover.compositionIso h R S c k T d).hom.app M).val.app (op C)
        (restrictSection (k ≫ h) R T (proEtaleRingCompositeCoefficients k h R S T c d)
          M A C (g' ≫ (proEtaleBaseChange k).map g ≫
            (MorphismProperty.Over.pullbackComp k h).inv.app A) x) := by
  sorry

/-- Composition of c_g is strict after the prescribed ordinary pullback comparison.
Source: Stacks, Tags 03D8 and 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: apply restriction_comp_section to E^q and the degree-p site arrows. The
coefficient identification is proEtaleRingCompositeCoefficients; the module comparison
is the published compositionIso, whose mate is sectionwise fibre-product pasting.
The two total maps agree on every summand, hence are equal. -/
theorem restriction_comp {X Y Z : Scheme.{u}} (h : Y ⟶ X) (k : Z ⟶ Y)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T)
    (W : X.ProEt) (W' : Y.ProEt) (W'' : Z.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over W'))
    (L : SimplicialObject (Over W''))
    (g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (g' : L ⋙ Over.forget W'' ⟶ V ⋙ Over.forget W' ⋙ proEtaleBaseChange k)
    (E : CochainComplex (proEtaleRingModules X R) ℤ) :
    restriction h R S c W W' U V g E ((pull h R S c).obj E) (𝟙 _) ≫
        restriction k S T d W' W'' V L g' ((pull h R S c).obj E)
          ((pull k S T d).obj ((pull h R S c).obj E)) (𝟙 _) =
      restriction (k ≫ h) R T (proEtaleRingCompositeCoefficients k h R S T c d)
        W W'' U L (compositeDiagram h k W W' W'' U V L g g') E
        ((pull k S T d).obj ((pull h R S c).obj E))
        ((NatIso.mapHomologicalComplex
          (AcyclicHypercover.compositionIso h R S c k T d) (.up ℤ)).hom.app E) := by
  sorry

/-- The unique ordinary identity direct-image comparison, fixed on every section by
base-change identity pasting. Its coefficient identification is the published canonical one.
Source: Stacks, Tag 03D8, identity case
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: restriction along the inverse of pullbackId gives each component. Its inverse
is restriction along pullbackId. Functoriality of sheaf restriction gives the inverse
identities and naturality. The ring inverse-image identity comparison is the adjunction
mate of this same pasting, so these maps are module-linear. The component formula
specifies every sheaf map and hence proves uniqueness. -/
theorem identity_directImage_existsUnique (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃! d : proEtaleRingModuleDirectImage (𝟙 X) R R
        ((proEtaleRingInverseImageId X).app R) ≅ 𝟭 (proEtaleRingModules X R),
      ∀ (M : proEtaleRingModules X R) (W : X.ProEt)
        (x : M.val.obj (op ((proEtaleBaseChange (𝟙 X)).obj W))),
        (d.hom.app M).val.app (op W) x =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app W).op x := by
  sorry

/-- Identity direct-image comparison, selected only from its unique section formula.
Source: Stacks, Tag 03D8 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def identityDirectImage (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  Classical.choose (identity_directImage_existsUnique X R)

/-- The identity pullback comparison is the mate of the fixed identity pasting.
Source: Stacks, Tag 03D8 (blueprint: lem-sfb-hypercover-derived-unit-chain-squares). -/
def identityPullback (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback (𝟙 X) R R ((proEtaleRingInverseImageId X).app R) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleRingModuleAdjunction (𝟙 X) R R ((proEtaleRingInverseImageId X).app R))).symm
      (identityDirectImage X R).symm

/-- Identity restriction gives the identity total map after the canonical coefficient
and ordinary identity comparisons. Source: Stacks, Tags 03D8 and 09A2
(blueprint: lem-sfb-hypercover-derived-unit-chain-squares).
Proof: the unit equation for the identityPullback mate, followed by restriction
along pullbackId.inv, is the identity section map. Apply it in each bidegree and
use the coproduct universal property. This includes empty schemes and zero complexes. -/
theorem restriction_id (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (E : CochainComplex (proEtaleRingModules X R) ℤ) :
    restriction (𝟙 X) R R ((proEtaleRingInverseImageId X).app R) W W U U
      (Functor.whiskerLeft (U ⋙ Over.forget W)
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv)
      E E ((NatIso.mapHomologicalComplex (identityPullback X R) (.up ℤ)).hom.app E) =
        𝟙 ((total X R W U).obj E) := by
  sorry

end AlgebraicGeometry.Scheme.HypercoverUnit
