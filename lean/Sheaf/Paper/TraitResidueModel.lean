/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Sheaf.RepresentationTheory.CompletedAugmentationAlgebra
public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# The canonical residue model on a strictly henselian trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVII, §§1.2.1--1.2.3,
Propositions 1.2.1.2 and 1.2.2.1, Lemma 1.2.3.2, printed pp. 259--262.
(blueprint: lem-per-trait-residue-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Avoid generating unused equality and size lemmas for the dependent data bundles.
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The existing tame root-limit topology, installed on the trait's tame group.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
instance traitTameInertiaTopology (Ω : Type u) [Field Ω] (p : ℕ) :
    TopologicalSpace (TameRoots.limitSubgroup Ω p) := TameRoots.limitTopology Ω p

/-- Prime-field coefficients, lifted to the universe of modules on the small étale site.
Source: ILO XVII §1.2, `n = ell` (blueprint: lem-per-trait-residue-model). -/
def TraitCoefficients (ell : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod ell)

/-- The lifted prime field structure.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
instance traitCoefficientsField (ell : ℕ) [Fact ell.Prime] :
    Field (TraitCoefficients.{u} ell) := ULift.field

/-- The characteristic exponent of the closed residue field, including exponent one.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
abbrev traitCharacteristicExponent (R : Type u) [CommRing R] [IsLocalRing R] :=
  ringExpChar (IsLocalRing.ResidueField R)

/-- The separable closure inside the chosen algebraically closed generic field.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitSeparableField (R : Type u) [CommRing R] [IsDomain R]
    (Ω : Type u) [Field Ω] [Algebra (FractionRing R) Ω] : Type u :=
  separableClosure (FractionRing R) Ω

/-- The separable closure in an algebraically closed field is separably closed.
Source: ILO XVII §1.2 and `IsSepClosure.sep_closed`
(blueprint: lem-per-trait-residue-model). -/
instance traitSeparableFieldIsSepClosed (R : Type u) [CommRing R] [IsDomain R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω] :
    IsSepClosed (TraitSeparableField R Ω) :=
  IsSepClosure.sep_closed (FractionRing R)

/-- The actual Galois automorphism group, with Mathlib's Krull topology.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitGaloisGroup (R : Type u) [CommRing R] [IsDomain R]
    (Ω : Type u) [Field Ω] [Algebra (FractionRing R) Ω] :=
  TraitSeparableField R Ω ≃ₐ[FractionRing R] TraitSeparableField R Ω

/-- The geometric generic point with the same separable closure as the chosen point.
Passing from the algebraically closed field to this separably closed field changes no stalk.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
abbrev traitGenericPoint (R : Type u) [CommRing R] [IsDomain R]
    (Ω : Type u) [Field Ω] [Algebra (FractionRing R) Ω] :
    Spec (.of (TraitSeparableField R Ω)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) (TraitSeparableField R Ω)).comp
    (algebraMap R (FractionRing R))))

/-- The closed geometric point of the strictly henselian trait, represented by its
separably closed residue field. Source: ILO XVII §1.2
(blueprint: lem-per-trait-residue-model). -/
abbrev traitClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Coefficient-module sheaves on the trait.
Source: ILO XVII §1.2.2 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitSheaves (Λ : Type (u + 1)) [CommRing Λ] (R : Type u) [CommRing R] :=
  Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)

/-- The actual generic stalk functor.
Source: ILO XVII §1.2.2 (blueprint: lem-per-trait-residue-model). -/
abbrev traitGenericStalk (Λ : Type (u + 1)) [CommRing Λ] (R : Type u)
    [CommRing R] [IsDomain R] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra (FractionRing R) Ω] :=
  (Scheme.pointSmallEtale (traitGenericPoint R Ω)).sheafFiber (A := ModuleCat.{u + 1} Λ)

/-- The actual closed stalk functor.
Source: ILO XVII §1.2.2 (blueprint: lem-per-trait-residue-model). -/
abbrev traitClosedStalk (Λ : Type (u + 1)) [CommRing Λ] (R : Type u)
    [CommRing R] [IsStrictlyHenselianLocalRing R] :=
  (Scheme.pointSmallEtale (traitClosedPoint R)).sheafFiber (A := ModuleCat.{u + 1} Λ)

/-- The coefficient-linear global germ, given by the actual stalk colimit cocone.
Source: ILO XVII §1.2.2 (blueprint: lem-per-trait-residue-model). -/
def traitResidueGlobalGerm (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⟶
      (Scheme.pointSmallEtale x).sheafFiber :=
  (Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) X)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf _ _)
      ((Scheme.pointSmallEtale x).toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 X))
        (Over.homMk x (Category.comp_id x)))

/-- A topological generator means that its integral powers are dense.
Source: ILO XVII Proposition 1.2.1.2 (blueprint: lem-per-trait-residue-model). -/
def traitIsGenerator {G : Type u} [Group G] [TopologicalSpace G] (σ : G) : Prop :=
  closure (Set.range (fun n : ℤ ↦ σ ^ n)) = Set.univ

/-- The inverse-limit algebra and tame quotient, with their defining formulas.
These are conclusions of the proposition, not hypotheses supplied by its user.
Source: ILO XVII §1.2 and Proposition 1.2.1.2
(blueprint: lem-per-trait-residue-model). -/
structure TraitResidueAlgebra (Λ : Type (u + 1)) [CommRing Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (Ω : Type u) [Field Ω] [Algebra (FractionRing R) Ω] where
  tame : TraitGaloisGroup R Ω →* TameRoots.limitSubgroup Ω (traitCharacteristicExponent R)
  tame_continuous : Continuous tame
  tame_surjective : Function.Surjective tame
  tame_roots : ∀ (π : R), Irreducible π →
    ∀ (r : TameRoots.Order (traitCharacteristicExponent R) → TraitSeparableField R Ω),
      (∀ d, (r d) ^ d.val = algebraMap (FractionRing R) (TraitSeparableField R Ω)
        (algebraMap R (FractionRing R) π)) →
      (∀ d e, d.val ∣ e.val → (r e) ^ (e.val / d.val) = r d) →
      ∀ (h : TraitGaloisGroup R Ω) d,
        ((tame h).val d : Ω) * algebraMap (TraitSeparableField R Ω) Ω (r d) =
          algebraMap (TraitSeparableField R Ω) Ω (h (r d))
  wild_pro_p : ∀ (Q : Type u) [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (f : tame.ker →* Q),
    Continuous f → Function.Surjective f → ∃ n : ℕ, Nat.card Q = traitCharacteristicExponent R ^ n
  wild_trivial : traitCharacteristicExponent R = 1 → Subsingleton tame.ker
  generator_exists :
    ∃ σ : TameRoots.limitSubgroup Ω (traitCharacteristicExponent R), traitIsGenerator σ
  augmentationBasis : ∀ σ : TameRoots.limitSubgroup Ω (traitCharacteristicExponent R),
    traitIsGenerator σ →
      Rep.CompletedAugmentation.Algebra Λ
        (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R)) ≃ₗ[
          Rep.CompletedAugmentation.Algebra Λ
            (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R))]
        Rep.CompletedAugmentation.Ideal Λ
          (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R))
  augmentationBasis_formula : ∀ σ h a,
    (augmentationBasis σ h a).val = (1 - Rep.CompletedAugmentation.groupElement Λ _ σ) * a

/-- The algebra acting on wild invariants.
Source: ILO XVII Definition 1.2.1.1 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitResidueRing (Λ : Type (u + 1)) [CommRing Λ]
    (R : Type u) [CommRing R] [IsLocalRing R] (Ω : Type u) [Field Ω] : Type (u + 1) :=
  Rep.CompletedAugmentation.Algebra Λ (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R))

/-- The augmentation ideal in the actual inverse-limit algebra.
Source: ILO XVII Definition 1.2.1.1 (blueprint: lem-per-trait-residue-model). -/
abbrev traitResidueIdeal (Λ : Type (u + 1)) [CommRing Λ]
    (R : Type u) [CommRing R] [IsLocalRing R] (Ω : Type u) [Field Ω] :
    Ideal (TraitResidueRing Λ R Ω) :=
  Rep.CompletedAugmentation.Ideal Λ (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R))

/-- The canonical stalk actions, invariant subfunctor, completed action and averaging,
all specified by their formulas on germs and finite quotients.  In particular the
inclusion identifies the invariant functor with the actual fixed-vector submodule.
Source: ILO XVII §§1.2.2--1.2.3 (blueprint: lem-per-trait-residue-model). -/
structure TraitResidueStalkData (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    (B : TraitResidueAlgebra Λ R Ω) where
  action : ∀ M : TraitSheaves Λ R,
    Representation Λ (TraitGaloisGroup R Ω) ((traitGenericStalk Λ R Ω).obj M)
  action_discrete : ∀ M v, IsOpen {h | action M h v = v}
  action_natural : ∀ {M M' : TraitSheaves Λ R} (f : M ⟶ M') h v,
    (traitGenericStalk Λ R Ω).map f (action M h v) =
      action M' h ((traitGenericStalk Λ R Ω).map f v)
  action_germ : ∀ (M : TraitSheaves Λ R) (h : TraitGaloisGroup R Ω)
    (X : (Spec (.of R)).Etale)
    (x y : (Scheme.pointSmallEtale (traitGenericPoint R Ω)).fiber.obj X),
    y.left = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ x.left →
    ∀ z : M.obj.obj (op X),
      action M h ((Scheme.pointSmallEtale (traitGenericPoint R Ω)).toPresheafFiber
        X x M.obj z) =
      (Scheme.pointSmallEtale (traitGenericPoint R Ω)).toPresheafFiber X y M.obj z
  closedGerm : Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅
    traitClosedStalk Λ R
  closedGerm_formula : closedGerm.hom = traitResidueGlobalGerm Λ (traitClosedPoint R)
  specialization : traitClosedStalk Λ R ⟶ traitGenericStalk Λ R Ω
  specialization_formula : closedGerm.hom ≫ specialization =
    traitResidueGlobalGerm Λ (traitGenericPoint R Ω)
  invariants : TraitSheaves Λ R ⥤ ModuleCat.{u + 1} Λ
  inclusion : invariants ⟶ traitGenericStalk Λ R Ω
  inclusion_injective : ∀ M, Function.Injective (inclusion.app M)
  inclusion_range : ∀ M, Set.range (inclusion.app M) =
    {v | ∀ h : B.tame.ker, action M h.val v = v}
  specializationInvariant : traitClosedStalk Λ R ⟶ invariants
  specializationInvariant_formula : specializationInvariant ≫ inclusion = specialization
  tameAction : ∀ M : TraitSheaves Λ R,
    Representation Λ (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R)) (invariants.obj M)
  tameAction_formula : ∀ M h n,
    inclusion.app M (tameAction M (B.tame h) n) = action M h (inclusion.app M n)
  [invariantsModule : ∀ M, Module (TraitResidueRing Λ R Ω) (invariants.obj M)]
  [invariantsTower : ∀ M,
    IsScalarTower Λ (TraitResidueRing Λ R Ω) (invariants.obj M)]
  [invariantsCommute : ∀ M,
    SMulCommClass (TraitResidueRing Λ R Ω) Λ (invariants.obj M)]
  completedAction_formula : ∀ (M : TraitSheaves Λ R)
    (U : OpenNormalSubgroup (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R)))
    (n : invariants.obj M),
    (∀ g : U, tameAction M g.val n = n) → ∀ a : TraitResidueRing Λ R Ω,
      a • n = (a.val U).coeff.sum (fun q c ↦ c • tameAction M (Quotient.out q) n)
  completedAction_natural : ∀ {M M' : TraitSheaves Λ R} (f : M ⟶ M') (a : TraitResidueRing Λ R Ω) n,
    invariants.map f (a • n) = a • invariants.map f n
  averaging : traitGenericStalk Λ R Ω ⟶ invariants
  averaging_retraction : inclusion ≫ averaging = 𝟙 invariants
  averaging_formula : ∀ (M : TraitSheaves Λ R) (v : (traitGenericStalk Λ R Ω).obj M)
    (U : OpenSubgroup B.tame.ker) [U.toSubgroup.Normal]
    [Fintype (B.tame.ker ⧸ U.toSubgroup)],
    (∀ h : U, action M h.val.val v = v) →
      inclusion.app M (averaging.app M v) =
        (Nat.card (B.tame.ker ⧸ U.toSubgroup) : Λ)⁻¹ •
          ∑ q : B.tame.ker ⧸ U.toSubgroup, action M (Quotient.out q).val v


/-- Finite-width totalization uses Mathlib's coproduct total complex. Its summands are
indexed by `q + i = n` and its differential is the usual signed total differential.
Source: ILO XVII Proposition 1.2.2.1 (blueprint: lem-per-trait-residue-model). -/
def traitTotalFunctor {Λ : Type (u + 1)} [CommRing Λ]
    {C : Type v} [Category C] [Preadditive C]
    (F : C ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ) [F.Additive] :
    CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
  F.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u + 1} Λ) (.up ℤ) (.up ℤ) (.up ℤ)

/-- Totalize a natural transformation termwise, using the same total complex.
Source: ILO XVII §1.2.3 (blueprint: lem-per-trait-residue-model). -/
def traitTotalTransformation {Λ : Type (u + 1)} [CommRing Λ]
    {C : Type v} [Category C] [Preadditive C]
    {F F' : C ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ} [F.Additive] [F'.Additive]
    (f : F ⟶ F') : traitTotalFunctor F ⟶ traitTotalFunctor F' :=
  Functor.whiskerRight (f.mapHomologicalComplex (.up ℤ))
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u + 1} Λ) (.up ℤ) (.up ℤ) (.up ℤ))

/-- The Tate line, with its actual roots-of-unity carrier.
Source: ILO XVII §1.2.3 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitTateLine (ell : ℕ) (Ω : Type u) [Field Ω] :=
  ULift.{u + 1} (Additive (rootsOfUnity ell Ω))

/-- A coefficient-module functor representing maps linear for a specified ring action.
The evaluations are injective and their image is precisely the additive A-linear maps.
Source: ILO XVII Proposition 1.2.2.1 (blueprint: lem-per-trait-residue-model). -/
structure TraitIdealHomFunctor (Λ A : Type (u + 1)) [Field Λ] [Ring A]
    (J : Ideal A) (C : Type v) [Category C] (N : C ⥤ ModuleCat.{u + 1} Λ)
    (smul : ∀ M : C, A → N.obj M → N.obj M) where
  idealHom : C ⥤ ModuleCat.{u + 1} Λ
  apply : ∀ M : C, idealHom.obj M → J → N.obj M
  apply_add : ∀ M (b c : idealHom.obj M) a,
    apply M (b + c) a = apply M b a + apply M c a
  apply_smul : ∀ M (r : Λ) (b : idealHom.obj M) a,
    apply M (r • b) a = r • apply M b a
  apply_right_add : ∀ M (b : idealHom.obj M) x y,
    apply M b (x + y) = apply M b x + apply M b y
  apply_right_linear : ∀ M (b : idealHom.obj M) (a : A) (x : J),
    apply M b ⟨a * x.val, J.mul_mem_left a x.property⟩ = smul M a (apply M b x)
  apply_injective : ∀ M, Function.Injective (apply M)
  apply_range : ∀ M, Set.range (apply M) =
    {b | (∀ x y, b (x + y) = b x + b y) ∧ ∀ (a : A) (x : J),
      b ⟨a * x.val, J.mul_mem_left a x.property⟩ = smul M a (b x)}
  apply_natural : ∀ {M M' : C} (f : M ⟶ M') (b : idealHom.obj M) (a : J),
    apply M' (idealHom.map f b) a = N.map f (apply M b a)

/-- The Hom functor for the actual augmentation ideal and actual invariant action.
Source: ILO XVII Proposition 1.2.2.1 (blueprint: lem-per-trait-residue-model). -/
abbrev TraitResidueIdealData (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    (B : TraitResidueAlgebra Λ R Ω) (D : TraitResidueStalkData Λ R Ω B) :=
  TraitIdealHomFunctor Λ (TraitResidueRing Λ R Ω) (traitResidueIdeal Λ R Ω)
    (TraitSheaves Λ R) D.invariants
    (fun M a n ↦ @SMul.smul _ _ (D.invariantsModule M).toSMul a n)

/-- The three-term exact complex on sheaves of coefficients.
Source: ILO XVII Propositions 1.2.1.2 and 1.2.2.1 (blueprint: lem-per-trait-residue-model).
Proof: the source identifies the three terms with closed stalks, tame invariants and
Hom from the augmentation ideal; exactness follows from finite p-group averaging and
finite cyclic quotient calculations described in the node proof. -/
structure TraitResidueComplexCore (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    (B : TraitResidueAlgebra Λ R Ω) (D : TraitResidueStalkData Λ R Ω B)
    (I : TraitResidueIdealData Λ R Ω B D) where
  F : TraitSheaves Λ R ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ
  [F_additive : F.Additive]
  degree0 : F ⋙ HomologicalComplex.eval _ (.up ℤ) 0 ≅ traitClosedStalk Λ R
  degree1 : F ⋙ HomologicalComplex.eval _ (.up ℤ) 1 ≅ D.invariants
  degree2 : F ⋙ HomologicalComplex.eval _ (.up ℤ) 2 ≅ I.idealHom
  outside : ∀ M (i : ℤ), i < 0 ∨ 2 < i → IsZero ((F.obj M).X i)
  firstDifferential : ∀ M,
    (F.obj M).d 0 1 ≫ degree1.hom.app M =
      degree0.hom.app M ≫ D.specializationInvariant.app M
  lastDifferential : ∀ M m a,
    I.apply M (degree2.hom.app M ((F.obj M).d 1 2 (degree1.inv.app M m))) a =
      @SMul.smul _ _ (D.invariantsModule M).toSMul a.val m
  exact : ∀ (i : ℤ),
    PreservesFiniteLimits (F ⋙ HomologicalComplex.eval _ (.up ℤ) i) ∧
      PreservesFiniteColimits (F ⋙ HomologicalComplex.eval _ (.up ℤ) i)
  preservesQuasiIso : ∀ {K L : CochainComplex (TraitSheaves Λ R) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso ((traitTotalFunctor F).map f)

attribute [instance] TraitResidueComplexCore.F_additive

/-- The Tate twist, source complex and canonical generator transition maps.
Source: ILO XVII Definition 1.2.3.1 and Lemma 1.2.3.2
(blueprint: lem-per-trait-residue-model). -/
structure TraitResidueTwistData (ell : ℕ) (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    (B : TraitResidueAlgebra Λ R Ω) (D : TraitResidueStalkData Λ R Ω B)
    (I : TraitResidueIdealData Λ R Ω B D) (C : TraitResidueComplexCore Λ R Ω B D I) where
  [tateModule : Module Λ (TraitTateLine ell Ω)]
  rootProjection : TameRoots.limitSubgroup Ω (traitCharacteristicExponent R) →* rootsOfUnity ell Ω
  rootProjection_formula : ∀ (d : TameRoots.Order (traitCharacteristicExponent R)),
    d.val = ell → ∀ g, ((rootProjection g).val : Ω) = (g.val d : Ω)
  twistHom : ∀ (N : ModuleCat.{u + 1} Λ),
    ((ihom (ModuleCat.of Λ (TraitTateLine ell Ω))).obj N) ≃
      {f : Additive (TameRoots.limitSubgroup Ω (traitCharacteristicExponent R)) →+ N //
        Continuous (fun g ↦ (WithTopology.equiv N ⊥).symm (f g))}
  twistHom_formula : ∀ (N : ModuleCat.{u + 1} Λ)
    (f : (ihom (ModuleCat.of Λ (TraitTateLine ell Ω))).obj N) g,
    (twistHom N f).val g = f.hom (ULift.up (Additive.ofMul (rootProjection g.toMul)))
  sourceFunctor : TraitSheaves Λ R ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ
  [source_additive : sourceFunctor.Additive]
  sourceFormula : sourceFunctor ≅ traitGenericStalk Λ R Ω ⋙
    ihom (ModuleCat.of Λ (TraitTateLine ell Ω)) ⋙
      HomologicalComplex.single (ModuleCat.{u + 1} Λ) (.up ℤ) 2
  sSigma : ∀ σ : TameRoots.limitSubgroup Ω (traitCharacteristicExponent R),
    traitIsGenerator σ → (sourceFunctor ⟶ C.F)
  sSigma_formula : ∀ σ h M
    (f : (ihom (ModuleCat.of Λ (TraitTateLine ell Ω))).obj
      ((traitGenericStalk Λ R Ω).obj M)),
    I.apply M (C.degree2.hom.app M ((sSigma σ h).app M |>.f 2 <|
      (sourceFormula.inv.app M).f 2
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 2
          ((ihom (ModuleCat.of Λ (TraitTateLine ell Ω))).obj
            ((traitGenericStalk Λ R Ω).obj M))).inv f)))
      (B.augmentationBasis σ h 1) =
        D.averaging.app M (f.hom (ULift.up (Additive.ofMul (rootProjection σ))))
  uniqueNaturalHomotopy :
    ∀ (σ τ : TameRoots.limitSubgroup Ω (traitCharacteristicExponent R))
      (hσ : traitIsGenerator σ) (hτ : traitIsGenerator τ),
    ∃! h : ∀ M, Homotopy ((sSigma σ hσ).app M) ((sSigma τ hτ).app M),
      ∀ {M M' : TraitSheaves Λ R} (f : M ⟶ M') i j,
        (sourceFunctor.map f).f i ≫ (h M').hom i j =
          (h M).hom i j ≫ (C.F.map f).f j

attribute [instance] TraitResidueTwistData.source_additive

/-- The open generic locus, defined as the complement of the closed point.
Source: ILO XVII §1.2 (blueprint: lem-per-trait-residue-model). -/
def traitGenericOpen (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (.of R)).Opens :=
  ⟨{IsLocalRing.closedPoint R}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩

/-- The actual stalk functor applied termwise to complexes.
Source: ILO XVII §1.2.3 (blueprint: lem-per-trait-residue-model). -/
abbrev traitGenericComplex (Λ : Type (u + 1)) [CommRing Λ] (R : Type u)
    [CommRing R] [IsDomain R] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra (FractionRing R) Ω] :=
  (traitGenericStalk Λ R Ω).mapHomologicalComplex (.up ℤ)

/-- Tensoring a complex with the actual Tate line, term by term.
Source: ILO XVII Definition 1.2.3.1 (blueprint: lem-per-trait-residue-model). -/
def traitTensorComplex {Λ : Type (u + 1)} [CommRing Λ] (L : ModuleCat.{u + 1} Λ) :
    CochainComplex (ModuleCat.{u + 1} Λ) ℤ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
  (MonoidalCategory.tensorLeft L).mapHomologicalComplex (.up ℤ)

set_option backward.isDefEq.respectTransparency true

/-- The derived comparison and residue transition, with their formulas on representatives.
The evaluation isomorphism is fixed by ordinary tensor-Hom evaluation on every summand;
the residue equation holds for every generator and every bounded below representative.
Source: ILO XVII Proposition 1.2.2.1, Definition 1.2.3.1 and Lemma 1.2.3.2
(blueprint: lem-per-trait-residue-model). -/
structure TraitResidueDerivedData (ell : ℕ) (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    (B : TraitResidueAlgebra Λ R Ω) (D : TraitResidueStalkData Λ R Ω B)
    (I : TraitResidueIdealData Λ R Ω B D) (C : TraitResidueComplexCore Λ R Ω B D I)
    (T : TraitResidueTwistData ell Λ R Ω B D I C) where
  augmentation : supportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R) ⋙
    HomologicalComplex.single (ModuleCat.{u + 1} Λ) (.up ℤ) 0 ⟶ C.F
  augmentation_formula : ∀ M,
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      ((supportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R)).obj M)).inv ≫
      (augmentation.app M).f 0 ≫ C.degree0.hom.app M =
    (supportedEtaleSectionsι Λ (Spec (.of R)) (traitGenericOpen R)).app M ≫
      D.closedGerm.hom.app M
  totalAugmentation :
    (supportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R)).mapHomologicalComplex
      (.up ℤ) ⟶ traitTotalFunctor C.F
  totalAugmentation_formula : ∀ (K : CochainComplex (TraitSheaves Λ R) ℤ) (q : ℤ),
    (totalAugmentation.app K).f q =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        ((supportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R)).obj (K.X q))).inv ≫
      (augmentation.app (K.X q)).f 0 ≫
      HomologicalComplex₂.ιTotal ((C.F.mapHomologicalComplex (.up ℤ)).obj K)
        (.up ℤ) q 0 q (add_zero q)
  comparison : DerivedCategory.Plus.Q ⋙
      derivedSupportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R) ≅
    CochainComplex.Plus.ι _ ⋙ traitTotalFunctor C.F ⋙ DerivedCategory.Q
  comparison_normalization : ∀ (K : CochainComplex.Plus (TraitSheaves Λ R)),
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} Λ)).inv.app
        (((supportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R)).mapHomologicalComplex
          (.up ℤ)).obj K.obj) ≫
      (DerivedCategory.Plus.QhCompιIsoιCompQh (ModuleCat.{u + 1} Λ)).inv.app
        ((supportedEtaleSections Λ (Spec (.of R))
          (traitGenericOpen R)).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (TraitSheaves Λ R)).obj K)) ≫
      DerivedCategory.Plus.ι.map
        ((supportedEtaleSections Λ (Spec (.of R))
          (traitGenericOpen R)).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient (TraitSheaves Λ R)).obj K)) ≫
      comparison.hom.app K = DerivedCategory.Q.map (totalAugmentation.app K.obj)
  genericDerived : DerivedCategory.Plus (TraitSheaves Λ R) ⥤
    DerivedCategory (ModuleCat.{u + 1} Λ)
  genericFactor : DerivedCategory.Plus.Q ⋙ genericDerived ≅
    CochainComplex.Plus.ι _ ⋙ traitGenericComplex Λ R Ω ⋙ DerivedCategory.Q
  tensorDerived : DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
    DerivedCategory (ModuleCat.{u + 1} Λ)
  tensorFactor : DerivedCategory.Q ⋙ tensorDerived ≅
    @traitTensorComplex Λ _ (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule) ⋙
      DerivedCategory.Q
  evaluation : traitTotalFunctor T.sourceFunctor ⋙
      @traitTensorComplex Λ _ (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule) ≅
    traitGenericComplex Λ R Ω ⋙ shiftFunctor _ (-2 : ℤ)
  evaluation_formula : ∀ (K : CochainComplex (TraitSheaves Λ R) ℤ) (q n : ℤ)
    (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (q, 2) = n) (h' : q = n + -2),
    (MonoidalCategory.tensorLeft
      (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule)).map
        (HomologicalComplex₂.ιTotal
          ((T.sourceFunctor.mapHomologicalComplex (.up ℤ)).obj K) (.up ℤ) q 2 n h) ≫
      (evaluation.hom.app K).f n ≫
      (CochainComplex.shiftFunctorObjXIso
        ((traitGenericComplex Λ R Ω).obj K) (-2) n q h').hom =
    (MonoidalCategory.tensorLeft
      (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule)).map
        ((T.sourceFormula.hom.app (K.X q)).f 2 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 2
            ((ihom
              (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule)).obj
                ((traitGenericStalk Λ R Ω).obj (K.X q)))).hom) ≫
      (ihom.ev (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule)).app
        ((traitGenericStalk Λ R Ω).obj (K.X q))
  negativeResidue : genericDerived ⋙ shiftFunctor _ (-2 : ℤ) ⟶
    derivedSupportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R) ⋙ tensorDerived
  residue_formula : ∀ σ (hσ : traitIsGenerator σ)
    (K : CochainComplex.Plus (TraitSheaves Λ R)),
    DerivedCategory.Q.map (evaluation.hom.app K.obj) ≫
      (DerivedCategory.Q.commShiftIso (-2 : ℤ)).hom.app
        ((traitGenericComplex Λ R Ω).obj K.obj) ≫
      (genericFactor.inv.app K)⟦(-2 : ℤ)⟧' ≫
      negativeResidue.app (DerivedCategory.Plus.Q.obj K) ≫
      tensorDerived.map (comparison.hom.app K) ≫
      tensorFactor.hom.app ((traitTotalFunctor C.F).obj K.obj) =
    DerivedCategory.Q.map
      ((@traitTensorComplex Λ _
        (@ModuleCat.of Λ _ (TraitTateLine ell Ω) _ T.tateModule)).map
          ((traitTotalTransformation (T.sSigma σ hσ)).app K.obj))

/-- All clauses of the supported residue model, packaged from its canonical components.
Source: ILO XVII §§1.2.1--1.2.3 (blueprint: lem-per-trait-residue-model).
The component structures expose every object, differential, exactness, twist, evaluation,
and natural-homotopy clause of the source statement. -/
abbrev TraitResidueModelData (ell : ℕ) (Λ : Type (u + 1)) [Field Λ]
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω] :=
  Σ B : TraitResidueAlgebra Λ R Ω,
    Σ D : TraitResidueStalkData Λ R Ω B,
      Σ I : TraitResidueIdealData Λ R Ω B D,
        Σ C : TraitResidueComplexCore Λ R Ω B D I,
          Σ T : TraitResidueTwistData ell Λ R Ω B D I C,
            TraitResidueDerivedData ell Λ R Ω B D I C T

/-- The residue transition, shifted from its equivalent degree-minus-two form.
Source: ILO XVII Definition 1.2.3.1 (blueprint: lem-per-trait-residue-model). -/
def traitResidueTransition {ell : ℕ} {Λ : Type (u + 1)} [Field Λ]
    {R : Type u} [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω]
    {B : TraitResidueAlgebra Λ R Ω} {D : TraitResidueStalkData Λ R Ω B}
    {I : TraitResidueIdealData Λ R Ω B D} {C : TraitResidueComplexCore Λ R Ω B D I}
    {T : TraitResidueTwistData ell Λ R Ω B D I C}
    (E : TraitResidueDerivedData ell Λ R Ω B D I C T) :
    E.genericDerived ⟶ derivedSupportedEtaleSections Λ (Spec (.of R)) (traitGenericOpen R) ⋙
      E.tensorDerived ⋙ shiftFunctor _ (2 : ℤ) :=
  (Functor.rightUnitor E.genericDerived).inv ≫
    Functor.whiskerLeft E.genericDerived
      ((shiftFunctorZero _ ℤ).inv ≫ (shiftFunctorAdd' _ (-2 : ℤ) 2 0 rfl).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.negativeResidue (shiftFunctor _ (2 : ℤ)) ≫
    (Functor.associator _ _ _).hom

/-- The canonical three-term residue model and derived residue transition on a trait.
Source: ILO XVII Propositions 1.2.1.2 and 1.2.2.1, Definition 1.2.3.1, Lemma 1.2.3.2.
(blueprint: lem-per-trait-residue-model).

Proof: the canonical tame character identifies the tame quotient with the compatible
prime-to-p roots of unity and gives its pro-p kernel and procyclic generator
[lem-per-trait-tame-algebra]. In each finite cyclic group ring, coefficient comparison
identifies the kernel of 1-sigma with the norm line and its image with augmentation zero.
Projecting solutions from the quotient of order ell*d kills the ambiguity ell*N_d;
this gives a compatible unique solution in the completed algebra and the free basis of I.
The stalk/triple equivalence [lem-per-trait-sheaf-gluing] identifies specialization and
componentwise exactness. Averaging finite p-group orbits is independent of refinement,
natural, and a retraction onto wild invariants, proving exactness of invariants.
Evaluation on the free basis of I proves exactness of the third term. The specialization
is H-invariant, so the displayed differentials compose to zero.
For an injective sheaf the generic module and its wild invariants are injective by the
exact-left-adjoint criterion [lem-exc-rg-right-adjoint-preserves-injectives]. Extending
maps of triples identifies degree-zero supported sections and kills middle cohomology.
To kill final cohomology, extend (1-z)B_(ell*d) -> N across the finite cyclic group ring;
the norm kills each vector, so this is well-defined and yields (1-sigma)y=x.
Enough injectives and bounded below injective replacements reduce the derived comparison
to this computation [lem-weil-pbc-module-sheaves-grothendieck-abelian],
[lem-sp-grothendieck-enough-injectives],
[lem-sc-bounded-below-injective-resolution-existence]. A three-column filtration shows
that totalization preserves quasi-isomorphisms; row exactness gives the normalized
comparison to the right derived supported-section functor.
Continuous additive maps G -> N factor through G/ell*G = mu_ell, giving the twist Hom
identification. Evaluate at sigma, average, and invert evaluation on 1-sigma to define
s_sigma. Natural homotopies reduce by the triple maps and averaging to discrete tame
modules. Their natural endomorphisms are the completed algebra, by evaluation on regular
finite quotient modules. If 1-tau=u(1-sigma) and tau=sigma^alpha, the maps differ by
 g=alpha/u. The finite geometric-sum formula gives epsilon(u)=alpha mod ell, hence
1-g lies in I. Its unique division by 1-sigma is the unique natural homotopy.
Totalizing these natural homotopies cancels the vertical terms with opposite signs.
Localization therefore gives a map independent of the generator and representative.
Tensor-Hom evaluation for the one-dimensional Tate line gives the stated residue map. -/
theorem exists_traitResidueModel (ell : ℕ) [Fact ell.Prime]
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] (_hell : IsUnit (ell : R))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing R) Ω] :
    Nonempty (TraitResidueModelData ell (TraitCoefficients.{u} ell) R Ω) := by
  sorry

end AlgebraicGeometry.Etale
