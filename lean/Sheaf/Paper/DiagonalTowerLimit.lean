/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.DiagonalTowerSystem
public import Sheaf.Paper.DiagonalTowerLimitInterface
public import Sheaf.Paper.DiagonalLimitAssembly
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.FormalClosedSupportIILimits
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import all Sheaf.Paper.FormalClosedSupportIILimits
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The completed diagonal class

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.md, clauses 1--3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

Strict towers have constant discrete Z_l coefficients. Only the final arrow has
coefficients in the completed ring sheaf. Positive exponent n+1 is indexed by n.

## Main statements

- `diagonalTower_limit`: completed endpoints and the unique completed diagonal arrow.
- `diagonalTower_directImage`: levelwise direct image and its canonical limit comparison.
- `diagonalCompletedTwist_limits`: exactness, products and inverse limits for both twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u v w a b c vc r
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] diagonalCompletedSource diagonalOrdinaryRlim
  diagonalSourceLimitMap diagonalTargetLimitMap diagonalRootLimitComparison
  diagonalFiniteCycleNormalization DiagonalArrowCompatibility
  diagonalCompleteDataAssertion DiagonalLimitDataSpec
attribute [local irreducible] diagonalSingleLimitComparison diagonalExactFunctorExtImage
attribute [local irreducible] CategoryTheory.Abelian.Ext

@[instance_reducible] private def diagonalResidueInvertible (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    ∀ x : X, Invertible (ℓ : X.residueField x) := by
  classical
  have hℓ : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr (by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact fun h ↦ hpℓ (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one))
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom
  have hX : IsUnit (ℓ : Γ(X, ⊤)) := by simpa only [map_natCast] using hℓ.map φ
  intro x
  let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (ℓ : X.residueField x) from by
    simpa only [map_natCast] using hX.map ψ).invertible


private theorem diagonalLineLimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (P : SheafOfModules.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ)))
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ)))]
    (hP : ∀ U : X.ProEt, ∃ s : Sieve U, s ∈ Scheme.ProEt.topology X U ∧
      ∀ (V : X.ProEt) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ SheafOfModules.unit
          ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ)).over V))) :
    (SheafOfModules.siteSheafTensorRight (A := Scheme.purTwistZlCompletion X ℓ) P).Additive ∧
    PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (A := Scheme.purTwistZlCompletion X ℓ) P) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (A := Scheme.purTwistZlCompletion X ℓ) P) ∧
    (∃ (_ : ((𝟭 _).prod' ((Functor.const _).obj
      ((DerivedCategory.singleFunctor _ 0).obj P)) ⋙
        SheafOfModules.siteDerivedTensorIndependentCoefficients
          (Scheme.ProEt.topology X) (Scheme.purTwistZlCompletion X ℓ)).CommShift ℤ),
      CondensedRing.ClosedSupportLimitFunctorProperties
        ((𝟭 _).prod' ((Functor.const _).obj
          ((DerivedCategory.singleFunctor _ 0).obj P)) ⋙
            SheafOfModules.siteDerivedTensorIndependentCoefficients
              (Scheme.ProEt.topology X) (Scheme.purTwistZlCompletion X ℓ))) := by
  classical
  open SheafOfModules MonoidalCategory in
  obtain ⟨_, hAdd, _, hLim, hCol, _, _, hflat, _, _, _, e, _, _, a, b, _⟩ :=
    LineEvaluation.evaluation_inverse_pair.{u + 1, u, u + 1} (Scheme.purTwistZlCompletion X ℓ) P hP
  let eqv := CategoryTheory.Equivalence.mk
    (MonoidalCategory.tensorRight P)
    (MonoidalCategory.tensorRight (SheafOfModules.LineEvaluation.dual.{u + 1, u, u + 1}
      (Scheme.purTwistZlCompletion X ℓ) P)) a.symm b
  have : (MonoidalCategory.tensorRight P).IsEquivalence := eqv.isEquivalence_functor
  let iso := SheafOfModules.siteSheafTensorRightIso
    (Scheme.purTwistZlCompletion X ℓ) P
  have hAdd' : (SheafOfModules.siteSheafTensorRight
      (A := Scheme.purTwistZlCompletion X ℓ) P).Additive :=
    Functor.additive_of_iso iso.symm
  have : (SheafOfModules.siteSheafTensorRight
      (A := Scheme.purTwistZlCompletion X ℓ) P).IsEquivalence :=
    Functor.isEquivalence_of_iso iso.symm
  refine ⟨hAdd', inferInstance, inferInstance, ?_⟩
  have := hAdd
  have := hLim
  have := hCol
  obtain ⟨_, _, _, _, _, _, _, _, s, ht, chi, _, _, eta, _, _, _⟩ :=
    SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      (Scheme.purTwistZlCompletion X ℓ) P hflat
  let := s
  have := ht
  let D := SheafOfModules.FlatSingleDerivedNormalization.derived
    (Scheme.purTwistZlCompletion X ℓ) P
  have : D.IsEquivalence := Functor.isEquivalence_of_iso eta.symm
  let eP := (DerivedCategory.singleFunctorIsoCompQ _ 0).app P
  let T := SheafOfModules.siteDerivedTensorIndependentCoefficients
    (Scheme.ProEt.topology X) (Scheme.purTwistZlCompletion X ℓ)
  let c : D ≅ (𝟭 _).prod' ((Functor.const _).obj
      ((DerivedCategory.singleFunctor _ 0).obj P)) ⋙ T :=
    NatIso.ofComponents (fun M ↦ T.mapIso (Iso.prod (Iso.refl M) eP.symm))
      (by
        intro M N f
        change T.map (CategoryTheory.Prod.mkHom f (𝟙 _)) ≫
          T.map (CategoryTheory.Prod.mkHom (𝟙 N) eP.inv) =
          T.map (CategoryTheory.Prod.mkHom (𝟙 M) eP.inv) ≫
            T.map (CategoryTheory.Prod.mkHom f (𝟙 _))
        rw [← T.map_comp, ← T.map_comp]
        congr 1
        ext <;> simp)
  let := Functor.CommShift.ofIso c ℤ
  have := Functor.CommShift.ofIso_compatibility c ℤ
  have := Functor.isTriangulated_of_iso c
  have := Functor.isEquivalence_of_iso c
  exact ⟨inferInstance, CondensedRing.limitProperties _ (fun _ ↦ inferInstance)⟩

/-- Both signed Tate twists are exact, preserve all products, and carry every
homotopy-limit triangle and its canonical comparison to a homotopy-limit triangle.
This expresses commutation with the total derived inverse limit, not just with limits
of degree-zero sheaves.

Source: blueprint clause 2, Stacks 099L
(blueprint: det-prop-diagonal-tower-limit).
Proof: the root limit is locally free of rank one over the completed ring by
lem-pur-twist-sheaf-locally-free; its dual has the dual trivializations. Tensor by
either line is locally the identity, so is exact on sheaves and preserves products.
The signed-line tensor is the functor of sk-def-sp-tate-twist. Derived tensor is
triangulated. Apply the tensor clause of det-formal-closed-support-ii-limits with
X=Z=S, identity immersions and empty complement. Products and fibers give the Roos
triangle of the tensor tower; the normalized comparison is an isomorphism. -/
theorem diagonalCompletedTwist_limits (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ X)]
    (d : ℤ) (hd : d = 1 ∨ d = -1) :
    (diagonalCompletedSheafTwist ℓ X d).Additive ∧
    PreservesFiniteLimits (diagonalCompletedSheafTwist ℓ X d) ∧
    PreservesFiniteColimits (diagonalCompletedSheafTwist ℓ X d) ∧
    (∃ (_ : (diagonalCompletedTwist ℓ X d).CommShift ℤ),
      CondensedRing.ClosedSupportLimitFunctorProperties (diagonalCompletedTwist ℓ X d)) := by
  classical
  let := diagonalResidueInvertible ℓ k p hpℓ X
  let R := Scheme.purTwistZlCompletion X ℓ
  let L := Scheme.purTwistZlModule X ℓ
  obtain ⟨I, U, f, hc, he⟩ :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X ℓ (ULift.{u} ℚ_[ℓ])).2.1.1
  have hU : (Scheme.ProEt.topology X).CoversTop U := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  have hL : ∀ V : X.ProEt, ∃ s : Sieve V, s ∈ Scheme.ProEt.topology X V ∧
      ∀ (W : X.ProEt) (f : W ⟶ V), s f →
        Nonempty (L.over W ≅ SheafOfModules.unit ((Scheme.purTwistRing X R).over W)) := by
    intro V
    refine ⟨Sieve.ofObjects U V, hU V, ?_⟩
    rintro W f ⟨i, ⟨g⟩⟩
    obtain ⟨e⟩ := he i
    exact ⟨((SheafOfModules.overFunctorMap (Scheme.purTwistRing X R) g).app L).symm ≪≫
      (SheafOfModules.overMap (Scheme.purTwistRing X R) g).mapIso e ≪≫
        SheafOfModules.overMapUnitIso (R := Scheme.purTwistRing X R) g⟩
  rcases hd with rfl | rfl
  · exact diagonalLineLimits ℓ X L hL
  · exact diagonalLineLimits ℓ X (SheafOfModules.LineEvaluation.dual.{u + 1, u, u + 1} R L)
      (SheafOfModules.LineEvaluation.evaluation_inverse_pair.{u + 1, u, u + 1} R L hL).1


/-- The generic direct-image assertion, sharing its categorical structures.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-limit). -/
def diagonalDirectImageAssertion
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] : Prop :=
    ∃ (LX : DiagonalRlim A) (LY : DiagonalRlim B)
      (Rf : DiagonalRightDerived (F))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        A B).obj
          (F)))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙
          F ≅
        (Functor.whiskeringRight ℕᵒᵖ A B).obj
          (F) ⋙ lim),
      (∀ H : (ℕᵒᵖ ⥤ A),
        c₀.hom.app H = limit.post H
          (F)) ∧
      (∀ P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ,
        Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            A B).obj
              (F)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex ((ℕᵒᵖ ⥤ A)) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ A).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj
            (F)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory ((ℕᵒᵖ ⥤ A))) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M)

section DirectImageProof

set_option backward.defeqAttrib.useBackward true

private theorem diagonalRightDerived_exists
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] : Nonempty (DiagonalRightDerived F) := by
  obtain ⟨R, η, hu, hc, s, ht⟩ := CategoryTheory.RingedStrictTowerProof.totalDerivedData F
  let := s
  exact ⟨⟨R, η, hu, hc, ht⟩⟩

private theorem diagonalRlim_exists
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] : Nonempty (DiagonalRlim A) := by
  obtain ⟨L⟩ := diagonalRightDerived_exists (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  have := L.universal
  let β (n : ℕ) :
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ))
        DerivedCategory.Q ≫ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.inv
  let π (n : ℕ) := L.R.rightDerivedDesc L.η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (β n)
  refine ⟨{ L with projection := π, normalization := ?_ }⟩
  intro P n
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp [β]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem diagonalIsoNormalization
    {C : Type a} [Category.{v} C] {U V W Z T : C}
    (a : U ≅ V) (b : Z ≅ T) (u : U ⟶ W) (e : W ⟶ Z) (f : V ⟶ T)
    (h : (a.inv ≫ u) ≫ e = f ≫ b.inv) : u ≫ e ≫ b.hom = a.hom ≫ f := by
  have h' := congrArg (fun z ↦ a.hom ≫ z ≫ b.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h'

private theorem diagonalEvaluationComparison
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ B) [F.Additive]
    (Rf : DiagonalRightDerived F)
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)) :
    ∃ e : ∀ n : ℕ, Rt.R ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R,
      ∀ (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
            (e n).hom.app (DerivedCategory.Q.obj P) ≫
            Rf.R.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P) =
          ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
            ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj P) ≫
            Rf.η.app
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let EA (n : ℕ) := (evaluation ℕᵒᵖ A).obj (op n)
  let EB (n : ℕ) := (evaluation ℕᵒᵖ B).obj (op n)
  let α (n : ℕ) :
      (FT ⋙ EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ (Rt.R ⋙ (EB n).mapDerivedCategory) :=
    Functor.whiskerLeft (FT.mapHomologicalComplex (.up ℤ))
        (EB n).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight Rt.η (EB n).mapDerivedCategory
  let β (n : ℕ) :
      (FT ⋙ EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ ((EA n).mapDerivedCategory ⋙ Rf.R) :=
    Functor.whiskerLeft ((EA n).mapHomologicalComplex (.up ℤ)) Rf.η ≫
      Functor.whiskerRight (EA n).mapDerivedCategoryFactors.inv Rf.R
  have hα (n : ℕ) : (Rt.R ⋙ (EB n).mapDerivedCategory).IsRightDerivedFunctor
      (α n) (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := by
    apply (CategoryTheory.derives (FT ⋙ EB n)).isRightDerivedFunctor_of_isIso
    intro I
    have := Rt.computation I.obj I.property
    change IsIso ((EB n).mapDerivedCategoryFactors.inv.app _ ≫
      (EB n).mapDerivedCategory.map (Rt.η.app I.obj))
    infer_instance
  have hβ (n : ℕ) : ((EA n).mapDerivedCategory ⋙ Rf.R).IsRightDerivedFunctor
      (β n) (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := by
    apply (CategoryTheory.derives (FT ⋙ EB n)).isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    have hi : CochainComplex.IsKInjective
        (((EA n).mapHomologicalComplex (.up ℤ)).obj I.obj) :=
      tower_evaluation_isKInjective A I.obj (op n)
    have := Rf.computation (((EA n).mapHomologicalComplex (.up ℤ)).obj I.obj) hi
    change IsIso (Rf.η.app (((EA n).mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      Rf.R.map ((EA n).mapDerivedCategoryFactors.inv.app I.obj))
    infer_instance
  let e (n : ℕ) := Functor.rightDerivedUnique _ _ (α n) (β n)
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  refine ⟨e, ?_⟩
  intro P n
  have he := Functor.rightDerivedNatTrans_app _ _ (α n) (β n)
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (𝟙 _) P
  change ((EB n).mapDerivedCategoryFactors.inv.app _ ≫
      (EB n).mapDerivedCategory.map (Rt.η.app P)) ≫
        (e n).hom.app (DerivedCategory.Q.obj P) = 𝟙 _ ≫
          (Rf.η.app
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            Rf.R.map ((EA n).mapDerivedCategoryFactors.inv.app P)) at he
  rw [Category.id_comp] at he
  exact diagonalIsoNormalization
    ((EB n).mapDerivedCategoryFactors.app
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj P))
    (Rf.R.mapIso ((EA n).mapDerivedCategoryFactors.app P))
    ((EB n).mapDerivedCategory.map (Rt.η.app P))
    ((e n).hom.app (DerivedCategory.Q.obj P))
    (Rf.η.app (((EA n).mapHomologicalComplex (.up ℤ)).obj P)) he

private theorem diagonalMapComposite
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{u} D]
    (F : C ⥤ D) {X Y Z : C} {T : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (r : F.obj Z ⟶ T)
    (k : F.obj X ⟶ T) (hfg : f ≫ g = h) (hk : F.map h ≫ r = k) :
    F.map f ≫ F.map g ≫ r = k := by
  calc
    F.map f ≫ F.map g ≫ r = F.map (f ≫ g) ≫ r := by
      rw [F.map_comp, Category.assoc]
    _ = F.map h ≫ r := by rw [hfg]
    _ = k := hk

private theorem diagonalProjectionDiagram
    {C : Type a} [Category.{v} C] {O A B D E G H I J K V : C}
    (a : O ⟶ A) (b : A ⟶ B) (c : B ⟶ D)
    (d : O ⟶ J) (t : J ⟶ E) (v : E ⟶ D)
    (p : D ⟶ G) (q : E ⟶ H) (r : H ⟶ G)
    (e : G ⟶ I) (s : I ⟶ K) (z : H ⟶ V) (n : V ⟶ K)
    (m : J ⟶ V) (x : A ⟶ K) (k : B ⟶ I)
    (hc : a ≫ b ≫ c = d ≫ t ≫ v) (hn : v ≫ p = q ≫ r)
    (he : r ≫ e ≫ s = z ≫ n) (hY : t ≫ q ≫ z = m)
    (hF : d ≫ m ≫ n = a ≫ x) (hX : b ≫ k ≫ s = x) :
    (a ≫ b) ≫ c ≫ p ≫ e ≫ s = (a ≫ b) ≫ k ≫ s := by
  calc
    (a ≫ b) ≫ c ≫ p ≫ e ≫ s = d ≫ t ≫ v ≫ p ≫ e ≫ s := by
      simpa only [Category.assoc] using congrArg (fun l ↦ l ≫ p ≫ e ≫ s) hc
    _ = d ≫ t ≫ q ≫ r ≫ e ≫ s := by
      simpa only [Category.assoc] using congrArg (fun l ↦ d ≫ t ≫ l ≫ e ≫ s) hn
    _ = d ≫ t ≫ q ≫ z ≫ n := congrArg (fun l ↦ d ≫ t ≫ q ≫ l) he
    _ = d ≫ m ≫ n := by
      simpa only [Category.assoc] using congrArg (fun l ↦ d ≫ l ≫ n) hY
    _ = a ≫ x := hF
    _ = (a ≫ b) ≫ k ≫ s := by rw [← hX, Category.assoc]

private theorem diagonalDirectImage_of_preservesKInjective
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape ℕᵒᵖ F]
    [((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes] :
    diagonalDirectImageAssertion F := by
  obtain ⟨LX⟩ := diagonalRlim_exists A
  obtain ⟨LY⟩ := diagonalRlim_exists B
  obtain ⟨Rf⟩ := diagonalRightDerived_exists F
  obtain ⟨Rt⟩ := diagonalRightDerived_exists ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)
  have := LX.universal
  have := LY.universal
  have := Rf.universal
  have := Rt.universal
  obtain ⟨e, he⟩ := diagonalEvaluationComparison F Rf Rt
  let c₀ := preservesLimitNatIso F (J := ℕᵒᵖ)
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let FTc := FT.mapHomologicalComplex (.up ℤ)
  obtain ⟨c, hc⟩ := towerComparison_existsLimitIso F Rf.R Rt.R LX.R LY.R
    Rf.η Rt.η LX.η LY.η Rf.computation Rt.computation LX.computation
    (fun P hP ↦ by
      have := hP
      exact LY.computation _ inferInstance) c₀
  refine ⟨LX, LY, Rf, Rt, e, c, c₀, fun _ ↦ rfl, hc,
    (fun P _ n ↦ he P n), ?_⟩
  intro M n
  have := towerComparison_limPreservesKInjective (A := A)
  obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A) F LX.R Rf.R LX.η Rf.η LX.computation
    (fun I hI ↦ by
      have := hI
      exact Rf.computation _ inferInstance)
  have := hα
  let γ₁ : LX.R ⋙ Rf.R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R :=
    c.hom ≫ Functor.whiskerLeft Rt.R (LY.projection n) ≫ (e n).hom
  let γ₂ : LX.R ⋙ Rf.R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ Rf.R :=
    Functor.whiskerRight (LX.projection n) Rf.R
  have hγ : γ₁ = γ₂ := by
    apply Functor.rightDerived_ext (LX.R ⋙ Rf.R) α
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    apply NatTrans.ext
    funext X
    let limπ := (NatTrans.mapHomologicalComplex
      (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶
        (evaluation ℕᵒᵖ A).obj (op n)) (.up ℤ)).app X
    let limπ' := (NatTrans.mapHomologicalComplex
      (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ B) ⥤ B) ⟶
        (evaluation ℕᵒᵖ B).obj (op n)) (.up ℤ)).app (FTc.obj X)
    let cX := (NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app X
    have hchain : cX ≫ limπ' = (F.mapHomologicalComplex (.up ℤ)).map limπ := by
      apply HomologicalComplex.hom_ext
      intro i
      exact preservesLimitIso_hom_π F (X.X i) (op n)
    have hF := diagonalMapComposite DerivedCategory.Q cX limπ'
      ((F.mapHomologicalComplex (.up ℤ)).map limπ)
      (Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj X))
      (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        Rf.R.map (DerivedCategory.Q.map limπ)) hchain (Rf.η.naturality limπ)
    have hX := congrArg Rf.R.map (LX.normalization X n)
    simp only [Functor.map_comp] at hX
    have hmain :
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          Rf.R.map (LX.η.app X)) ≫ γ₁.app (DerivedCategory.Q.obj X) =
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          Rf.R.map (LX.η.app X)) ≫ γ₂.app (DerivedCategory.Q.obj X) := by
      apply (cancel_mono (Rf.R.map
        (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X))).mp
      simpa only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.assoc] using diagonalProjectionDiagram
        (Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj X))
        (Rf.R.map (LX.η.app X)) (c.hom.app (DerivedCategory.Q.obj X))
        (DerivedCategory.Q.map cX) (LY.η.app (FTc.obj X)) (LY.R.map (Rt.η.app X))
        ((LY.projection n).app (Rt.R.obj (DerivedCategory.Q.obj X)))
        ((LY.projection n).app (DerivedCategory.Q.obj (FTc.obj X)))
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (Rt.η.app X))
        ((e n).hom.app (DerivedCategory.Q.obj X))
        (Rf.R.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app X))
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app (FTc.obj X))
        (Rf.η.app ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).obj X))
        (DerivedCategory.Q.map limπ') (Rf.R.map (DerivedCategory.Q.map limπ))
        (Rf.R.map ((LX.projection n).app (DerivedCategory.Q.obj X)))
        (hc X) ((LY.projection n).naturality (Rt.η.app X))
        (he X n) (LY.normalization (FTc.obj X) n) hF hX
    exact (congrArg (fun z ↦ z ≫ γ₁.app (DerivedCategory.Q.obj X)) (hαapp X)).trans
      (hmain.trans
        (congrArg (fun z ↦ z ≫ γ₂.app (DerivedCategory.Q.obj X)) (hαapp X)).symm)
  exact NatTrans.congr_app hγ M

end DirectImageProof

/-- Derived direct image on the constant-coefficient tower category is levelwise and
commutes with the total derived limit, for morphisms of the pro-etale sites
in the standing finite-type, separated field setting.
The final equation retains the canonical projections of the comparison.

Source: blueprint clause 1, Stacks 0A07 and 0940
(blueprint: det-prop-diagonal-tower-limit).
Proof: the direct image is restriction along base change and commutes with ordinary
limits. Resolve strict towers by K-injective towers; evaluation preserves K-injectives,
so the evaluated derived direct image is Rf_* of the evaluated level. The constant
tower functor is exact and left adjoint to limit. The two composites are therefore
the same derived direct image on the tower site, by
lem-weil-ringed-tower-pushforward-limit-comparison and
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Their common derived unit fixes the
comparison and naturality of the tower projections gives the displayed equation. -/
theorem diagonalTower_directImage (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    diagonalDirectImageAssertion
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f) := by
  have _hpℓ := hpℓ
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod ℓ X) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) X
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod ℓ Y) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) Y
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod ℓ X)
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ Y) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod ℓ Y)
  let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f
  let F := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f
  let LT := (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ Y) (DiagonalMod ℓ X)).obj L
  have : PreservesFiniteLimits LT :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesLimitsOfShape (C := ℕᵒᵖ) L⟩
  have : PreservesFiniteColimits LT :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesColimitsOfShape (C := ℕᵒᵖ) L⟩
  have : LT.PreservesHomology := {}
  have : ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X)
      (DiagonalMod ℓ Y)).obj F).PreservesKInjectiveComplexes :=
    ((upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f).whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes
  exact diagonalDirectImage_of_preservesKInjective F

/-- The completed diagonal class is the limit of the simultaneous reduction of the
positive Cartier boundary. Its endpoints are the supported completed constant and the
completed Tate line shifted by two. The unique lift is specified by its whole underlying
constant-coefficient morphism, not by a claim that individual reductions detect maps.
The reduction isomorphisms are normalized against the canonical limit projections and
the canonical derived quotient units.

Source: blueprint main-20261015, sk-prop-diagonal-tower-limit.md, clauses 1 and 3;
Stacks 099L, 099I and 099M (blueprint: det-prop-diagonal-tower-limit).

Proof:
1. Quotient transitions and the root power transitions are epimorphisms, the latter
by lem-pur-twist-sheaf-locally-free and invertibility of ell. det-pe-milnor-epimorphic
identifies derived and ordinary limits. The ordinary limits are the completed
coefficient sheaf and its Tate line, by det-prop-sfb-qlbar-colimit-x-integral-limit.
2. The diagonal is Cartier. Its complementary open is quasi-compact, since locally
it is the distinguished affine open D(t). lem-exc-proetale-closed-exact preserves
coefficient epimorphisms. Apply the same Milnor comparison to its direct-image
tower; direct image commutes with ordinary limits sectionwise. This gives the
supported completed constant. Clause 2 permits commuting the Tate line and shift.
3. det-prop-diagonal-tower-system identifies simultaneous reduction of the
integral source and G_m[1] with the supported finite constants and roots shifted
by two. Its completion formula identifies Rlim T(partial) with derived completion
of partial, with the intrinsic ell-completeness criterion.
4. lemma-weil-pbc-adic-completion-reduction identifies finite reduction of this
limit with evaluation at that level. The finite quotient has its two-term free
resolution. Naturality identifies the map, not merely the endpoints; its quotient
unit is adjoint to the tower projection. Thus the displayed finite arrow is the
torsion diagonal class with its positive Cartier/Kummer normalization.
5. lem-weil-pbc-constant-completion-equivalence identifies constant and completed
finite reductions and completion units. Both endpoints are derived complete.
Restriction from completed to constant coefficients is fully faithful on these
objects (sk-lem-integral-models, specialized to Q_l). Hence there is exactly one
completed-coefficient arrow inducing the whole constant-coefficient completion.
No assertion of uniqueness from separate finite reductions is used. -/
theorem diagonalTower_limit (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
  DiagonalCompletedLimitSpec ℓ Y hY D := by
  sorry

end AlgebraicGeometry.ProEtale
