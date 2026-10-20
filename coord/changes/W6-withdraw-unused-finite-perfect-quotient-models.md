# Sheaf.Paper.FinitePerfectQuotientModels

## Reason

Withdraw the unused assigned module under dispatched worker brief step 8d.
After resuming the interrupted proof work, the current shared source tree has no
importer of this module and no occurrence of any of its public declarations outside
its own file. Its former consumers Sheaf.Paper.ResidueLissePerfectLift and
Sheaf.Paper.FinitePerfectAdicRealization are absent from the current library.
No consumer needs adaptation.

An independent source import-graph traversal finds 9537 modules in the
TargetsCheck closure and 2777 in the Challenge closure, including external imports;
neither closure contains this module. The graph has no missing Sheaf or
WeilConjectures import source. The item node does not realize any statement or
proof step in dag/units/sk-thm-properbasechange.json.

The mathematical statement and proof plan remain in
lem-weil-pbc-residue-perfect-finite-quotient-models. Only its Lean attachment becomes
null. The mathematical parent's DAG citation remains unchanged. No target statement,
definition used by a target, upstream declaration, or unit route is changed.

## Old

The complete withdrawn module, including its existing definitions and signatures:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module
public import Sheaf.Paper.CompletedAdicIntrinsicCompletion
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.Paper.NilpotentReductionLissity
import Sheaf.SixFunctors.ConnectedEtalePerfectConstant
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Uniform perfect models of finite quotients

Source: Stacks Tags 09C2 and 094I
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).

This interface records finite-level models without asserting a completed realization.
All coefficient identifications are normalized on constant sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- The locally bijective characterization at the actual coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the small pro-etale site is essentially small in universe t+1. -/
theorem finitePerfectModelsAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Standard algebraic derived localization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsAlgebraHasDerived (A : Type t) [CommRing A] :
    HasDerivedCategory (ModuleCat.{t} A) := HasDerivedCategory.standard _
/-- Standard derived localization for the actual coefficient sheaves.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsRingHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) := HasDerivedCategory.standard _
/-- Sheafification on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  hasSheafifyEssentiallySmallSite.{t, t + 1, t + 1, t + 2, t + 1} _ _
/-- Local bijectivity on the concrete localized site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, t + 1, t + 1,
    t + 2, t + 1, t + 1, t + 1} _
/-- Standard derived localization on each slice.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
instance finitePerfectModelsSliceHasDerived (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

/-- Apply the actual constant module functor termwise, with its universe lift.
Source: Stacks Tags 03CY and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def finiteModelConstantComplex (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :=
  ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
    koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).obj P

/-- A finite quotient admits perfect constant models in a specified interval on a chart.
Source: Stacks Tags 094I and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsOn (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (V : X.Etale)
    (a b : ℤ) : Prop :=
  ∃ T : Sieve V, T ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), T g →
      ∃ P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ,
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (n + 1)) (P.X i) ∧
          Module.Finite (A ⧸ d.ideal ^ (n + 1)) (P.X i)) ∧
        Nonempty
          (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
            ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
              ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
                (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))

/-- Etale local finite-projective quotient models with one interval on each chart.
The covering and the model at a finite level may depend on that level. This property
asserts no compatible choice of trivializations and no completed realization.
Source: Stacks Tags 09C2 and 094I
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def HasUniformFinitePerfectModels (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) : Prop :=
  ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
    ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
      ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
        FinitePerfectModelsOn X d φ M n V a b

/-- Normalization of the finite coefficient identifications on constant sections.
This fixes their compatibility with the quotient homomorphisms, rather than permitting
independent identifications at different levels.
Source: Stacks Tags 093M and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsNormalized (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  ∀ (n : ℕ) (U : X.ProEtᵒᵖ) (a : completedAdicQuotient d n),
    (φ n).hom.app U ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
      (AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap X
        (completedAdicQuotient d n)).app U a

/-- The finite comparisons preserve both quotient transitions and the scalar map.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
def FinitePerfectModelsCompatible (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) : Prop :=
  (∀ n : ℕ,
    adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) ≫
        φ n = φ (n + 1) ≫
      completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) ∧
  (∀ n : ℕ,
    completedAdicScalar X d ≫ completedAdicCommProjection X d n =
      adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫ φ n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized comparisons preserve the actual consecutive quotient maps.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: it suffices to test on constant presheaf sections. Naturality of the two
sheafification units reduces both composites to the same constant quotient function. -/
private theorem finitePerfectModelsComparison_step (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) (n : ℕ) :
    adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)) ≫
        φ n =
      φ (n + 1) ≫
        completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n) := by
  let J := ProEt.topology X
  let q := adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing X d n).property
  ext U a
  change (φ n).hom.app U
      ((adicConstantMap X q).hom.app U
        ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a)) =
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app U
      ((φ (n + 1)).hom.app U
        ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a))
  let qlift : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 2)) →+*
      ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) := RingHom.ulift q
  have hq := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      ((RingHom.ulift q) a) =
    (adicConstantMap X q).hom.app U
      ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1 + 1))).app U a) at hq
  rw [← hq, hnorm, hnorm]
  have hs := congrArg
    (fun k ↦ (k.app U).hom ((finiteCoefficientConstants X
      (completedAdicQuotient d (n + 1))).app U a))
    (toSheafify_naturality J (completedAdicFinitePresheafStep X d n))
  have hc : (completedAdicFinitePresheafStep X d n).app U
        ((finiteCoefficientConstants X (completedAdicQuotient d (n + 1))).app U a) =
      (finiteCoefficientConstants X (completedAdicQuotient d n)).app U (qlift a) := by
    apply ContinuousMap.ext
    intro c
    rfl
  simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
  rw [hc] at hs
  change (toSheafify J (finiteCoefficientPresheaf X
      (completedAdicQuotient d n))).app U
        ((finiteCoefficientConstants X (completedAdicQuotient d n)).app U (qlift a)) = _
  simpa only [completedAdicQuotientCommMap, completedAdicRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ, completedAdicFiniteStep,
    finiteCoefficientScalarMap, NatTrans.comp_app, RingCat.comp_apply,
    CommRingCat.hom_ofHom, RingCat.Hom.hom, sheafifyMap, J] using! hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed scalar map is normalized by the finite quotient comparisons.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: test the equality after the constant presheaf unit. The scalar map's defining
projection equation gives the left side, and naturality of the sheafification unit
followed by normalization of the finite comparison gives the right side. -/
private theorem finitePerfectModelsScalar_projection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) (n : ℕ) :
    completedAdicScalar X d ≫ completedAdicCommProjection X d n =
      adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫
        φ n := by
  let J := ProEt.topology X
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing X d n).property
  ext U a
  have hs := (completedAdicScalar_exists X d).exists.choose_spec n U a
  let qlift : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have hq := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom qlift)))
  change (koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U
      (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) =
    (adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
      ((koszulConstantUnit X A).app U a) at hq
  change (completedAdicProjection X d n).hom.app U
      (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicScalar X d)).hom.app U ((koszulConstantUnit X A).app U a)) =
    (φ n).hom.app U
      ((adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app U
        ((koszulConstantUnit X A).app U a))
  rw [← hq, hnorm]
  exact hs

/-- Normalization on constant sections determines a compatible coefficient system.
Source: Stacks Tags 093M and 09C6
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: precompose each required square with the constant-presheaf sheafification unit.
Naturality identifies the consecutive quotient maps. The defining projection equation
for the completed scalar map identifies the scalar squares. Sheafification's universal
property reflects both equalities back to maps of sheaves. -/
theorem finitePerfectModels_normalized_compatible (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hnorm : FinitePerfectModelsNormalized X d φ) :
    FinitePerfectModelsCompatible X d φ :=
  ⟨finitePerfectModelsComparison_step X d φ hnorm,
    finitePerfectModelsScalar_projection X d φ hnorm⟩

/-- Further restriction is exact and preserves the representative-based derived
restriction isomorphisms. Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: the underlying sheaf functor is pullback to the localized site. It preserves
finite limits and colimits, and the faithful exact forgetful functor reflects short
exactness. Derived composition and the representative localization factors then
identify further restriction with restriction to the smaller chart. -/
private theorem finitePerfectModelsOverMap_exact (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V) :
    (SheafOfModules.overMap.{t + 1} R f).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overMap.{t + 1} R f) ∧
      PreservesFiniteColimits (SheafOfModules.overMap.{t + 1} R f) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let H := (ProEt.topology X).overMapPullback AddCommGrpCat.{t + 1} f
  have hAdd : F.Additive := ⟨fun {_ _} a b ↦ by ext V x; rfl⟩
  let e : F ⋙ SheafOfModules.toSheaf.{t + 1} (R.over U) ≅
      SheafOfModules.toSheaf.{t + 1} (R.over V) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      ((ProEt.topology X).over U) ((ProEt.topology X).over V)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits H :=
    PreservesColimitsOfSize.preservesFiniteColimits H
  have h (S : ShortComplex (SheafOfModules.{t + 1} (R.over V))) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{t + 1} (R.over U))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf.{t + 1} (R.over V))).map_of_exact H)
  exact ⟨hAdd, (Functor.exact_tfae F).out 0 3 |>.mp h⟩

/-- The exact derived restriction agrees with the chosen representative formula.
Source: Stacks Tags 03DJ and 05RU
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private def finitePerfectModelsRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-- A local isomorphism persists on every smaller chart.
Source: Stacks Tag 03DJ
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models). -/
private theorem finitePerfectModelsRestrictIso_further (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) {U V : X.ProEt} (f : U ⟶ V)
    (M N : DerivedCategory (SheafOfModules.{t + 1} R))
    (e : ringedSiteDerivedRestrictionOfUniverses R V M ≅
      ringedSiteDerivedRestrictionOfUniverses R V N) :
    Nonempty (ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N) := by
  let F := SheafOfModules.overMap.{t + 1} R f
  let FV := SheafOfModules.overFunctor.{t + 1} R V
  let FU := SheafOfModules.overFunctor.{t + 1} R U
  have := (finitePerfectModelsOverMap_exact X R f).1
  have := (finitePerfectModelsOverMap_exact X R f).2.1
  have := (finitePerfectModelsOverMap_exact X R f).2.2
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  have := (ringedOverFunctor_exactGeneral R V).1
  have := (ringedOverFunctor_exactGeneral R V).2.1
  have := (ringedOverFunctor_exactGeneral R V).2.2
  have c (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
      F.mapDerivedCategory.obj (ringedSiteDerivedRestrictionOfUniverses R V K) ≅
        ringedSiteDerivedRestrictionOfUniverses R U K :=
    F.mapDerivedCategory.mapIso (finitePerfectModelsRestrictionComparison X R V K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso FV F).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R f)).app K ≪≫
      finitePerfectModelsRestrictionComparison X R U K
  exact ⟨(c M).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫ c N⟩
/-- One step of the perfect-residue coefficient filtration preserves local models
and their fixed Tor interval. No completeness or simultaneous trivialization is assumed.

Source: Stacks Project, sites-cohomology.tex, Tag 094I; proetale.tex, Tag 09C2;
connected etale perfect constancy.
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).

Proof: refine the two etale covers giving the residue and previous-level models to
one cover. Tensor the constant quotient sequence with a flat K-flat representative
of M. Its kernel term is the residue model tensored with I^(n+1)/I^(n+2), by
balancing. This is a bounded constant complex with finite cohomology. The previous
model supplies the other outer term. The weak Serre theorem over the Noetherian
finite coefficient ring gives locally constant finite cohomology of the middle
term, with the same bounds. Finite-ring constructible derived origin descends it to
the etale site. Full faithfulness transports its residue marking. Nilpotent-reduction
lissity makes its etale cohomology finite locally constant. For the Tor bound, tensor
with an arbitrary module and use its finite ideal filtration: each quotient is an
A/I-module, so balancing with the residue model gives vanishing outside [a,b].
Connected etale perfect constancy now provides local perfect constant values.
Represent them by finite-projective complexes in [a,b], using this Tor bound.
The coefficient squares identify each tensor and reduction with the specified
quotient functors. Compose the local coverings. Empty charts use empty covers. -/
theorem residuePerfect_quotient_models_succ
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (_hab : a ≤ b)
    (_hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (_hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    FinitePerfectModelsOn X d φ M (n + 1) V a b := by
  sorry

/-- A perfect constant residue model gives uniformly bounded perfect constant models
at all finite levels, on etale refinements. Completeness of M is not assumed.

Source: Stacks Tags 094I and 09C2
(blueprint: lem-weil-pbc-residue-perfect-finite-quotient-models).
Proof: keep the given residue covering. Enlarge a possibly empty interval to
[min a b,b]. Further exact slice restriction gives the same residue model on every
smaller chart. This proves the zero-level case. Induct on the quotient level with
the one-step coefficient-filtration theorem, preserving this fixed interval. -/
theorem residuePerfect_finite_quotient_models
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hresidue : ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
      ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i) ∧
            Module.Finite (A ⧸ d.ideal ^ (0 + 1)) (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V) ((completedAdicQuotientReduction X d 0).obj M) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V) ((completedAdicDerivedChange X (φ 0)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    HasUniformFinitePerfectModels X d φ M := by
  obtain ⟨S, hS, hlocal⟩ := hresidue
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hlocal V f hf
  have : P.IsStrictlyGE a := ha
  have hzero : FinitePerfectModelsOn X d φ M 0 V (min a b) b := by
    refine ⟨⊤, X.smallEtaleTopology.top_mem V, ?_⟩
    intro W g _
    refine ⟨P, P.isStrictlyGE_of_ge (min a b) a (min_le_left _ _), hb, hP, ?_⟩
    exact finitePerfectModelsRestrictIso_further X (completedAdicFiniteRing X d 0)
      ((toProEt X).map g) _ _ e
  refine ⟨min a b, b, min_le_right _ _, ?_⟩
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact residuePerfect_quotient_models_succ X d φ hφ hcompat M V
      (min a b) b (min_le_right _ _) hzero n ih

end AlgebraicGeometry.Scheme
```

## New

The delivery tool replaces the withdrawn file with an empty module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

There is no replacement theorem or definition. The node's lean field is null;
its statement, proof, dependencies, source and unit remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none | none | No direct or transitive importer and no external declaration use. |

The source check covers lean/Sheaf, lean/WeilConjectures, TargetsCheck and Challenge.
No other Lean file is changed. The two private covering lemmas developed and
compiled during this session are discarded with the unused module.

## Status

landed 20261020T135438-L-1824396 2026-10-20 (merge of deliver/W6/Sheaf.Paper.FinitePerfectQuotientModels)
