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

end AlgebraicGeometry.Scheme
