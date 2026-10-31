/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceNormalization
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTransitions
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import all WeilConjectures.SmoothPurity.Adic.AdicPurityTwistReduction
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
import WeilConjectures.SmoothPurity.AllStageCtfPullback.AllStageCtfPullbackUnit
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceTransitionSquare
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTransitionCocycles
import all WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
import all WeilConjectures.SmoothPurity.Adic.AdicPurityObjects
import all WeilConjectures.SmoothPurity.Adic.AdicPuritySourceNormalization
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Uniform finiteness and canonical reductions of the adic purity source

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-adic-reconstruction.proof.md, common-bounds sentence and source-object argument.
(blueprint: lem-pur-adic-source-finiteness-reductions).

The helpers put the recorded direct quotient comparisons in the same coordinates.
Their data are quotient maps, adjunction transposes and the root-normalized finite
source comparison. In particular the finite normalization is defined independently
of the integral source reduction whose compatibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [hYsep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

universe a₁ a₂ a₃ v₁ v₂ v₃

private theorem purSource_transfer_unit
    {A : Type a₁} [Category.{v₁} A] (R : A ⥤ A) (u : R ≅ 𝟭 A)
    {M N : A} (e : M ⟶ N) [IsIso e] (t : M ⟶ R.obj M) (v : N ⟶ R.obj N)
    (hs : e ≫ v = t ≫ R.map e) (hu : t ≫ u.hom.app M = 𝟙 M) :
    v ≫ u.hom.app N = 𝟙 N := by
  apply (cancel_epi e).mp
  calc
    e ≫ (v ≫ u.hom.app N) = (t ≫ R.map e) ≫ u.hom.app N := by rw [← hs]; simp
    _ = (t ≫ u.hom.app M) ≫ e := by
      simpa only [Category.assoc, Functor.id_map] using
        congrArg (fun k ↦ t ≫ k) (u.hom.naturality e)
    _ = e ≫ 𝟙 N := by rw [hu]; simp

private theorem purSource_transfer_comp
    {A : Type a₁} [Category.{v₁} A] {B : Type a₂} [Category.{v₂} B]
    {T : Type a₃} [Category.{v₃} T]
    (R : B ⥤ A) (S : T ⥤ B) (Q : T ⥤ A) (c : S ⋙ R ≅ Q)
    {M₁ N₁ : A} {M₂ N₂ : B} {M₃ N₃ : T}
    (e₁ : M₁ ⟶ N₁) [IsIso e₁] (e₂ : M₂ ⟶ N₂) (e₃ : M₃ ⟶ N₃)
    (t₁ : M₁ ⟶ R.obj M₂) (t₂ : M₂ ⟶ S.obj M₃) (t₃ : M₁ ⟶ Q.obj M₃)
    (v₁ : N₁ ⟶ R.obj N₂) (v₂ : N₂ ⟶ S.obj N₃) (v₃ : N₁ ⟶ Q.obj N₃)
    (h₁ : e₁ ≫ v₁ = t₁ ≫ R.map e₂)
    (h₂ : e₂ ≫ v₂ = t₂ ≫ S.map e₃)
    (h₃ : e₁ ≫ v₃ = t₃ ≫ Q.map e₃)
    (ht : t₁ ≫ R.map t₂ ≫ c.hom.app M₃ = t₃) :
    v₁ ≫ R.map v₂ ≫ c.hom.app N₃ = v₃ := by
  apply (cancel_epi e₁).mp
  calc
    e₁ ≫ (v₁ ≫ R.map v₂ ≫ c.hom.app N₃) =
        t₁ ≫ R.map (e₂ ≫ v₂) ≫ c.hom.app N₃ := by
      rw [← Category.assoc e₁ v₁, h₁]
      simp only [Functor.map_comp, Category.assoc]
    _ = t₁ ≫ R.map t₂ ≫ R.map (S.map e₃) ≫ c.hom.app N₃ := by
      rw [h₂, Functor.map_comp]
      simp only [Category.assoc]
    _ = t₁ ≫ R.map t₂ ≫ c.hom.app M₃ ≫ Q.map e₃ := by
      rw [show R.map (S.map e₃) ≫ c.hom.app N₃ =
        c.hom.app M₃ ≫ Q.map e₃ from c.hom.naturality e₃]
    _ = e₁ ≫ v₃ := by
      simpa only [Category.assoc] using
        (congrArg (fun k ↦ k ≫ Q.map e₃) ht).trans h₃.symm

private theorem purSource_adj_square
    {A : Type a₁} [Category.{v₁} A] {B : Type a₂} [Category.{v₂} B]
    (F : A ⥤ B) (R S : B ⥤ A) (adj : F ⊣ R) (j : S ≅ R)
    {M M' : A} {N N' : B} (e : M ⟶ M') (e' : N ⟶ N')
    (t : M ⟶ S.obj N) (v : M' ⟶ S.obj N') (w : F.obj M' ⟶ N')
    (hw : adj.homEquiv _ _ w = v ≫ j.hom.app N')
    (hs : e ≫ v = t ≫ S.map e') :
    F.map e ≫ w = (adj.homEquiv _ _).symm (t ≫ j.hom.app N) ≫ e' := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, hw]
  calc
    e ≫ v ≫ j.hom.app N' = (t ≫ S.map e') ≫ j.hom.app N' := by
      rw [← hs, Category.assoc]
    _ = (t ≫ j.hom.app N) ≫ R.map e' := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ t ≫ k) (j.hom.naturality e')

private theorem purSource_tor_iso (W : Scheme.{u}) (A : Type u) [CommRing A]
    {M N : proEtaleDerivedCategory W A} (e : M ≅ N) (a b : ℤ)
    (h : HasProEtaleTorAmplitude W A M a b) :
    HasProEtaleTorAmplitude W A N a b := by
  refine ⟨h.1, ?_⟩
  rintro L P ⟨q⟩ g hg hP T i hi
  exact h.2 L P ⟨q ≪≫ e.symm⟩ g hg hP T i hi

private theorem purSource_support_shift (W : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleDerivedCategory W A) (a b t : ℤ)
    (h : proEtaleCohomologicalSupport M ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport (M⟦t⟧) ⊆ Set.Icc (a - t) (b - t) := by
  intro i hi
  have hi' : i + t ∈ proEtaleCohomologicalSupport M := by
    intro hz
    apply hi
    exact (((DerivedCategory.homologyFunctor _ 0).shiftIso t i (i + t)
      (add_comm t i)).app M).isZero_iff.mpr hz
  obtain ⟨ha, hb⟩ := h hi'
  exact ⟨by omega, by omega⟩

private theorem purSource_twist_iso (W : Scheme.{u})
    [∀ x : W, Invertible (C.l : W.residueField x)] (n : ℕ)
    (M : DerivedCategory (scalarReductionSource C.l E W)) :
    IsIso (adicPurityTwistReduction C.l E n W d M) := by
  let TI := (integralSheafTwist C.l E W (d : ℤ)).mapDerivedCategory
  let TF := (adicPurityFiniteSheafTwist C.l E n W d).mapDerivedCategory
  have tw (k : ℤ) := twist_preserves_finiteness C.l E W C.Qbar k
  obtain ⟨ei⟩ := (tw (d : ℤ)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ei'⟩ := (tw (-(d : ℤ))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have : TI.IsEquivalence := Functor.IsEquivalence.mk'
    (sfIntegralTwistingFunctor C.l E W (-(d : ℤ))) ei.symm (by
      simpa only [neg_neg] using ei')
  obtain ⟨ef⟩ := (tw (d : ℤ)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 n
  obtain ⟨ef'⟩ := (tw (-(d : ℤ))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 n
  have hTF : TF = finiteComplexTwist C.l E W n (d : ℤ) :=
    (adicPurityFiniteTwistPresentation C.l E n W d).symm
  have hfe : (finiteComplexTwist C.l E W n (d : ℤ)).IsEquivalence :=
    Functor.IsEquivalence.mk'
      (finiteComplexTwist C.l E W n (-(d : ℤ))) ef.symm (by
        simpa only [neg_neg] using ef')
  have : TF.IsEquivalence := by rw [hTF]; exact hfe
  let adj := (derivedScalarExtensionRestrictionAdjunction C.l E W n).choose
  let e := adicPurityDerivedTwistRestriction C.l E n W d
  let α := ((mateEquiv adj adj).symm e.hom).natTrans
  have : IsIso α := isIso_inverseMate_of_equivalences adj adj e
  have he : adicPurityTwistReduction C.l E n W d M ≫
      (eqToIso (adicPurityFiniteTwistPresentation C.l E n W d)).hom.app
        ((scalarReductionDerivedExtension C.l E W n).obj M) = α.app M := by
    apply (adj.homEquiv _ _).injective
    have hg : IsAdicPurityTwistReduction C.l E n W d M
        (adicPurityTwistReduction C.l E n W d M) :=
      (adicPurityTwistReduction_existsUnique C.l E n W d M).exists.choose_spec
    change adj.homEquiv _ _ (_ ≫ _) = _ at hg
    rw [hg, Adjunction.homEquiv_unit]
    exact unit_mateEquiv_symm adj adj e.hom M
  have : IsIso (adicPurityTwistReduction C.l E n W d M ≫
      (eqToIso (adicPurityFiniteTwistPresentation C.l E n W d)).hom.app
        ((scalarReductionDerivedExtension C.l E W n).obj M)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (adicPurityTwistReduction C.l E n W d M)
    ((eqToIso (adicPurityFiniteTwistPresentation C.l E n W d)).hom.app
      ((scalarReductionDerivedExtension C.l E W n).obj M))

include hXsep hYsep in
/-- Uniform finiteness, exact bounds and the canonical coherent source reductions.
Source: main-20261015 thm-pur-adic-reconstruction.proof.md, common-bounds sentence;
expanded source-object argument, Steps 1--8
(blueprint: lem-pur-adic-source-finiteness-reductions).

Proof: (1) Apply lem-sf-pullback-tor-amplitude at every finite quotient. Exact constant
inverse image and lem-weil-pbc-exact-functor-complex-cohomology preserve the supplied
cohomological interval separately from the Tor interval. (2) prop-weil-twist-preserves
preserves both intervals and constructibility; the cochain shift subtracts 2d from
both endpoints. (3) lem-pur-integral-operations-preserve-constructible supplies integral
pullback finiteness. The coefficient-system inverse image of lem-coef-semilinear-derived-
sections is relabelled by the canonical constant-ring isomorphisms of prop-weil-pbc-
proetale-constant-exact. It preserves normalization. lem-coef-normalized-dvr-effectivity
then gives the coherent pullback reduction counits; lem-pur-integral-operation-roos-
effectivity identifies these with the actual Roos projection adjuncts. (4) The completed
rank-one line of lem-pur-twist-sheaf-locally-free satisfies lem-pur-integral-line-reduction-
restriction. The K-flat equations of lem-pur-integral-line-derived-comparisons normalize
its reduction and strict transitions. Shift this comparison to obtain an invertible
reduction of U. (5) Transpose the twist factor under lem-weil-derived-scalar-extension-
restriction-adjunction. The two transposes agree on every local tensor by the prescribed
root quotient and scalar-unit equations of def-pur-adic-finite-tensor-realization and
def-pur-adic-root-comparisons. Thus the invertible composite is precisely b^U.
(6) Paste the pullback counit square with the line reduction square. On tensors both
paths send (x tensor u) tensor v to x tensor q(u)v by lem-sfb-successive-derived-quotient-
normalization. The root quotients commute with direct reduction and shifts act termwise.
This is the displayed direct-quotient square, including successive quotients.
(7) Equal indices give the action unitor. For three indices balancing gives the same
product of the two quotient scalars. Transposing gives the restriction identity and
composition equations below, so b^U intertwines their cocycles as well.
(8) lem-weil-integral-constructible-triangulated gives integral constructibility after
shifting. The reduction isomorphisms and the uniform shifted Tor interval give exactly
finiteTorConstructibleIntegral for the actual source. -/
theorem purAdicSource_finiteness_reductions
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    finiteTorConstructibleIntegral C.l E X (purAdicSource D C E f d K) ∧
    (∀ r s a b : ℤ,
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension C.l E Y n).obj K) ⊆ Set.Icc r s) →
      (∀ n : ℕ, Scheme.HasProEtaleTorAmplitude Y
        (Padic.coefficientExtensionRing C.l E (n + 1))
        ((scalarReductionDerivedExtension C.l E Y n).obj K) a b) →
      ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible C.l E (n + 1) (Nat.succ_pos n) X
          (purAdicFiniteSource D C E f d K n) ∧
        proEtaleCohomologicalSupport (purAdicFiniteSource D C E f d K n) ⊆
          Set.Icc (r - 2 * (d : ℤ)) (s - 2 * (d : ℤ)) ∧
        Scheme.HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing C.l E (n + 1))
          (purAdicFiniteSource D C E f d K n) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))) ∧
    (∀ n : ℕ, IsIso (purAdicSourceReduction D C E f d K hK n)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
        (Nat.add_le_add_right h 1) X).map (purAdicSourceReduction D C E f d K hK m) ≫
          purAdicFiniteSourceNormalization D C E f d K hK h =
        purAdicQuotientNormalization D C E X h (purAdicSource D C E f d K) ≫
          purAdicSourceReduction D C E f d K hK n) ∧
    (∀ n : ℕ,
      purAdicFiniteSourceTransition D C E f d K hK (Nat.le_refl n) ≫
        (normalizedDVRResUnit C.l E X n).hom.app _ = 𝟙 _) ∧
    (∀ {c b a : ℕ} (hab : a ≤ b) (hbc : b ≤ c),
      purAdicFiniteSourceTransition D C E f d K hK hbc ≫
        (normalizedDVRRes C.l E X hbc).map
          (purAdicFiniteSourceTransition D C E f d K hK hab) ≫
        (normalizedDVRResComp C.l E X hbc hab).hom.app _ =
      purAdicFiniteSourceTransition D C E f d K hK (hab.trans hbc)) := by
  let : ∀ x : X, Invertible (C.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit D C X x).invertible
  let : ∀ y : Y, Invertible (C.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit D C Y y).invertible
  let : LocallyOfFiniteType (X.asOver (Spec (.of D.k))).hom := ‹_›
  let : LocallyOfFiniteType (Y.asOver (Spec (.of D.k))).hom := ‹_›
  let : QuasiCompact (X.asOver (Spec (.of D.k))).hom := ‹_›
  let : QuasiCompact (Y.asOver (Spec (.of D.k))).hom := ‹_›
  let : IsSeparated (f.asOver (Spec (.of D.k))).left := ‹IsSeparated f›
  let : LocallyOfFiniteType (f.asOver (Spec (.of D.k))).left := ‹LocallyOfFiniteType f›
  let : QuasiCompact (f.asOver (Spec (.of D.k))).left := ‹QuasiCompact f›
  have hp := AllStageCtfPullback.preserves_ctf_and_unit (purAdicFiniteSetting D C E 0)
    (X.asOver (Spec (.of D.k))) (Y.asOver (Spec (.of D.k)))
    (f.asOver (Spec (.of D.k)))
  have ht := twist_preserves_finiteness C.l E X C.Qbar (d : ℤ)
  have hfinite : ∀ r s a b : ℤ,
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension C.l E Y n).obj K) ⊆ Set.Icc r s) →
      (∀ n : ℕ, HasProEtaleTorAmplitude Y
        (Padic.coefficientExtensionRing C.l E (n + 1))
        ((scalarReductionDerivedExtension C.l E Y n).obj K) a b) →
      ∀ n : ℕ,
        intrinsicFiniteTorsionConstructible C.l E (n + 1) (Nat.succ_pos n) X
          (purAdicFiniteSource D C E f d K n) ∧
        proEtaleCohomologicalSupport (purAdicFiniteSource D C E f d K n) ⊆
          Set.Icc (r - 2 * (d : ℤ)) (s - 2 * (d : ℤ)) ∧
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing C.l E (n + 1))
          (purAdicFiniteSource D C E f d K n) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ)) := by
    intro r s a b hs ha n
    let A := Padic.coefficientExtensionRing C.l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing _ _ _ (Nat.succ_pos n)
    let M := (scalarReductionDerivedExtension C.l E Y n).obj K
    let N := (finiteDerivedPullback C.l E n f).obj M
    let T := (finiteComplexTwist C.l E X n (d : ℤ)).obj N
    have hc := (purAdicReductionFiniteTor D C E Y K hK n).1
    obtain ⟨hcN, haN⟩ := hp.1 n M hc a b (ha n)
    have hsN : proEtaleCohomologicalSupport N ⊆ Set.Icc r s := by
      intro i hi
      apply hs n
      intro hz
      apply hi
      exact (((sfIntrinsicPullback A f).mapDerivedCategoryHomologyFunctorIso i).app M).isZero_iff.mp
        ((sfIntrinsicPullback A f).map_isZero hz)
    have hcT := ht.2.2.2.2.1 n N hcN
    have hsT := ht.2.2.2.2.2.2.1 n r s N hsN
    have haT := ht.2.2.2.2.2.2.2.1 n a b N haN
    let P := intrinsicFiniteTorsionConstructible C.l E (n + 1) (Nat.succ_pos n) X ⊓
      fun V ↦ HasFiniteProEtaleTorAmplitude X A V
    have : P.IsTriangulated := (finite_ctf_isTriangulated C.l E
      (n + 1) (Nat.succ_pos n) X).2.1
    have hcshift := P.le_shift (2 * (d : ℤ)) T ⟨hcT, a, b, haT⟩
    exact ⟨hcshift.1, purSource_support_shift X A T r s (2 * (d : ℤ)) hsT,
      (finite_ctf_isTriangulated C.l E (n + 1) (Nat.succ_pos n) X).2.2.1
        T a b (2 * (d : ℤ)) haT⟩
  have hsource : finiteTorConstructibleIntegral C.l E X (purAdicSource D C E f d K) := by
    have hM := hp.2.2.2 K hK
    have hT := ht.2.2.2.2.2.2.2.2.2.2.2.1 _ hM
    refine ⟨(sfIntegralConstructible C.l E X).le_shift (2 * (d : ℤ)) _ hT.1, ?_⟩
    obtain ⟨a, b, hab, ha⟩ := hT.2
    refine ⟨a - 2 * (d : ℤ), b - 2 * (d : ℤ), by omega, ?_⟩
    intro n
    let F := scalarReductionDerivedExtension C.l E X n
    let M := (integralComplexTwist D C.l C.different E X (d : ℤ)).obj
      ((integralDerivedPullback C.l E f).obj K)
    have hb := (finite_ctf_isTriangulated C.l E (n + 1) (Nat.succ_pos n) X).2.2.1
      (F.obj M) a b (2 * (d : ℤ)) (ha n)
    exact purSource_tor_iso X _ ((purAdicReductionShift C.l E X n
      (2 * (d : ℤ))).symm.app M) _ _ hb
  have hiso (n : ℕ) : IsIso (purAdicSourceReduction D C E f d K hK n) := by
    have hc := (pullbackTensorComparisonCounits C.l E f ⟨K, hK.1⟩ ⟨K, hK.1⟩).2.1
    have hpull : IsIso (purAdicPullbackReduction C.l E f K n) := by
      dsimp only [purAdicPullbackReduction]
      infer_instance
    have htwist := purSource_twist_iso D C E d X n
      ((integralDerivedPullback C.l E f).obj K)
    dsimp only [purAdicSourceReduction]
    infer_instance
  have hsquare {m n : ℕ} (h : n ≤ m) :=
    purAdicSourceReduction_transition_square D C E f d K hK h
  obtain ⟨hunit, hcomp⟩ := integralReductionTransition_cocycles D C.l C.different E X
    (purAdicSource D C E f d K)
  refine ⟨hsource, hfinite, hiso, ?_, ?_, ?_⟩
  · intro m n h
    let adj := (purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1)
      (Nat.succ_pos n) (Nat.add_le_add_right h 1) X
    let j := purAdicQuotientRestrictionIso D C E X h
    let v := purAdicFiniteSourceNormalization D C E f d K hK h
    have hv : adj.homEquiv _ _ v =
        purAdicFiniteSourceTransition D C E f d K hK h ≫ j.hom.app _ := by
      dsimp only [adj, v, j, purAdicFiniteSourceTransition]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
    exact purSource_adj_square _ _ _ adj j
      (purAdicSourceReduction D C E f d K hK m)
      (purAdicSourceReduction D C E f d K hK n)
      (normalizedDVRReductionTransition C.l E X D C.different h
        (purAdicSource D C E f d K))
      (purAdicFiniteSourceTransition D C E f d K hK h) v hv (hsquare h)
  · intro n
    have := hiso n
    exact purSource_transfer_unit (normalizedDVRRes C.l E X (Nat.le_refl n))
      (normalizedDVRResUnit C.l E X n) (purAdicSourceReduction D C E f d K hK n)
      _ _ (hsquare (Nat.le_refl n)) (hunit n)
  · intro c b a hab hbc
    have := hiso c
    exact purSource_transfer_comp (normalizedDVRRes C.l E X hbc)
      (normalizedDVRRes C.l E X hab) (normalizedDVRRes C.l E X (hab.trans hbc))
      (normalizedDVRResComp C.l E X hbc hab)
      (purAdicSourceReduction D C E f d K hK c)
      (purAdicSourceReduction D C E f d K hK b)
      (purAdicSourceReduction D C E f d K hK a)
      _ _ _ _ _ _ (hsquare hbc) (hsquare hab) (hsquare (hab.trans hbc))
      (hcomp hab hbc)

end WeilConjectures
