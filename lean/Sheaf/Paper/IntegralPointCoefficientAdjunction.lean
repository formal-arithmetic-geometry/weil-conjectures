/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q91, Q18, T3
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exact extension and normalized sections for integral point coefficients

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; point comparison,
third paragraph (blueprint: lem-pod-integral-point-coefficient-adjunction).

The coefficient and site universes are independent. All sheaves, scalar maps,
local tensor generators and adjunction formulas reuse PointDerivedHomModels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.PointDerivedHom
open scoped ChangeOfRings TensorProduct

namespace WeilConjectures.IntegralPointCoefficientAdjunction

variable (k : Type t) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing valuation ring, lifted only into the containing coefficient universe.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev R := coefficientRing.{t, u} l E 1 true

/-- The existing completed integral coefficient sheaf on the unchanged small site.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev B := coefficientSheaf.{t, u} k l E 1 true

/-- The limit lift of the actual constant residue maps, with commutativity retained.
Source: blueprint point coefficients
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev alpha := coefficientMap.{t, u} k l E 1 true

/-- Constant values in the finite quotient sheaf; n denotes the positive exponent n+1.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-pod-integral-point-coefficient-adjunction). -/
abbrev finiteValue (n : ℕ) :=
  scalar.{t, u} k (coefficientSheaf.{t, u} k l E (n + 1) false)
    (coefficientMap.{t, u} k l E (n + 1) false) (op (finalObject k))

private theorem constants_bijective [IsAlgClosed k]
    (A : CommRingCat.{max u (t + 1)}) :
    Function.Bijective ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj A)).app
        (op (finalObject k))) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let P := ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj A)
  let η := toSheafify J P
  refine ⟨?_, ?_⟩
  · intro x y h
    simpa using Scheme.ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _)
      (Presheaf.equalizerSieve_mem J η x y h)
  · intro x
    obtain ⟨y, hy⟩ := Scheme.ProEt.id_mem_of_mem_topology_of_iso (Iso.refl _)
      (Presheaf.imageSieve_mem J η x)
    refine ⟨y, ?_⟩
    change η.app (op (finalObject k)) y = x
    exact hy.trans (ConcreteCategory.congr_hom ((sheafify J P).map_id _) x)

private theorem finite_transition (n : ℕ)
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (a : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) :
    (integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app U
        (scalar.{t, u} k (coefficientSheaf.{t, u} k l E (n + 2) false)
          (coefficientMap.{t, u} k l E (n + 2) false) U a) =
      scalar.{t, u} k (coefficientSheaf.{t, u} k l E (n + 1) false)
        (coefficientMap.{t, u} k l E (n + 1) false) U
          (ULift.up (Padic.coefficientExtensionTransition l E (n + 1) a.down)) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let f : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift
  exact (congrArg (fun h ↦ (h.app U).hom a)
    (toSheafify_naturality J ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).map f))).symm

private theorem scalar_projection (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)
    (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) (r : R l E) :
    (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app U
        (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) U r) =
      scalar.{t, u} D.k (coefficientSheaf.{t, u} D.k l E (n + 1) false)
        (coefficientMap.{t, u} D.k l E (n + 1) false) U
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) r.down)) := by
  let J := Scheme.ProEt.topology (Spec (.of D.k))
  let η := (toSheafify J ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj
    (coefficientRing.{t, u} l E 1 true))).app U
  have h := congrArg (fun f ↦ (f.hom.app U).hom (η r))
    (limit.lift_π (integralConstantConeOfUniverses l E (Spec (.of D.k))) (op n))
  change (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app U
      (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) U r) =
    (integralConstantQuotientOfUniverses l E (Spec (.of D.k)) n).hom.app U (η r) at h
  rw [h]
  let f : coefficientRing.{t, u} l E 1 true ⟶ coefficientRing.{t, u} l E (n + 1) false :=
    CommRingCat.ofHom (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E (n + 1))).ulift
  exact (congrArg (fun h ↦ (h.app U).hom r)
    (toSheafify_naturality J ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).map f))).symm

private theorem completed_bijective (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)
    [IsAlgClosed D.k] :
    Function.Bijective (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E)
      (op (finalObject D.k))) := by
  classical
  obtain ⟨e, he, _⟩ := (Padic.coefficientExtension_integers_profinite_tower.{u, 0} l E).1
  let U := op (finalObject D.k)
  let S := integralCoefficientSheafSystem l E (Spec (.of D.k))
  let ev := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of D.k)))
      RingCat.{max u (t + 1)} ⋙
    (evaluation (Spec (.of D.k)).ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U
  let p (n : ℕ) :=
    (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app U
  have hp (x y : (B D.k l E).obj.obj U) (h : ∀ n, p n x = p n y) : x = y := by
    apply Concrete.isLimit_ext (S ⋙ ev) (isLimitOfPreserves ev (limit.isLimit S)) x y
    intro j
    exact h j.unop
  have hv (n : ℕ) : Function.Bijective (finiteValue D.k l E n) :=
    constants_bijective D.k (coefficientRing.{t, u} l E (n + 1) false)
  refine ⟨?_, ?_⟩
  · intro x y h
    apply ULift.ext
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    apply ULift.up_injective
    apply (hv n).1
    have hh := congrArg (p n) h
    change (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app U
      (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) U x) =
        (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app U
          (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) U y) at hh
    rw [scalar_projection, scalar_projection] at hh
    exact hh
  · intro b
    let z (n : ℕ) := ((Equiv.ofBijective _ (hv n)).symm (p n b)).down
    have hz (n : ℕ) : finiteValue D.k l E n (ULift.up (z n)) = p n b :=
      (Equiv.ofBijective _ (hv n)).apply_symm_apply _
    have hzcompat (n : ℕ) : Padic.coefficientExtensionTransition l E (n + 1)
        (z (n + 1)) = z n := by
      apply ULift.up_injective
      apply (hv n).1
      rw [← finite_transition D.k l E n U]
      change (integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app U
        (finiteValue D.k l E (n + 1) (ULift.up (z (n + 1)))) = _
      rw [hz, hz]
      have hw := congrArg (fun f ↦ (f.hom.app U) b)
        (limit.w S (homOfLE (Nat.le_succ n)).op)
      dsimp only [S, integralCoefficientSheafSystem] at hw
      rw [Functor.ofOpSequence_map_homOfLE_succ] at hw
      exact hw
    let z' : Padic.coefficientExtensionPositiveLimit l E :=
      ⟨z, by
        change z ∈ ⨅ n, RingHom.eqLocus _ _
        simp only [Subring.mem_iInf, RingHom.mem_eqLocus]
        exact hzcompat⟩
    refine ⟨ULift.up (e.symm z'), ?_⟩
    apply hp
    intro n
    rw [scalar_projection]
    change finiteValue D.k l E n (ULift.up
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (e.symm z'))) = _
    rw [← he, e.apply_symm_apply]
    exact hz n


private def continuousRingPresheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj V := CommRingCat.of C(V.unop.left, A)
  map h := CommRingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def constantToContinuous (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ continuousRingPresheaf X A where
  app V := CommRingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem continuousRingPresheaf_isSheaf (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousRingPresheaf X A) := by
  let : HasLimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    CommRingCat.hasLimitsOfSize.{t + 1, max u (t + 1), t}
  let : PreservesLimitsOfSize.{t, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    CommRingCat.forget_preservesLimitsOfSize.{t + 1, max u (t + 1), t}
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (continuousRingPresheaf X A) (forget CommRingCat.{max u (t + 1)})]
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem constantToContinuous_locallyInjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem constantToContinuous_locallySurjective
    (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm

private def continuousIso (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [HasSheafify (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective CommRingCat.{max u (t + 1)}] :
    sheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≅ continuousRingPresheaf X A := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)
  let F := continuousRingPresheaf X A
  let φ := constantToContinuous X A
  have hF := continuousRingPresheaf_isSheaf X A
  have : Presheaf.IsLocallyInjective J φ := constantToContinuous_locallyInjective X A
  have : Presheaf.IsLocallySurjective J φ := constantToContinuous_locallySurjective X A
  have : IsIso ((presheafToSheaf J CommRingCat.{max u (t + 1)}).map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  have : IsIso (sheafifyMap J φ) := inferInstance
  exact asIso (sheafifyMap J φ) ≪≫ (isoSheafify J hF).symm

private theorem continuousIso_unit (X : Scheme.{t}) (A : Type (max u (t + 1)))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [HasSheafify (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective CommRingCat.{max u (t + 1)}] :
    toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
        (continuousIso X A).hom = constantToContinuous X A := by
  dsimp [continuousIso]
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [toSheafify_naturality, isoSheafify_inv, Category.assoc,
    sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
  exact Category.comp_id _

private def continuousMapHom (X : Scheme.{t})
    {A A' : Type (max u (t + 1))} [CommRing A] [CommRing A']
    [TopologicalSpace A] [TopologicalSpace A'] [DiscreteTopology A] [DiscreteTopology A']
    (f : A →+* A') : continuousRingPresheaf X A ⟶ continuousRingPresheaf X A' where
  app V := CommRingCat.ofHom
    { toFun g := ⟨f ∘ g, (continuous_of_discreteTopology (f := f)).comp g.continuous⟩
      map_one' := by ext; exact map_one f
      map_mul' := by intro g h; ext; exact map_mul f _ _
      map_zero' := by ext; exact map_zero f
      map_add' := by intro g h; ext; exact map_add f _ _ }
  naturality _ _ _ := by ext; rfl

private theorem continuousIso_natural
    {A A' : Type (max u (t + 1))} [CommRing A] [CommRing A']
    [TopologicalSpace A] [TopologicalSpace A'] [DiscreteTopology A] [DiscreteTopology A']
    (f : A →+* A') :
    sheafifyMap (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Spec (.of k)).ProEtᵒᵖ).map (CommRingCat.ofHom f)) ≫
      (continuousIso (Spec (.of k)) A').hom =
        (continuousIso (Spec (.of k)) A).hom ≫ continuousMapHom (Spec (.of k)) f := by
  let : HasWeakSheafify (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} (Spec (.of k))).isRightAdjoint
  apply sheafify_hom_ext (D := CommRingCat.{max u (t + 1)})
    (Scheme.ProEt.topology (Spec (.of k))) _ _ (continuousRingPresheaf_isSheaf _ _)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    continuousIso_unit, ← Category.assoc, continuousIso_unit]
  ext V g
  rfl

private theorem completed_sections_torsionfree (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)
    (U : (Spec (.of D.k)).ProEtᵒᵖ) (a : R l E) (ha : a ≠ 0)
    (b : (B D.k l E).obj.obj U)
    (hab : scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) U a * b = 0) : b = 0 := by
  classical
  let A (n : ℕ) := ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let (n : ℕ) : TopologicalSpace (A n) := ⊥
  let (n : ℕ) : DiscreteTopology (A n) := ⟨rfl⟩
  let X := Spec (.of D.k)
  let S := integralCoefficientSheafSystem l E X
  let p (n : ℕ) := (completedIntegralCoefficientProjection l E X D hl n).hom.app U
  let θ (n : ℕ) :
      (coefficientSheaf.{t, u} D.k l E (n + 1) false).obj.obj U ≃+*
        C(U.unop.left, A n) :=
    ((continuousIso X (A n)).app U).commRingCatIsoToRingEquiv
  have htransition (n : ℕ) :
      θ n ((integralCoefficientSheafTransition l E X n).hom.app U (p (n + 1) b)) =
        (continuousMapHom X (Padic.coefficientExtensionTransition l E (n + 1)).ulift).app U
          (θ (n + 1) (p (n + 1) b)) := by
    exact congrArg (fun f ↦ (f.app U) (p (n + 1) b))
      (continuousIso_natural D.k (Padic.coefficientExtensionTransition l E (n + 1)).ulift)
  have hcompat (n : ℕ) :
      (integralCoefficientSheafTransition l E X n).hom.app U (p (n + 1) b) = p n b := by
    have hw := congrArg (fun f ↦ (f.hom.app U) b)
      (limit.w S (homOfLE (Nat.le_succ n)).op)
    dsimp only [S, integralCoefficientSheafSystem] at hw
    rw [Functor.ofOpSequence_map_homOfLE_succ] at hw
    exact hw
  obtain ⟨e, he, _⟩ := (Padic.coefficientExtension_integers_profinite_tower.{u, 0} l E).1
  have hzero (x : U.unop.left) : ∀ n, θ n (p n b) x = 0 := by
    let z : Padic.coefficientExtensionPositiveLimit l E :=
      ⟨fun n ↦ (θ n (p n b) x).down, by
        change _ ∈ ⨅ n, RingHom.eqLocus _ _
        simp only [Subring.mem_iInf, RingHom.mem_eqLocus]
        intro n
        have ht := congrArg (fun g ↦ (g x).down) (htransition n)
        rw [hcompat] at ht
        exact ht.symm⟩
    have haz : a.down * e.symm z = 0 := by
      apply e.injective
      apply Subtype.ext
      funext n
      rw [map_mul, e.apply_symm_apply, map_zero]
      change (e a.down).val n * (θ n (p n b) x).down = 0
      rw [he]
      have hh := congrArg (fun y ↦ (θ n (p n y) x).down) hab
      rw [map_mul, map_zero, map_mul, map_zero] at hh
      have hp := scalar_projection l E D hl n U a
      have hc := congrArg (fun f ↦ (f.app U) (ULift.up
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down)))
        (continuousIso_unit X (A n))
      change θ n (scalar.{t, u} D.k
        (coefficientSheaf.{t, u} D.k l E (n + 1) false)
          (coefficientMap.{t, u} D.k l E (n + 1) false) U
            (ULift.up (Ideal.Quotient.mk
              (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))) = _ at hc
      rw [hp, hc] at hh
      exact hh
    have ha' : a.down ≠ 0 := fun h ↦ ha (ULift.ext _ _ h)
    have hz : z = 0 := by
      have h := (mul_eq_zero.mp haz).resolve_left ha'
      simpa using congrArg e h
    intro n
    apply ULift.ext
    exact congrArg (fun z : Padic.coefficientExtensionPositiveLimit l E ↦ z.val n) hz
  let ev := sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)} ⋙
    (evaluation X.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U
  apply Concrete.isLimit_ext (S ⋙ ev) (isLimitOfPreserves ev (limit.isLimit S)) b 0
  intro j
  change p j.unop b = p j.unop 0
  rw [map_zero]
  apply (θ j.unop).injective
  rw [map_zero]
  apply ContinuousMap.ext
  intro x
  exact hzero x j.unop

private theorem finite_scalar_lift
    (A : CommRingCat.{max u (t + 1)}) (U : (Spec (.of k)).ProEt) (n : ℕ)
    (a : Fin n → (constantRing.{t, u} k A).obj.obj (op U)) :
    ∃ S : Sieve U, S ∈ Scheme.ProEt.topology (Spec (.of k)) U ∧
      ∀ (V : (Spec (.of k)).ProEt) (f : V ⟶ U), S f →
        ∀ i, ∃ c : A,
          ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
            ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)).app (op V)) c =
              (constantRing.{t, u} k A).obj.map f.op (a i) := by
  induction n with
  | zero => exact ⟨⊤, (Scheme.ProEt.topology _).top_mem U, fun _ _ _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
    let η := toSheafify (Scheme.ProEt.topology (Spec (.of k)))
      ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)
    let Z := Presheaf.imageSieve η (a 0)
    refine ⟨Z ⊓ S, (Scheme.ProEt.topology _).intersection_covering
      (Presheaf.imageSieve_mem _ _ _) hS, ?_⟩
    intro V f hf
    refine Fin.cases ?_ (fun i ↦ hs V f hf.2 i)
    exact hf.1

-- Keep the relation argument abstract so elaboration does not unfold the completed limit.
private theorem flat_of_flat_sections
    (A : CommRingCat.{max u (t + 1)})
    (T : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k A ⟶ T)
    (hflat : ∀ V : (Spec (.of k)).ProEt,
      letI := (scalar.{t, u} k T α (op V)).toAlgebra
      Module.Flat A (T.obj.obj (op V))) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      ((SheafOfModules.restrictScalars.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat RingCat)).map α)).obj
            (SheafOfModules.unit (ring.{t, u} k T))) := by
  classical
  let C := constantRing.{t, u} k A
  let N := (SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat RingCat)).map α)).obj
        (SheafOfModules.unit (ring.{t, u} k T))
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{t + 1, t,
    max u (t + 1), max u (t + 1)} C N
  intro U n a y hy
  obtain ⟨S, hS, hs⟩ := finite_scalar_lift k A U n a
  refine ⟨S, hS, ?_⟩
  intro V f hf
  choose c hc using hs V f hf
  let φ := scalar.{t, u} k T α (op V)
  let Q := T.obj.obj (op V)
  let : Algebra A Q := φ.toAlgebra
  have : Module.Flat A Q := hflat V
  let z : Fin n → Q := fun i ↦ N.val.map f.op (y i)
  have hz : ∑ i, c i • z i = 0 := by
    have h := congrArg (N.val.map f.op) hy
    simp only [map_sum, map_zero, N.val.map_smul] at h
    change (∑ i, α.hom.app (op V) (C.obj.map f.op (a i)) * z i) = 0 at h
    have hh (i : Fin n) : φ (c i) =
        α.hom.app (op V) (C.obj.map f.op (a i)) :=
      congrArg (α.hom.app (op V)) (hc i)
    change (∑ i, φ (c i) * z i) = 0
    simp_rw [hh]
    exact h
  obtain ⟨m, d, z', hd, hz'⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := Q) hz
  let η := toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)
  let ηV : A →+* C.obj.obj (op V) := (η.app (op V)).hom
  have hc' (i : Fin n) : ηV (c i) = C.obj.map f.op (a i) := hc i
  refine ⟨m, (fun i j ↦ ηV (d i j)), z', ?_, ?_⟩
  · intro i
    exact hd i
  · intro j
    simp_rw [← hc']
    simpa only [map_sum, map_mul, map_zero] using congrArg ηV (hz' j)

private theorem completed_flat (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)
    [IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E)] :
    SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      ((SheafOfModules.restrictScalars.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of D.k)))
          (forget₂ CommRingCat RingCat)).map (alpha.{t, u} D.k l E))).obj
            (SheafOfModules.unit (ring.{t, u} D.k (B.{t, u} D.k l E)))) := by
  let A := R.{t, u} l E
  have : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv.symm : Padic.coefficientExtensionIntegers l E ≃+* A).toRingHom
      ULift.ringEquiv.symm.surjective
  have : IsDomain A := MulEquiv.isDomain (Padic.coefficientExtensionIntegers l E)
    (ULift.ringEquiv : A ≃+* Padic.coefficientExtensionIntegers l E).toMulEquiv
  apply flat_of_flat_sections D.k A (B.{t, u} D.k l E) (alpha.{t, u} D.k l E)
  intro V
  let φ := scalar.{t, u} D.k (B.{t, u} D.k l E) (alpha.{t, u} D.k l E) (op V)
  let Q := (B.{t, u} D.k l E).obj.obj (op V)
  let : Algebra A Q := φ.toAlgebra
  have : Module.IsTorsionFree A Q := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r x hx
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr (completed_sections_torsionfree l E D hl (op V) r hr x hx)
  exact inferInstance

namespace Ordinary

attribute [local instance 3000] abSheafify abLocallyBijective

variable (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)

private def constantPresheafHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (Q : PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R))) :
    ((constantPresheaf.{t, u} k R).obj M ⟶ Q) ≃
      (M ⟶ Q.obj (op (finalObject k))) where
  toFun f := f.app (op (finalObject k))
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        ((Q.map (toFinal k U.unop).op).hom.comp f.hom)
      naturality := by
        intro U V i
        ext x
        change Q.map (toFinal k V.unop).op (f.hom x) =
          Q.map i (Q.map (toFinal k U.unop).op (f.hom x))
        rw [← Q.map_comp_apply]
        have h : (toFinal k V.unop).op = (toFinal k U.unop).op ≫ i := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact (MorphismProperty.Over.w i.unop).symm
        rw [h] }
  left_inv f := by
    ext U x
    exact (PresheafOfModules.naturality_apply f (toFinal k U.unop).op x).symm
  right_inv f := by
    ext x
    change Q.map (toFinal k (finalObject k)).op (f.hom x) = f.hom x
    have h : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    rw [h, op_id, Q.map_id]
    rfl

private def constantHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (F : Modules.{t, u} k (constantRing.{t, u} k R)) :
    ((constantModules.{t, u} k R).obj M ⟶ F) ≃
      (M ⟶ (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) :=
  (PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t, max u (t + 1), t + 1}
    (constantUnit.{t, u} k R)).trans
    (constantPresheafHomEquiv.{t, u} k M
      ((PresheafOfModules.restrictScalars (constantUnit.{t, u} k R)).obj F.val))

private theorem constantHomEquiv_naturality_left
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N)
    (F : Modules.{t, u} k (constantRing.{t, u} k R))
    (g : (constantModules.{t, u} k R).obj N ⟶ F) :
    constantHomEquiv.{t, u} k M F ((constantModules.{t, u} k R).map f ≫ g) =
      f ≫ constantHomEquiv.{t, u} k N F g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
            (constantUnit.{t, u} k R)).map
          ((constantPresheaf.{t, u} k R).map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  rfl

private theorem constantHomEquiv_naturality_right
    (M : ModuleCat.{max u (t + 1)} R)
    {F G : Modules.{t, u} k (constantRing.{t, u} k R)}
    (f : (constantModules.{t, u} k R).obj M ⟶ F) (g : F ⟶ G) :
    constantHomEquiv.{t, u} k M G (f ≫ g) =
      constantHomEquiv.{t, u} k M F f ≫
        (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).map g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def constantAdjunction :
    constantModules.{t, u} k R ⊣
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantHomEquiv.{t, u} k
      homEquiv_naturality_left_symm := by
        intro M N F f g
        apply (constantHomEquiv.{t, u} k M F).injective
        rw [Equiv.apply_symm_apply, constantHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ constantHomEquiv_naturality_right k _ f g }

open SheafOfModules.CoefficientOrdinaryProof

private def extensionFunctor : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B :=
  constantModules.{t, u} k R ⋙ tensorFunctor.{max u (t + 1), t + 1, t} α

private def extensionSectionsIso :
    restriction.{max u (t + 1), t + 1, t} α ⋙ sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) ≅
      sections.{t, u} k B α :=
  NatIso.ofComponents (fun F ↦
    (show ((restriction.{max u (t + 1), t + 1, t} α ⋙
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) ≃ₗ[R]
      (sections.{t, u} k B α).obj F from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso) (by intros; rfl)

private def extensionAdjunction : extensionFunctor.{t, u} k B α ⊣ sections.{t, u} k B α :=
  ((constantAdjunction.{t, u} k).comp (tensorAdjunction.{max u (t + 1), t + 1, t} α)).ofNatIsoRight
    (extensionSectionsIso.{t, u} k B α)

private theorem extensionAdjunction_formula
    (M : ModuleCat.{max u (t + 1)} R) (F : Modules.{t, u} k B)
    (h : (extensionFunctor.{t, u} k B α).obj M ⟶ F) (x : M) :
    ((extensionAdjunction.{t, u} k B α).homEquiv M F h).hom x =
      h.val.app (op (finalObject k)) (extensionElement.{t, u} k B α M
        (op (finalObject k)) 1 x) := by
  rfl

private theorem extensionAdjunction_explicit :
    ExplicitAdjunction.{t, u} k B α (extensionFunctor.{t, u} k B α)
      (fun _ ↦ rfl) (extensionAdjunction.{t, u} k B α) := by
  constructor
  · exact extensionAdjunction_formula.{t, u} k B α
  · intro M F f U b x
    let h := ((extensionAdjunction.{t, u} k B α).homEquiv M F).symm f
    let q := (tensorAdjunction.{max u (t + 1), t + 1, t} α).homEquiv
      ((constantModules.{t, u} k R).obj M) F h
    let p := PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R) q
    have hp := PresheafOfModules.naturality_apply p (toFinal k U.unop).op x
    have hp' : h.val.app U (extensionElement.{t, u} k B α M U 1 x) =
        F.val.map (toFinal k U.unop).op (f.hom x) := by
      have hf := congrArg (fun g ↦ g.hom x)
        (((extensionAdjunction.{t, u} k B α).homEquiv M F).apply_symm_apply f)
      change h.val.app (op (finalObject k))
        (extensionElement.{t, u} k B α M (op (finalObject k)) 1 x) = f.hom x at hf
      change h.val.app U (extensionElement.{t, u} k B α M U 1 x) =
        F.val.map (toFinal k U.unop).op
          (h.val.app (op (finalObject k))
            (extensionElement.{t, u} k B α M (op (finalObject k)) 1 x)) at hp
      rw [hf] at hp
      exact hp
    change h.val.app U (extensionElement.{t, u} k B α M U b x) = _
    rw [← hp']
    let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (𝟙 (ring.{t, u} k B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} α
          ((constantModules.{t, u} k R).obj M))
    let H := η.app U ≫ h.val.app U
    change H.hom (b ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
      constantElement.{t, u} k R M U x) =
        b • H.hom ((1 : B.obj.obj U) ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
          constantElement.{t, u} k R M U x)
    rw [← H.hom.map_smul]
    congr 1
    change _ = (b * 1) ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
      constantElement.{t, u} k R M U x
    simp only [mul_one]

private theorem constant_exact :
    PreservesFiniteLimits (constantModules.{t, u} k R) ∧
      PreservesFiniteColimits (constantModules.{t, u} k R) := by
  let P := constantPresheaf.{t, u} k R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P (PresheafOfModules.sheafification
    (constantUnit.{t, u} k R)),
    comp_preservesFiniteColimits P (PresheafOfModules.sheafification
      (constantUnit.{t, u} k R))⟩

private theorem extension_exact
    (hf : SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      ((SheafOfModules.restrictScalars.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat RingCat)).map α)).obj
            (SheafOfModules.unit (ring.{t, u} k B)))) :
    PreservesFiniteLimits (extensionFunctor.{t, u} k B α) ∧
      PreservesFiniteColimits (extensionFunctor.{t, u} k B α) := by
  let C := constantRing.{t, u} k R
  let N := (restriction.{max u (t + 1), t + 1, t} α).obj
    (SheafOfModules.unit (ring.{t, u} k B))
  let := SheafOfModules.isMonoidal_W_independentCoefficients C
  let := SheafOfModules.monoidalCategory C
  let := SheafOfModules.symmetricCategory C
  have hN := SheafOfModules.flat_to_cat C N hf
  have : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft N) := hN.1.1
  obtain ⟨e, he⟩ := SheafOfModules.exists_changeOfRings_tensor_comparison_independent α
  let iso : tensorFunctor.{max u (t + 1), t + 1, t} α ⋙
      SheafOfModules.toSheaf (ring.{t, u} k B) ≅
    CategoryTheory.MonoidalCategory.tensorLeft N ⋙
      SheafOfModules.toSheaf (ring.{t, u} k C) :=
    NatIso.ofComponents e (fun f ↦ he f)
  have : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft N ⋙
      SheafOfModules.toSheaf (ring.{t, u} k C)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (tensorFunctor.{max u (t + 1), t + 1, t} α ⋙
      SheafOfModules.toSheaf (ring.{t, u} k B)) :=
    preservesFiniteLimits_of_natIso iso.symm
  have : PreservesFiniteLimits (tensorFunctor.{max u (t + 1), t + 1, t} α) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _)
  have : PreservesFiniteLimits (constantModules.{t, u} k R) := (constant_exact k).1
  let : (extensionFunctor.{t, u} k B α).IsLeftAdjoint :=
    (extensionAdjunction.{t, u} k B α).isLeftAdjoint
  have : PreservesFiniteColimits (extensionFunctor.{t, u} k B α) :=
    inferInstance
  exact ⟨comp_preservesFiniteLimits _ _, inferInstance⟩

end Ordinary

/-- Exact coefficient extension and sections, with the actual normalized adjunction.
Source: blueprint point-dualizing proof, second sentence, and point comparison,
third paragraph (blueprint: lem-pod-integral-point-coefficient-adjunction).

Proof:
1. The coefficient DVR theorem makes the integers a PID and hence Noetherian.
The profinite-tower theorem identifies the integers with their compatible positive
quotients, normalized by reduction.
2. Every covering sieve of the final object contains its identity. Local bijectivity
of the constant sheafification unit therefore makes its final component bijective.
Naturality of this unit proves compatibility with finite transition maps. The limit
projection equations give the completed scalar projection formula. Joint injectivity
of those projections and the profinite-tower theorem prove the completed bijection.
3. Repeat the continuous-function comparison of the finite-constant-sections theorem
at the independent coefficient universe. Open fibres give local surjectivity; a point
of a nonempty object detects equality of constants, and the empty cover handles the
empty object. The comparison is natural for quotient ring maps. At each point a section
of the completion therefore gives a compatible quotient family, hence an integer.
A nonzero integer cannot annihilate such a value. Joint injectivity of the projections
then makes the entire section module torsion free, so it is flat over the PID.
For a finite relation with coefficients in the constant ring sheaf, intersect the
covering sieves on which those coefficients lift to constants. Sectionwise flatness
factors the restricted relation. Applying the constant unit to its matrix supplies
the local equational criterion for flatness over the constant ring sheaf.
4. Compose the constant-module sheafification adjunction with the proved ordinary
tensor/restriction adjunction. Evaluation at the final object and restriction along its
unique maps give both normalized Hom formulas. The independent-universe tensor comparison
identifies underlying scalar extension with tensoring by the restricted coefficient unit.
Its flatness gives finite limits; the adjunction gives finite colimits. Evaluating the
Hom formulas on identities proves the unit and counit formulas. The independent-universe
point-sections theorem supplies exact sections. Exact additive functors preserve finite
limits and finite colimits of unbounded complexes degreewise. -/
theorem integral_point_coefficient_adjunction (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p) :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    SheafOfModules.IsFlatOnSite
      ((SheafOfModules.restrictScalars.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of D.k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (alpha D.k l E))).obj
          (SheafOfModules.unit (ring.{t, u} D.k (B D.k l E)))) ∧
    (∀ n : ℕ, Function.Bijective (finiteValue D.k l E n)) ∧
    (∀ (n : ℕ) (a : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))),
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app
          (op (finalObject D.k)) (finiteValue D.k l E (n + 1) a) =
        finiteValue D.k l E n (ULift.up (Padic.coefficientExtensionTransition l E (n + 1)
          a.down))) ∧
    Function.Bijective (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E)
      (op (finalObject D.k))) ∧
    (∀ (n : ℕ) (r : R l E),
      (completedIntegralCoefficientProjection l E (Spec (.of D.k)) D hl n).hom.app
          (op (finalObject D.k))
          (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E) (op (finalObject D.k)) r) =
        finiteValue D.k l E n
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) r.down))) ∧
    exactFunctor _ _ (sections.{t, u} D.k (B D.k l E) (alpha D.k l E)) ∧
    ∃ (L : ModuleCat.{max u (t + 1)} (R l E) ⥤ Modules.{t, u} D.k (B D.k l E))
      (hobj : ∀ M, L.obj M = extensionObject.{t, u} D.k (B D.k l E) (alpha D.k l E) M),
      (∀ (M N : ModuleCat.{max u (t + 1)} (R l E)) (f : M ⟶ N),
        L.map f = eqToHom (hobj M) ≫
          extensionMorphism.{t, u} D.k (B D.k l E) (alpha D.k l E) f ≫
          eqToHom (hobj N).symm) ∧
      exactFunctor _ _ L ∧
      ∃ adj : L ⊣ sections.{t, u} D.k (B D.k l E) (alpha D.k l E),
        ExplicitAdjunction.{t, u} D.k (B D.k l E) (alpha D.k l E) L hobj adj ∧
        (∀ (M : ModuleCat.{max u (t + 1)} (R l E)) (x : M),
          (adj.unit.app M).hom x = generator.{t, u} D.k (B D.k l E) (alpha D.k l E)
            L hobj M (op (finalObject D.k)) 1 x) ∧
        (∀ (F : Modules.{t, u} D.k (B D.k l E)) (U : (Spec (.of D.k)).ProEtᵒᵖ)
          (b : (B D.k l E).obj.obj U)
          (y : (sections.{t, u} D.k (B D.k l E) (alpha D.k l E)).obj F),
          (adj.counit.app F).val.app U
              (generator.{t, u} D.k (B D.k l E) (alpha D.k l E) L hobj
                ((sections.{t, u} D.k (B D.k l E) (alpha D.k l E)).obj F) U b y) =
            b • F.val.map (toFinal D.k U.unop).op y) ∧
        exactFunctor _ _ (extensionComplex.{t, u} D.k (B D.k l E) (alpha D.k l E) L adj) ∧
        exactFunctor _ _ (sectionComplex.{t, u} D.k (B D.k l E) (alpha D.k l E)) := by
  classical
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    hdvr.2.2.2.2.2.2.2.2.1
  have hsections := (ProEtale.point_proEtale_sections_exact_of_universes.{t, u, 0, 0}
    D.k).2 (B D.k l E)
  have hΓlim : PreservesFiniteLimits (sections.{t, u} D.k (B D.k l E) (alpha D.k l E)) := by
    let := hsections.1
    exact comp_preservesFiniteLimits _ _
  have hΓcol : PreservesFiniteColimits (sections.{t, u} D.k (B D.k l E)
      (alpha D.k l E)) := by
    let := hsections.2.1
    change PreservesFiniteColimits
      (ProEtale.pointModuleSectionsOfUniverses.{t, u} D.k (B D.k l E) ⋙
        ModuleCat.restrictScalars (scalar.{t, u} D.k (B D.k l E) (alpha D.k l E)
          (op (finalObject D.k))))
    infer_instance
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ⟨hΓlim, hΓcol⟩, ?_⟩
  · exact completed_flat l E D hl
  · intro n
    exact constants_bijective D.k (coefficientRing.{t, u} l E (n + 1) false)
  · intro n a
    exact finite_transition D.k l E n _ a
  · exact completed_bijective l E D hl
  · intro n r
    exact scalar_projection l E D hl n _ r
  · let L := Ordinary.extensionFunctor.{t, u} D.k (B D.k l E) (alpha D.k l E)
    let hobj : ∀ M, L.obj M = extensionObject.{t, u} D.k (B D.k l E)
        (alpha D.k l E) M := fun _ ↦ rfl
    let adj := Ordinary.extensionAdjunction.{t, u} D.k (B D.k l E) (alpha D.k l E)
    have hexp := Ordinary.extensionAdjunction_explicit.{t, u} D.k
      (B D.k l E) (alpha D.k l E)
    obtain ⟨hLlim, hLcol⟩ := Ordinary.extension_exact D.k (B D.k l E)
      (alpha D.k l E) (completed_flat l E D hl)
    refine ⟨L, hobj, ?_, ⟨hLlim, hLcol⟩, adj, hexp, ?_, ?_, ?_, ?_⟩
    · intro M N f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · intro M x
      have h := hexp.1 M (L.obj M) (𝟙 _) x
      rw [adj.homEquiv_id] at h
      exact h
    · intro F U b y
      have h := hexp.2 _ F (𝟙 _) U b y
      rw [adj.homEquiv_symm_id] at h
      exact h
    · let := adj.left_adjoint_additive
      let : PreservesFiniteLimits L := hLlim
      let : PreservesFiniteColimits L := hLcol
      unfold extensionComplex
      apply (exactFunctor_iff _).2
      exact ⟨inferInstance, inferInstance⟩
    · let : PreservesFiniteLimits (sections.{t, u} D.k (B D.k l E)
          (alpha D.k l E)) := hΓlim
      let : PreservesFiniteColimits (sections.{t, u} D.k (B D.k l E)
          (alpha D.k l E)) := hΓcol
      apply (exactFunctor_iff _).2
      exact ⟨inferInstance, inferInstance⟩

end WeilConjectures.IntegralPointCoefficientAdjunction
