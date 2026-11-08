/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Topology.ContinuousMapCondensedRing
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Filtered.Final
public import Submission.WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Regular scalars and finite quotients of completed coefficients

Source: blueprint, sec-smooth-purity, sk-lem-sp-tower proof, first paragraph,
and coefficient setup in sk-def-sp-coefficient-towers; Stacks Tags 00WK and 00YR.
(blueprint: lem-sp-completed-coefficient-regular-quotients).

Natural level n denotes exponent n+1. The commutative-ring objects below retain the
underlying ring sheaves of the recorded coefficient towers. Quotients are the existing
sheafifications of sectionwise principal-power quotients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- A constant integral scalar as a compatible section of the actual completed ring.
Source: blueprint, coefficient setup, constant scalar convention
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spCompletedScalarSection (a : Padic.coefficientExtensionIntegers l E) :
    ((completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat.{max u (t + 1)}).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (Functor.whiskerRight (integralConstantToCompletionOfUniverses l E T).hom
      (forget RingCat.{max u (t + 1)}))
    ((Functor.sectionsFunctor T.ProEtᵒᵖ).map
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget CommRingCat.{max u (t + 1)}))
      ⟨fun _ ↦ ULift.up a, fun _ ↦ rfl⟩)

private theorem constRing_surj {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private def scalarHom (U : T.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
  ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom.comp
    (((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom)

private abbrev constO :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

private def constMap : constO l E T ⟶ completedIntegralCommRingSheafUnrestricted l E T where
  hom :=
    { app U :=
        letI := completedIntegralCoefficientCommRingUnrestricted l E T U
        CommRingCat.ofHom ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom
      naturality := by
        intro U V f
        apply (forget₂ CommRingCat RingCat).map_injective
        exact (integralConstantToCompletionOfUniverses l E T).hom.naturality f }

private def constQuot (I : Ideal (Padic.coefficientExtensionIntegers l E)) :
    constO l E T ⟶ (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))) :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I)))

private theorem uniformizer_normalized (n : ℕ) :
    constMap l E T ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      constQuot l E T (Padic.coefficientExtensionIdeal l E (n + 1)) := by
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x)
    (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))

private theorem projection_scalar {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (p.hom.app U) (scalarHom l E T U a) =
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))).app U
          (ULift.up (Ideal.Quotient.mk I a)) := by
  have hc := congrArg (fun h ↦ h.hom.app U
    ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
        (ULift.up a))) hp
  let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
    CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
  have hn := congrArg (fun h ↦ h.app U (ULift.up a))
    (toSheafify_naturality (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map φ))
  exact hc.trans hn.symm

private theorem projection_surjective {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I) (U : T.ProEtᵒᵖ) :
    Function.Surjective (p.hom.app U) := by
  have : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  have hs : Function.Surjective ((constQuot l E T I).hom.app U) := by
    let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
      CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
    have hsφ : Function.Surjective φ := by
      intro b
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
      exact ⟨ULift.up a, ULift.ext ha⟩
    exact constRing_surj (Scheme.ProEt.topology T) φ hsφ U
  intro x
  obtain ⟨a, ha⟩ := hs x
  exact ⟨(constMap l E T).hom.app U a,
    (congrArg (fun h ↦ h.hom.app U a) hp).trans ha⟩

private theorem scalar_killed {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) (m : ℕ)
    (ha : a ^ m ∈ I) : (p.hom.app U) (scalarHom l E T U a ^ m) = 0 := by
  rw [← map_pow, projection_scalar l E T p hp]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact map_zero _

private theorem uniformizer_kernel (n : ℕ) (U : T.ProEtᵒᵖ) :
    RingHom.ker ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom =
      sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
        (n + 1) U := by
  ext x
  change _ = 0 ↔ x ∈ Ideal.span
    {scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := completedIntegralProjection_divisible l E T n U x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hz := scalar_killed l E T _ (uniformizer_normalized l E T n) U
      (Padic.coefficientExtensionUniformizer l E) (n + 1)
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n + 1))
    change ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom
      (scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) = 0 at hz
    rw [map_mul, hz, zero_mul]

end AlgebraicGeometry.ProEtale
