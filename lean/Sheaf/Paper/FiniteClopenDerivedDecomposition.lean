/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.FiniteClopenDecompositionCore



import all Sheaf.Paper.FiniteClopenDecompositionCore

/-! # Finite clopen decomposition of derived coefficient categories

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-derived-decomposition).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
-/

@[expose] public noncomputable section
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
-- Preserve the fixed coefficient universes after importing the private support API.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
  AlgebraicGeometry.Scheme.ProEt.ClopenScalar.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenScalar.locallyBijective
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.locallyBijective
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.RingedDerivedNative.monoidal
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

universe u w v c₀ d₀ v₀ z₀ r₀
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

attribute [-instance] WeilConjectures.OpenCompletedRestriction.globalHasDerived
  SheafOfModules.scalarRestriction_limits SheafOfModules.scalarRestriction_colimits

attribute [local irreducible] clopenRing Scheme.residueField

section Decomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Exact module equivalence and its explicit sectionwise inverse.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 1--3 of the node. The components cover the pro-etale site; distinct
intersections are empty. Glue modules and morphisms (module-sheaf gluing and set
sheaf morphism descent). On a test object V the inverse has sections the product
of the sections on V times_X Xi. Restriction maps and scalar actions are componentwise.
The sheaf axiom gives the unit and counit. Additivity is sectionwise and an additive
equivalence preserves kernels and cokernels. Empty components give zero factors;
the empty cover forces every section group to be zero. -/
theorem finiteClopen_module_equivalence (n : ℕ) (integral : Bool) :
    ∃ e : clopenModules X.left (P.clopenRing X.left n integral) ≌
        (∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      e.functor = Functor.pi' (fun i ↦
        clopenRestriction (j i).left (P.clopenRing X.left n integral)) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ∃ φ : ∀ (F : ∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
          (V : X.left.ProEt),
        ((e.inverse.obj F).val.obj (op V)) ≃+
          (∀ i, (F i).val.obj (op ((Scheme.proEtaleBaseChange (j i).left).obj V))),
        (∀ F V (r : (P.clopenRing X.left n integral).obj.obj (op V))
          (x : (e.inverse.obj F).val.obj (op V)) (i : I),
          φ F V (r • x) i =
            ((P.clopenRing X.left n integral).obj.map
              (MorphismProperty.Over.homMk
                (A := (clopenSiteInclusion (j i).left).obj
                  ((Scheme.proEtaleBaseChange (j i).left).obj V)) (B := V)
                (pullback.fst V.hom (j i).left) pullback.condition).op r) • φ F V x i) ∧
        (∀ (F : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (V W : X.left.ProEt) (f : V ⟶ W) (x : (e.inverse.obj F).val.obj (op W)),
          φ F V ((e.inverse.obj F).val.map f.op x) =
            fun i ↦ (F i).val.map ((Scheme.proEtaleBaseChange (j i).left).map f).op
              (φ F W x i)) ∧
        (∀ (F G : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (a : F ⟶ G) (V : X.left.ProEt) (x : (e.inverse.obj F).val.obj (op V)),
          φ G V ((e.inverse.map a).val.app (op V) x) =
            fun i ↦ (a i).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F V x i)) := by
  classical
  let R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (P.clopenRing X.left n integral)
  have hc : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left := by
    intro x
    exact Set.mem_iUnion.mp (show x ∈ ⋃ i, Set.range (j i).left by rw [hcover]; trivial)
  obtain ⟨G, η, ε, _, h₁, h₂, σ, hs, hr, hm, _, _⟩ :=
    Scheme.ProEt.ClopenRoos.normalized_module_gluing.{u, u + 1, u, w}
      X.left I (fun i ↦ (Xi i).left) (fun i ↦ (j i).left) hdisjoint hc R
      (by
        intro U a b
        exact @mul_comm ((P.clopenRing X.left n integral).obj.obj U) inferInstance a b)
  let E : clopenModules X.left (P.clopenRing X.left n integral) ≌
      (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))) :=
    CategoryTheory.Equivalence.mk _ G η ε
  refine ⟨E, rfl, inferInstance, inferInstance, inferInstance, inferInstance, σ, hs, ?_, ?_⟩
  · intro F V W f x
    funext i
    exact hr F W V f x i
  · intro F G f V x
    funext i
    exact hm F G f V x i



set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The degreewise restrictions induce the product of the unbounded derived categories,
with componentwise cohomology, tensor and the regular coefficient unit.
Source: Stacks 04TS, 015F, 06YS, 0G7D
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 4--6. Restriction and insertion into one coordinate are exact.
Their identities descend through quasi-isomorphisms, so the product here is the
product of derived categories. Exact restriction commutes with cohomology. The
bilinear universal property identifies ordinary tensors and the coefficient unit.
K-flatness is detected componentwise by testing against insertions of acyclic
complexes. Descending the pure-tensor comparison on K-flat resolutions gives
the natural tensor isomorphism, with the normalized existing tensor models. -/
theorem finiteClopen_unbounded_decomposition (n : ℕ) (integral : Bool) :
    (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))).IsEquivalence ∧
    (∀ (i : I) (m : ℤ), Nonempty
      (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ⋙
          DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙
          clopenRestriction (j i).left (P.clopenRing X.left n integral))) ∧
    (∀ i : I, Nonempty
      ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (P.clopenRing X.left n integral)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))))) ∧
    ∀ (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology X.left)
        (P.clopenRing X.left n integral)) (i : I)
      (Mi : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology (Xi i).left)
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      Nonempty (M.closed.tensor ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ≅
        ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).prod
          (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))) ⋙
            Mi.closed.tensor) := by
  exact unboundedForRing P X Xi j hdisjoint hcover (P.clopenRing X.left n integral)



attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Strict towers and their functorial Roos complexes restrict termwise.
Source: Stacks 08TC (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 7. Restriction keeps sectionwise countable products and their
projections, including the transition endomorphism 1-s. It therefore commutes
with its functorial shifted mapping cone on objects and strict maps. Exactness
of countable pro-etale products identifies these products with derived products.
Applying the exact restriction to any Roos triangle gives the component Roos
triangle, with its original maps; no canonical uniqueness of bare cones is used. -/
theorem finiteClopen_strict_roos (n : ℕ) (integral : Bool) (i : I) :
    Nonempty (integralOperationsRoosFunctor ⋙
        (clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
            (ComplexShape.up ℤ)) ⋙ integralOperationsRoosFunctor) := by
  let F := clopenRestriction (j i).left (P.clopenRing X.left n integral)
  have : F.IsRightAdjoint :=
    AlgebraicGeometry.ProEtale.VaryingRing.largePush_isRightAdjoint
      (Scheme.ProEt.topology (Xi i).left) (Scheme.ProEt.topology X.left)
      (clopenSiteInclusion (j i).left) _ _ (𝟙 _)
  exact clopenRoosIso F


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Finite constructibility, fixed cohomological intervals and fixed Tor intervals
are detected on the components; hence both finite-coefficient subcategories split.
Source: blueprint section-invariant well-definedness, finite stage
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 8. Intersect a finite stratification with the clopen pieces;
conversely unite their finitely many stratifications. Cohomology is componentwise,
so every common interval works. Test Tor against inserted degree-zero modules and
use componentwise derived tensor. Lifting the restriction functors to these full
subcategories and restricting the gluing inverse gives the two equivalences.
No nonempty-index hypothesis is needed; ordered intervals also work for zero objects. -/
theorem finiteClopen_finite_bounds (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b ↔
        ∀ i, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
      classical
      let Pn : PurityFiniteSetting.{u} := { P with
        level := n + 1
        level_pos := Nat.succ_pos n }
      let : X.left.Over (Spec (CommRingCat.of Pn.field.k)) := ⟨X.hom⟩
      have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hft
      have : QuasiCompact (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hqc
      have H := finite_clopen_constructibility_bounds Pn X.left (fun i ↦ (Xi i).left)
        (fun i ↦ (j i).left) hdisjoint hcover
      let e (i : I) := Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left
      have hsupport : ∀ (i : I),
          Scheme.proEtaleCohomologicalSupport
              ((Scheme.proEtaleConstantRingDerivedPullback Pn.Ring (j i).left).obj K) =
            Scheme.proEtaleCohomologicalSupport
              ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) :=
        fun i ↦ clopenSupport_iso ((e i).app K)
      have hbound : ∀ a b : ℤ, a ≤ b →
          (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
            ∀ i, Scheme.proEtaleCohomologicalSupport
              ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
                Set.Icc a b) := by
        intro a b hab
        simpa only [hsupport] using H.2.2.2.2.1 K a b hab
      refine ⟨?_, hbound, ?_⟩
      · have hconstructible := H.2.2.2.1 K
        have hcoh :
            (∀ m : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X.left Pn.Ring
              ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
            ∀ (i : I) (m : ℤ), Scheme.IsConstructibleProEtaleModuleSheaf (Xi i).left Pn.Ring
              ((DerivedCategory.homologyFunctor _ m).obj
                ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) := by
          refine hconstructible.trans ⟨?_, ?_⟩
          · intro h i m
            exact clopenSheafConstructible_iso
              ((DerivedCategory.homologyFunctor _ m).mapIso ((e i).app K)) (h i m)
          · intro h i m
            exact clopenSheafConstructible_iso
              ((DerivedCategory.homologyFunctor _ m).mapIso ((e i).app K)).symm (h i m)
        change (_ ∧ _) ↔ ∀ i, _ ∧ _
        constructor
        · rintro ⟨hb, hc⟩
          obtain ⟨a, ha⟩ := hb.bddBelow
          obtain ⟨b, hb⟩ := hb.bddAbove
          have hs : Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc (min a b) (max a b) :=
            fun q hq ↦ ⟨(min_le_left a b).trans (ha hq), (hb hq).trans (le_max_right a b)⟩
          intro i
          exact ⟨(Set.finite_Icc _ _).subset ((hbound _ _
            ((min_le_left a b).trans (le_max_left a b))).mp hs i), hcoh.mp hc i⟩
        · intro h
          have hs := Set.finite_iUnion (fun i ↦ (h i).1)
          obtain ⟨a, ha⟩ := hs.bddBelow
          obtain ⟨b, hb⟩ := hs.bddAbove
          refine ⟨(Set.finite_Icc (min a b) (max a b)).subset
            ((hbound _ _ ((min_le_left a b).trans (le_max_left a b))).mpr ?_),
            hcoh.mpr (fun i ↦ (h i).2)⟩
          intro i q hq
          have hmem : q ∈ ⋃ i, Scheme.proEtaleCohomologicalSupport
              ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) :=
            Set.mem_iUnion.mpr ⟨i, hq⟩
          exact ⟨(min_le_left a b).trans (ha hmem), (hb hmem).trans (le_max_right a b)⟩
      · intro a b hab
        refine (H.2.2.2.2.2.1 K a b hab).trans ?_
        exact forall_congr' (fun i ↦ clopenTor_iso ((e i).app K) a b)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restriction on the finite constructible full subcategory, with its actual
ambient pullback on both objects and arrows. Source: blueprint finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteConstructiblePullback (n : ℕ) (i : I) :=
  (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K.obj).1.mp
      K.property) i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite-Tor condition is detected on the finite list of components.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: use finiteClopen_finite_bounds for constructibility and Tor in a fixed interval.
For the converse take the minimum and maximum of the finitely many component bounds.
For no components take [0,0]; vanishing is detected by the empty covering sheaf axiom. -/
theorem finiteClopen_finiteTor_iff (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) := by
  classical
  have H := P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K
  constructor
  · rintro ⟨hc, a, b, ht⟩ i
    exact ⟨H.1.mp hc i, a, b, (H.2.2 a b ht.1).mp ht i⟩
  · intro h
    have hc := H.1.mpr (fun i ↦ (h i).1)
    choose a b ht using fun i ↦ (h i).2
    obtain ⟨c, hc'⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd'⟩ := (Set.finite_range b).bddAbove
    refine ⟨hc, min c d, max c d, (H.2.2 _ _ ?_).mpr ?_⟩
    · exact (min_le_left c d).trans (le_max_left c d)
    · intro i
      exact clopenTor_mono (ht i) ((min_le_left c d).trans (hc' ⟨i, rfl⟩))
        ((hd' ⟨i, rfl⟩).trans (le_max_right c d))


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite-Tor restriction is the full-subcategory lift of the recorded pullback.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteTorPullback (n : ℕ) (i : I) :=
  (finiteTorConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((finiteTorConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ (P.finiteClopen_finiteTor_iff X Xi j hdisjoint hcover n K.obj).mp K.property i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Both finite coefficient full-subcategory equivalences use these exact restrictions.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restrict the ambient derived equivalence using the componentwise predicates.
The inverse gluing preserves them by the converse parts of the two bound statements. -/
theorem finiteClopen_finite_equivalences (n : ℕ) :
    (Functor.pi' (fun i ↦ P.clopenFiniteConstructiblePullback X Xi j
      hdisjoint hcover n i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenFiniteTorPullback X Xi j
      hdisjoint hcover n i)).IsEquivalence := by
  let Pn : PurityFiniteSetting.{u} := { P with
    level := n + 1
    level_pos := Nat.succ_pos n }
  let : X.left.Over (Spec (CommRingCat.of Pn.field.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hft
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hqc
  have H := finite_clopen_constructibility_bounds Pn X.left (fun i ↦ (Xi i).left)
    (fun i ↦ (j i).left) hdisjoint hcover
  obtain ⟨e, ⟨he⟩⟩ := H.2.2.2.2.2.2.1
  obtain ⟨t, ⟨ht⟩⟩ := H.2.2.2.2.2.2.2.1
  constructor
  · apply Functor.isEquivalence_of_iso (F := e.functor)
    apply NatIso.pi'
    intro i
    apply Functor.fullyFaithfulCancelRight
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_pos n) (Xi i).left).ι
    exact isoWhiskerRight he (Pi.eval _ i) ≪≫
      isoWhiskerLeft _ (Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left)
  · apply Functor.isEquivalence_of_iso (F := t.functor)
    apply NatIso.pi'
    intro i
    apply Functor.fullyFaithfulCancelRight
      (finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_pos n) (Xi i).left).ι
    exact isoWhiskerRight ht (Pi.eval _ i) ≪≫
      isoWhiskerLeft _ (Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left)


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Tensor and integral reduction are componentwise for the actual coefficient functors.
Source: Stacks 06YS, 0G7D, 08TC; blueprint coefficient transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 5--6 and 9--11. Restriction carries sheaf tensor generators to the
same pure tensors. Descend on K-flat representatives to obtain the finite natural
comparison. For integral tensor and reduction, restrict the strict towers and
use the natural Roos comparison. Extend the resulting maps linearly to rational
Homs and then represent them at the common finite coefficient compositum.
All maps commute with identity and composite coefficient changes because the
pure-tensor formulas and the strict tower maps do. -/
theorem finiteClopen_tensor_and_reduction (i : I) :
    (∀ n : ℕ, Nonempty
      (finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).prod
          (finiteDerivedPullback P.coefficients.l P.extension n (j i).left)) ⋙
            finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty (P.clopenIntegralTensor X ⋙ P.clopenIntegralPullback (j i) ≅
      ((P.clopenIntegralPullback (j i)).prod (P.clopenIntegralPullback (j i))) ⋙
        P.clopenIntegralTensor (Xi i)) ∧
    Nonempty (P.clopenRationalTensor X ⋙ P.clopenRationalPullback (j i) ≅
      ((P.clopenRationalPullback (j i)).prod (P.clopenRationalPullback (j i))) ⋙
        P.clopenRationalTensor (Xi i)) ∧
    Nonempty (P.clopenCommonStageTensor X ⋙ P.clopenCommonStagePullback (j i) ≅
      ((P.clopenCommonStagePullback (j i)).prod (P.clopenCommonStagePullback (j i))) ⋙
        P.clopenCommonStageTensor (Xi i)) ∧
    (∀ n : ℕ, Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n)) ∧
    (∀ (m n : ℕ) (h : n ≤ m), Nonempty
      (coefficientFiniteQuotientDerived P.coefficients.l P.extension X.left h ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        finiteDerivedPullback P.coefficients.l P.extension m (j i).left ⋙
          coefficientFiniteQuotientDerived P.coefficients.l P.extension (Xi i).left h)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
      let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
      let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
      let l := P.coefficients.l
      let E := P.extension
      have h := derivedPullbackTensorIso l E (j i).left 0 P.coefficients.Qbar
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro n
        obtain ⟨e, _⟩ := (derivedPullbackTensorIso l E (j i).left n P.coefficients.Qbar).1
        exact ⟨e⟩
      · exact ⟨h.2.2.2.2.2.1.choose⟩
      · exact ⟨h.2.2.2.2.2.2.1.choose⟩
      · exact ⟨h.2.2.2.2.2.2.2.1.choose⟩
      · intro n
        let C := (sfIntegralConstructible l E X.left).ι
        let F := P.clopenIntegralPullback (j i)
        let SX := pullbackTensorCalculus l E X.left
        let SY := pullbackTensorCalculus l E (Xi i).left
        let G := C ⋙ SX.reduction ⋙ pullbackTensorSequenceDerived l E (j i).left
        have hc : IsIso (whiskerLeft G SY.adjunction.counit) := by
          apply (NatTrans.isIso_iff_isIso_app _).mpr
          intro K
          exact (pullbackTensorComparisonCounits l E (j i).left K K).2.1
        let e : F ⋙ (sfIntegralConstructible l E (Xi i).left).ι ⋙ SY.reduction ≅
            C ⋙ SX.reduction ⋙ pullbackTensorSequenceDerived l E (j i).left :=
          isoWhiskerLeft C
            (isoWhiskerRight (pullbackTensorIntegralPullbackModel l E (j i).left)
              SY.reduction) ≪≫
            @asIso _ _ _ _ (whiskerLeft G SY.adjunction.counit) hc
        exact ⟨(isoWhiskerRight
            (isoWhiskerLeft C (SX.reductionEvaluation n))
              (finiteDerivedPullback l E n (j i).left)).symm ≪≫
          isoWhiskerLeft (C ⋙ SX.reduction)
            (pullbackTensorDerivedEvaluation l E (j i).left n).symm ≪≫
          isoWhiskerRight e.symm (coefficientSequenceDerivedEvaluation l E (Xi i).left n) ≪≫
          isoWhiskerLeft (F ⋙ (sfIntegralConstructible l E (Xi i).left).ι)
            (SY.reductionEvaluation n)⟩
      · intro m n h
        exact ⟨(pullbackTensorQuotient l E (j i).left h).symm⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Integral finite-Tor restriction, including detection of each common interval
uniformly over every finite reduction.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: commute restriction with derived reduction and the strict Roos functor.
Completeness is the Roos triangle with its canonical reduction unit, hence is
componentwise. Apply finiteClopen_finite_bounds at every positive exponent; the
same a,b is retained, so these bounds are uniform in all reductions. A finite
union of the component intervals supplies common bounds for the inverse. -/
theorem finiteClopen_integral_bounds (K : sfIntegralConstructibleCategory
    P.coefficients.l P.extension X.left) :
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K.obj ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((P.clopenIntegralPullback (j i)).obj K).obj) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) ⊆ Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b)) := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  let ered (i : I) (n : ℕ) :
      (scalarReductionDerivedExtension l E (Xi i).left n).obj
          ((P.clopenIntegralPullback (j i)).obj K).obj ≅
        (finiteDerivedPullback l E n (j i).left).obj
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) :=
    (((P.finiteClopen_tensor_and_reduction X Xi j hdisjoint hcover i).2.2.2.2.1 n).some.app K).symm
  have hs (a b : ℤ) (hab : a ≤ b) :
      (∀ n, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) ⊆ Set.Icc a b) ↔
        ∀ i n, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b := by
    constructor
    · intro h i n
      rw [clopenSupport_iso (ered i n)]
      exact (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab |>.mp
        (h n) i
    · intro h n
      apply (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab |>.mpr
      intro i
      simpa only [clopenSupport_iso (ered i n)] using h i n
  have ht (a b : ℤ) (hab : a ≤ b) :
      (∀ n, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) a b) ↔
        ∀ i n, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b := by
    constructor
    · intro h i n
      apply (clopenTor_iso (ered i n) a b).mpr
      exact (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab |>.mp
        (h n) i
    · intro h n
      apply (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab |>.mpr
      exact fun i ↦ (clopenTor_iso (ered i n) a b).mp (h i n)
  refine ⟨?_, hs, ht⟩
  constructor
  · rintro ⟨_, a, b, hab, h⟩ i
    exact ⟨((P.clopenIntegralPullback (j i)).obj K).property,
      a, b, hab, fun n ↦ (ht a b hab).mp h i n⟩
  · intro h
    choose a b hab hb using fun i ↦ (h i).2
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range b).bddAbove
    refine ⟨K.property, min c d, max c d,
      (min_le_left c d).trans (le_max_left c d), ?_⟩
    apply (ht _ _ ((min_le_left c d).trans (le_max_left c d))).mpr
    intro i n
    exact clopenTor_mono (hb i n)
      ((min_le_left c d).trans (hc (Set.mem_range_self i)))
      ((hd (Set.mem_range_self i)).trans (le_max_right c d))



attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Lift the canonical constructible pullback to the integral finite-Tor category.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTorPullback (i : I) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X.left ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension (Xi i).left :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left).lift
    ((finiteTorConstructibleIntegral P.coefficients.l P.extension X.left).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension (j i).left)
    (fun K ↦ (P.finiteClopen_integral_bounds X Xi j hdisjoint hcover
      ⟨K.obj, K.property.1⟩).1.mp K.property i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Integral, rationalized, and common-stage constructible restriction equivalences.
The finite-Tor field categories are the very same categories by definition.
Source: blueprint section-invariant well-definedness, coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 9--11. The exact module equivalence preserves every reduction
and the strict Roos construction. Completeness, constructible reductions, and
bounds uniform in the positive level are thus componentwise. Finiteness of I
provides one common interval, both for cohomology and Tor. Restrict the integral
equivalence. Rationalization has unchanged objects and tensors each Hom with E;
finite products commute with that tensor via coordinate insertion and summation.
At the algebraically closed stage choose the finite compositum of all component
fields, glue there, and represent arrows there. Equality is checked after a further
finite compositum, proving full faithfulness and essential surjectivity. The empty
family gives the zero category, equivalent to the empty product category. -/
theorem finiteClopen_constructible_equivalences :
    (Functor.pi' (fun i ↦ P.clopenIntegralPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenIntegralTorPullback X Xi j
      hdisjoint hcover i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenRationalPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenCommonStagePullback (j i))).IsEquivalence := by
  sorry


attribute [local irreducible] rationalDerivedPullback constructibleIntegralPullback
  integralDerivedPullback
  integralScalarExtension

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Scalar extension commutes with the same restrictions, for arbitrary finite
coefficient extensions, including the identity map. Rationalization is compatible
with the integral restriction equivalence.
Source: blueprint coefficient transport, steps 6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: on strict K-flat representatives the two scalar/restriction composites
have identical pure-tensor maps at every quotient of the target coefficient
ring, with the same transition equations. Restricting Roos gives the natural
integral comparison. The rational comparison is its linear extension, and common
stages compute these same comparisons after a finite compositum. -/
theorem finiteClopen_scalar_extension (i : I)
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι X.left ⋙
          integralDerivedPullback P.coefficients.l L (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι (Xi i).left) ∧
    Nonempty (P.clopenIntegralPullback (j i) ⋙
        sfRationalConstructibleLocalization P.coefficients.l P.extension (Xi i).left ≅
      sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
        P.clopenRationalPullback (j i)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
    let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
    let l := P.coefficients.l
    let E := P.extension
    let C := (sfIntegralConstructible l E X.left).ι
    let F := integralDerivedPullback l E (j i).left
    let r := P.clopenIntegralPullback (j i)
    let D := (sfIntegralConstructible l E (Xi i).left).ι
    let δ : C ⋙ F ≅ r ⋙ D := pullbackInclusion l E (j i).left
    have hX : IsIso (whiskerLeft C (scalarCompletion l E L ι X.left)) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro K
      exact (scalarCompletion_existsUnique l E L ι X.left).exists.choose_spec.2
        K.obj K.property.1
    have hY : IsIso (whiskerLeft (r ⋙ D) (scalarCompletion l E L ι (Xi i).left)) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro K
      exact (scalarCompletion_existsUnique l E L ι (Xi i).left).exists.choose_spec.2
        _ ((P.clopenIntegralPullback (j i)).obj K).property.1
    let α := asIso (whiskerLeft C (scalarCompletion l E L ι X.left))
    let β := scalarPullbackOrdinary l E L ι (j i).left
    let γ := asIso (whiskerLeft (r ⋙ D) (scalarCompletion l E L ι (Xi i).left))
    constructor
    · refine ⟨?_⟩
      refine scalarSquare C F (integralDerivedPullback l L (j i).left)
        (integralOrdinaryDerivedScalar l E L ι X.left)
        (integralScalarExtension l E L ι X.left)
        (integralOrdinaryDerivedScalar l E L ι (Xi i).left)
        (integralScalarExtension l E L ι (Xi i).left) α β
          (isoWhiskerRight δ (integralOrdinaryDerivedScalar l E L ι (Xi i).left) ≪≫ γ ≪≫
            (isoWhiskerRight δ (integralScalarExtension l E L ι (Xi i).left)).symm) ≪≫
        isoWhiskerRight δ (integralScalarExtension l E L ι (Xi i).left) ≪≫
        Functor.associator r D (integralScalarExtension l E L ι (Xi i).left)
    · exact ⟨NatIso.ofComponents (fun K ↦ eqToIso
          ((rationalPullback_formula l E (j i).left).1
            ((sfRationalConstructibleLocalization l E X.left).obj K)).symm) (by
            intro K M f
            apply eq_of_heq
            let hK := ((rationalPullback_formula l E (j i).left).1
              ((sfRationalConstructibleLocalization l E X.left).obj K)).symm
            let hM := ((rationalPullback_formula l E (j i).left).1
              ((sfRationalConstructibleLocalization l E X.left).obj M)).symm
            exact (comp_eqToHom_heq _ hM).trans
              (((rationalPullback_formula l E (j i).left).2
                _ _ f 1).symm.trans (eqToHom_comp_heq _ hK).symm))⟩


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restriction preserves the specified coefficient units at every stage.
Source: blueprint coefficient transports, steps 5--6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the sheaf-level coefficient ring restricts to the component coefficient
ring, by localization of constant sheafification and sectionwise integral limits.
The regular modules therefore restrict to regular modules. The finite K-flat
and integral strict Roos formulas preserve this identification in degree zero.
Rationalization and the common-stage representative functors preserve these
isomorphisms, with no restriction on the chosen finite coefficient stage. -/
theorem finiteClopen_coefficient_units (i : I) :
    (∀ n : ℕ, Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
          (finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ≅
        finiteConstantCoefficientObject P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty ((P.clopenIntegralPullback (j i)).obj (P.clopenIntegralUnit X.left) ≅
      P.clopenIntegralUnit (Xi i).left) ∧
    Nonempty ((P.clopenRationalPullback (j i)).obj (P.clopenRationalUnit X.left) ≅
      P.clopenRationalUnit (Xi i).left) ∧
    ∀ B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
      Nonempty ((P.clopenCommonStagePullback (j i)).obj (P.clopenCommonStageUnit X.left B) ≅
        P.clopenCommonStageUnit (Xi i).left B) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
    let := fun k (x : (Xi k).left) ↦ (P.clopenResidue_isUnit (Xi k) x).invertible
    obtain ⟨v⟩ := integralUnitCheck P X Xi j P.extension i
    refine ⟨fun n ↦ finiteUnitCheck P X Xi j n i, ?_, ?_, ?_⟩
    · refine ⟨ObjectProperty.isoMk _ ?_⟩
      simpa only [clopenIntegralPullback, constructibleIntegralPullback,
        clopenIntegralUnit, ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj] using v
    · exact rationalUnitCheck P X Xi j P.extension i
        (P.clopenIntegralUnit X.left) (P.clopenIntegralUnit (Xi i).left) rfl rfl
    · exact commonUnitCheck P X Xi j i



attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The empty family forces the empty scheme and has the terminal product category.
Source: Stacks 04TS and the empty covering sheaf axiom
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the union of the empty family of images is empty, so the covering condition
makes X empty. Functions on an empty index type and their coordinatewise morphisms
are unique. The preceding equivalences identify each source category with that
product; this includes zero sheaves and complexes, with no chosen nonzero component. -/
theorem finiteClopen_empty [IsEmpty I] (n : ℕ) (integral : Bool) :
    IsEmpty X.left ∧
      Subsingleton (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))) ∧
      ∀ F G : (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
        Subsingleton (F ⟶ G) := by
  refine ⟨⟨fun x ↦ ?_⟩, inferInstance, fun F G ↦ ⟨fun f g ↦ funext (fun i ↦ isEmptyElim i)⟩⟩
  have hx : x ∈ ⋃ i, Set.range (j i).left := by rw [hcover]; trivial
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact isEmptyElim i



set_option allowUnsafeReducibility true
attribute [local reducible] clopenRing

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite derived restriction above is the recorded intrinsic inverse image,
after identifying its restricted constant coefficient sheaf with the component's.
The normalization on Q specifies termwise coefficient transport, including maps.
Source: Stacks 00XZ, 04TS, 015F
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: constant sheafification commutes with localization; its unit identifies
constant sections. Transport modules by the inverse ring isomorphism. The
underlying sectionwise restriction is the inverse image for an open immersion.
Its exact termwise descent is the recorded finiteDerivedPullback. -/
theorem finiteClopen_finite_restriction_identification (n : ℕ) (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left n false) ≅
        integralCoefficientCommRingSheaf P.coefficients.l P.extension (Xi i).left n)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n false))) ≌
        Scheme.proEtaleDerivedCategory (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty (clopenDerivedRestriction (j i).left (P.clopenRing X.left n false) ⋙
        e.functor ≅ finiteDerivedPullback P.coefficients.l P.extension n (j i).left) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
    let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
    let U : X.left.ProEt :=
      ⟨Over.mk (j i).left, show WeaklyEtale (j i).left from inferInstance⟩
    let d := (Scheme.finite_pullback_localization_cohomology P.coefficients.l
      P.extension n X.left U).some
    let c := d.ringIso.symm
    let G := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.inv
    let hAdd : G.Additive := scalarAdditive
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)
    let : G.IsEquivalence :=
      SheafOfModules.scalarRestriction_isEquivalence.{u + 1, u, u + 1} c.symm
    let hLimG : PreservesFiniteLimits G := inferInstance
    let hColG : PreservesFiniteColimits G := inferInstance
    let e := G.mapDerivedCategory.asEquivalence
    let F := clopenRestriction (j i).left (P.clopenRing X.left n false)
    let H := Scheme.proEtaleObjectModuleRestriction U
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) d.ringIso
    let hAddH : H.Additive := d.restrictionAdditive
    let hLimH : PreservesFiniteLimits H := d.restrictionLimits
    let hColH : PreservesFiniteColimits H := d.restrictionColimits
    let hAddF : F.Additive := clopenRestrictionAdditive (j i).left _
    let hFG : (F ⋙ G).Additive := additiveComp F G hAddF hAdd
    let hLimFG : PreservesFiniteLimits (F ⋙ G) :=
      @CategoryTheory.Limits.comp_preservesFiniteLimits _ _ _ _ _ _ F G inferInstance hLimG
    let hColFG : PreservesFiniteColimits (F ⋙ G) :=
      @CategoryTheory.Limits.comp_preservesFiniteColimits _ _ _ _ _ _ F G inferInstance hColG
    let α : F ⋙ G ≅ H :=
      pushforwardRestrictIso (clopenSiteInclusion (j i).left) _ _
    let β : clopenDerivedRestriction (j i).left (P.clopenRing X.left n false) ⋙
        e.functor ≅ H.mapDerivedCategory :=
      (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ F G
        inferInstance hAdd inferInstance inferInstance hLimG hColG).symm ≪≫
      @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ (F ⋙ G) H
        hFG d.restrictionAdditive hLimFG hColFG d.restrictionLimits d.restrictionColimits α
    exact ⟨c, e, ⟨G.mapDerivedCategoryFactors⟩, ⟨β ≪≫ d.derivedComparison.symm⟩⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The completed coefficient identification and its constructible comparison.
It relates the module-derived equivalence to the actual completed pullback;
completed pullback on arbitrary unbounded objects is not asserted to be an equivalence.
Source: Stacks 04TS; blueprint integral finite-clopen transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restriction preserves sectionwise inverse limits, so the compatible finite
constant-ring identifications give the completed ring identification. Transport
scalars along its inverse. On complete objects the normalized Roos construction
computes the original restriction, with the original canonical reduction units.
This identifies the two restrictions naturally on the full integral subcategory. -/
theorem finiteClopen_integral_restriction_identification (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left 0 true) ≅
        completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension (Xi i).left)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left 0 true))) ≌
        DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left 0 true) ⋙ e.functor ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
    let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
    let l := P.coefficients.l
    let E := P.extension
    let c := (OpenCompletedRestriction.coefficients l E (j i).left).completed.symm
    let G := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} c.inv
    let hAdd : G.Additive := scalarAdditive
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)
    let : G.IsEquivalence :=
      SheafOfModules.scalarRestriction_isEquivalence.{u + 1, u, u + 1} c.symm
    let hLimG : CategoryTheory.Limits.PreservesFiniteLimits G := inferInstance
    let hColG : CategoryTheory.Limits.PreservesFiniteColimits G := inferInstance
    let e : DerivedCategory (clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left 0 true))) ≌
        DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left) :=
      G.mapDerivedCategory.asEquivalence
    let F := clopenRestriction (j i).left (P.clopenRing X.left 0 true)
    let hAddF : F.Additive := clopenRestrictionAdditive (j i).left _
    let hFG : (F ⋙ G).Additive := additiveComp F G hAddF hAdd
    let hLimFG : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) :=
      @CategoryTheory.Limits.comp_preservesFiniteLimits _ _ _ _ _ _ F G inferInstance hLimG
    let hColFG : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) :=
      @CategoryTheory.Limits.comp_preservesFiniteColimits _ _ _ _ _ _ F G inferInstance hColG
    let α : F ⋙ G ≅ OpenCompletedRestriction.ordinary l E (j i).left :=
      pushforwardRestrictIso (clopenSiteInclusion (j i).left) _ _
    let β : clopenDerivedRestriction (j i).left (P.clopenRing X.left 0 true) ⋙
        e.functor ≅ OpenCompletedRestriction.derivedRestriction l E (j i).left :=
      (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ F G
        inferInstance hAdd inferInstance inferInstance hLimG hColG).symm ≪≫
      @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ (F ⋙ G) _
        hFG (OpenCompletedRestriction.ordinaryAdditive l E (j i).left)
        hLimFG hColFG (OpenCompletedRestriction.ordinaryLimits l E (j i).left)
        (OpenCompletedRestriction.ordinaryColimits l E (j i).left) α
    obtain ⟨d, hd⟩ := OpenCompletedRestriction.open_completed_restriction_complete
      l E (j i).left inferInstance inferInstance
    let C := (sfIntegralConstructible l E X.left).ι
    have hk : IsIso (whiskerLeft C (OpenCompletedRestriction.kappa l E (j i).left d)) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro K
      exact hd K.obj K.property
    exact ⟨c, e, ⟨G.mapDerivedCategoryFactors⟩,
      ⟨isoWhiskerLeft C β ≪≫
        @asIso _ _ _ _ (whiskerLeft C (OpenCompletedRestriction.kappa l E (j i).left d)) hk ≪≫
        pullbackInclusion l E (j i).left⟩⟩

end Decomposition
end PurityFiniteSetting
end WeilConjectures
