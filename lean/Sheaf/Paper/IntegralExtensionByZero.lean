/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.Paper.IntegralDerivedCoefficientData
import Sheaf.Paper.OpenExtensionConstantModelConstructible
import Sheaf.Paper.CondensedOpenExtensionProducts
import Sheaf.Paper.IntegralOpenExtensionReduction
import Sheaf.CategoryTheory.PretriangulatedKernelSplit

/-!
# Integral extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-int-compactness-ii,
`sk-cor-int-compactness-ii-extension-zero.md`, clauses (1)--(3); Stacks Project, Tag 09BP
(blueprint: det-cor-int-compactness-ii-extension-zero).

The coefficients are the continuous condensed integer ring of a finite extension of Q_l.
Reduction is actual derived tensor with its finite uniformizer-power quotient, regarded
as an integral module. Constructibility uses the recorded finite constant scalar models.
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe w v u' v'

open CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers

private theorem preservesLimitsFromProducts
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasProducts.{w} C] (F : C ⥤ D) [F.Additive]
    [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] :
    PreservesLimitsOfSize.{w, w} F where
  preservesLimitsOfShape := by
    intro J _
    constructor
    intro M
    constructor
    intro c hc
    classical
    let P := ∏ᶜ M.obj
    let R := ∏ᶜ fun a : Σ p : J × J, p.1 ⟶ p.2 ↦ M.obj a.1.2
    let s : P ⟶ R := Pi.lift fun a ↦ Pi.π M.obj a.1.1 ≫ M.map a.2
    let t : P ⟶ R := Pi.lift fun a ↦ Pi.π M.obj a.1.2
    let k : c.pt ⟶ P := Pi.lift fun j ↦ c.π.app j
    have hks : k ≫ s = k ≫ t := by
      apply Pi.hom_ext
      intro a
      simp [k, s, t, Category.assoc, c.w a.2]
    have hk : k ≫ (s - t) = 0 := by
      rw [Preadditive.comp_sub, hks, sub_self]
    let q (A : C) (a : A ⟶ P) (ha : a ≫ (s - t) = 0) : Cone M :=
      { pt := A
        π :=
          { app := fun j ↦ a ≫ Pi.π M.obj j
            naturality := by
              intro i j f
              have h' : a ≫ s = a ≫ t := by
                exact sub_eq_zero.mp (by simpa only [Preadditive.comp_sub] using ha)
              have h'' := congrArg
                (fun z ↦ z ≫ Pi.π (fun a : Σ p : J × J, p.1 ⟶ p.2 ↦ M.obj a.1.2)
                  ⟨(i,j),f⟩) h'
              simpa [s, t, Category.assoc] using h''.symm } }
    have hK : IsLimit (KernelFork.ofι k hk) := by
      refine KernelFork.IsLimit.ofι k hk (fun a ha ↦ hc.lift (q _ a ha)) ?_ ?_
      · intro A a ha
        apply Pi.hom_ext
        intro j
        simp [k, q, Category.assoc, hc.fac]
      · intro A a ha b hb
        apply hc.hom_ext
        intro j
        have h := congrArg (fun z ↦ z ≫ Pi.π M.obj j) hb
        simpa [k, q, Category.assoc] using h
    obtain ⟨hFK⟩ := F.preservesKernel_of_pretriangulated (s - t) k hk hK
    have hFk : F.map k ≫ F.map s = F.map k ≫ F.map t := by
      simpa only [← F.map_comp] using congrArg F.map hks
    let ff : Fork (F.map s) (F.map t) := Fork.ofι (F.map k) hFk
    have hff : IsLimit ff := by
      refine Fork.IsLimit.mk _
        (fun a ↦ hFK.lift (KernelFork.ofι a.ι (by
          rw [F.map_sub, Preadditive.comp_sub, a.condition, sub_self]))) ?_ ?_
      · intro a
        exact hFK.fac _ WalkingParallelPair.zero
      · intro a b hb
        apply hFK.hom_ext
        apply Fork.equalizer_ext (KernelFork.ofι (F.map k) _)
        have hh := hFK.fac (KernelFork.ofι a.ι (by
          rw [F.map_sub, Preadditive.comp_sub, a.condition, sub_self])) WalkingParallelPair.zero
        exact hb.trans hh.symm
    have hs (a : Σ p : J × J, p.1 ⟶ p.2) :
        F.map s ≫ F.map (Pi.π _ a) = F.map (Pi.π M.obj a.1.1) ≫ F.map (M.map a.2) := by
      rw [← F.map_comp, ← F.map_comp]
      simp [s]
    have ht (a : Σ p : J × J, p.1 ⟶ p.2) :
        F.map t ≫ F.map (Pi.π _ a) = F.map (Pi.π M.obj a.1.2) := by
      rw [← F.map_comp]
      simp [t]
    have hb := buildIsLimit (F := M ⋙ F)
      (c₁ := Fan.mk (F.obj P) (fun j ↦ F.map (Pi.π M.obj j)))
      (c₂ := Fan.mk (F.obj R) (fun a ↦ F.map (Pi.π _ a)))
      (F.map s) (F.map t) hs ht
      (isLimitOfHasProductOfPreservesLimit F M.obj)
      (isLimitOfHasProductOfPreservesLimit F (fun a : Σ p : J × J, p.1 ⟶ p.2 ↦ M.obj a.1.2))
      hff
    refine ⟨IsLimit.ofIsoLimit hb (Cone.ext (Iso.refl _) ?_)⟩
    intro j
    dsimp [buildLimit, ff]
    simp [← F.map_comp, k]

private theorem constantConstructibleOfIso
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
  [CompactSpace X] [QuasiSeparatedSpace X] :
    ∀ (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (M ≅ N) → IsConstantModelConstructible Λ X M → IsConstantModelConstructible Λ X N := by
  intro M N e hM
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hqc] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, ?_⟩
  intro a
  obtain ⟨c, hc⟩ := hS a
  refine ⟨c, ?_⟩
  intro i
  obtain ⟨P, hP, ⟨eP⟩⟩ := hc i
  refine ⟨P, hP, ⟨?_⟩⟩
  exact (upperStar Λ (c.f i)).mapIso
    ((upperStar Λ (S.immersion a)).mapIso e.symm) ≪≫ eP

private theorem constantSheafExtension
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (T : Scheme.FiniteLocallyClosedStratification U)
    (hT : ∀ a : Fin T.n, Topology.IsConstructible (T.stratum a))
    (hM : ∀ a : Fin T.n, HasFiniteConstantLocalModel Λ (T.domain a)
      ((upperStar Λ (T.immersion a)).obj M)) :
    IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M) := by
  exact (constantModelConstructible_openImmersionLowerShriek l (ringChar k)
    (Fact.out : ringChar k ≠ l) k Λ j M T hT hM).1

private def finiteStratification {U : Scheme.{u}} (S : Scheme.Stratification U) :
    Scheme.FiniteLocallyClosedStratification U :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }

private theorem finiteStratification_n {U : Scheme.{u}} (S : Scheme.Stratification U) :
    (finiteStratification S).n = S.n := rfl

private theorem finiteStratification_domain {U : Scheme.{u}} (S : Scheme.Stratification U)
    (a : Fin S.n) : (finiteStratification S).domain a = S.domain a := rfl

private theorem finiteStratification_immersion {U : Scheme.{u}} (S : Scheme.Stratification U)
    (a : Fin S.n) : (finiteStratification S).immersion a = S.immersion a := rfl

private theorem finiteStratification_stratum {U : Scheme.{u}} (S : Scheme.Stratification U)
    (a : Fin S.n) : (finiteStratification S).stratum a = S.stratum a := rfl

private theorem finiteStratification_constructible {U : Scheme.{u}} (S : Scheme.Stratification U) :
    ∀ a : Fin (finiteStratification S).n,
      Topology.IsConstructible ((finiteStratification S).stratum a) := S.isConstructible_stratum

private theorem localModelCongr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U V W : Scheme.{u}}
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (f : V ⟶ U) (g : W ⟶ U) (h : V = W) (hf : HEq f g) :
    HasFiniteConstantLocalModel Λ V ((upperStar Λ f).obj M) →
      HasFiniteConstantLocalModel Λ W ((upperStar Λ g).obj M) := by
  subst W
  cases hf
  exact id

private theorem finiteStratification_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U : Scheme.{u}} (S : Scheme.Stratification U)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj M)) →
    ∀ a : Fin (finiteStratification S).n,
      HasFiniteConstantLocalModel Λ ((finiteStratification S).domain a)
        ((upperStar Λ ((finiteStratification S).immersion a)).obj M) := by
  intro h a
  exact localModelCongr Λ M (S.immersion a) ((finiteStratification S).immersion a)
    (finiteStratification_domain S a).symm HEq.rfl (h a)

attribute [local irreducible] finiteStratification

private theorem constantStratifiedSheafExtension
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (S : Scheme.Stratification U)
    (hM : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj M)) :
    IsConstantModelConstructible Λ X ((openImmersionLowerShriek Λ j).obj M) := by
  exact constantSheafExtension l k Λ j M (finiteStratification S)
    (finiteStratification_constructible S) (finiteStratification_models Λ S M hM)


private theorem constantBoundedExtension
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    ∀ K, constantModelBoundedConstructible Λ U K →
      constantModelBoundedConstructible Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) := by
  classical
  intro K hK
  refine ⟨(openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro n
  apply constantConstructibleOfIso Λ X _ _
    (((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app K)
  have hM := hK.2 n
  have hqc : CompactSpace U ∧ QuasiSeparatedSpace U := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hqc] at hM
  obtain ⟨S, hS⟩ := hM
  exact constantStratifiedSheafExtension l k Λ j _ S hS


/-- Extension by zero along a quasi-compact open immersion is exact, preserves sums and
all existing small limits, commutes with uniformizer-power reduction, and preserves both
bounded constructibility and its localizing closure.

Source: blueprint main-20261015, sk-cor-int-compactness-ii-extension-zero, clauses (1)--(3);
Stacks Project, Tag 09BP (blueprint: det-cor-int-compactness-ii-extension-zero).

Proof:
1. The standing finite-type separated setting is qcqs. The existing exactness and
triangulated instances apply to the condensed-coefficient extension, and its derived
adjunction gives preservation of small sums.
2. Apply condensedOpenExtensionProducts. For any existing limit cone, the arrow into
the product of the diagram's objects is a kernel of the difference of the two maps
into the product indexed by arrows. The universal property of the original cone
proves this kernel property. The pretriangulated kernel preservation theorem carries
it through the additive functor; product preservation and buildIsLimit then give the
mapped cone's universal property. No existence of arbitrary equalizers is assumed.
3. Apply integralOpenExtensionReduction. Its proof specializes the locally closed
projection formula to the open immersion followed by the identity, then identifies
the pulled-back degree-zero quotient using coefficient pullback composition.
4. Exactness preserves boundedness and identifies cohomology with the extension of
cohomology. Retain each constructible sheaf's finite stratification and constant
local models, apply constantModelConstructible_openImmersionLowerShriek, and transport
along this cohomology isomorphism.
5. The inverse image of Loc(Dbc(X)) under the derived extension is triangulated,
replete, and closed under sums. Step 4 sends its generators into Loc(Dbc(X)); the
minimality property in localizingClosure_exists gives the final assertion. -/
theorem integralExtensionByZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))] :
    (openImmersionLowerShriek (integralCoefficientRing l E) j).PreservesHomology ∧
    Functor.IsTriangulated
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory) ∧
    PreservesLimitsOfSize.{u + 1, u + 1}
      (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ∧
    (∀ n : ℕ, Nonempty
      ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory ⋙
          integralReductionFunctor l E X n ≅
        integralReductionFunctor l E U n ⋙
          (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory)) ∧
    (∀ K : integralDerived l E U,
      constantModelBoundedConstructible (integralCoefficientRing l E) U K →
      constantModelBoundedConstructible (integralCoefficientRing l E) X
        ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory.obj K)) ∧
    (∀ K : integralDerived l E U,
      localizingClosure (constantModelBoundedConstructible (integralCoefficientRing l E) U) K →
      localizingClosure (constantModelBoundedConstructible (integralCoefficientRing l E) X)
        ((openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory.obj
          K)) := by
  classical
  let F := (openImmersionLowerShriek (integralCoefficientRing l E) j).mapDerivedCategory
  let Λ := integralCoefficientRing l E
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  let : QuasiSeparatedSpace U :=
    quasiSeparatedSpace_of_quasiSeparated (U ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have hbc := constantBoundedExtension l k Λ j
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, hbc, ?_⟩
  · intro I
    infer_instance
  · have hp := condensedOpenExtensionProducts Λ j
    let := hp.1
    let (I : Type (u + 1)) := hp.2 I
    exact preservesLimitsFromProducts F
  · exact integralOpenExtensionReduction l E k j
  · intro K hK
    let P := localizingClosure (constantModelBoundedConstructible (integralCoefficientRing l E) X)
    have hP := (localizingClosure_exists (integralCoefficientRing l E) X
      (constantModelBoundedConstructible (integralCoefficientRing l E) X)).2.2.2.1
    let := hP.1
    let := hP.2.1
    apply hK (P.inverseImage F)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hmem
      let := hD
      let : HasColimit (D ⋙ F) := inferInstance
      have h := hP.2.2 (D ⋙ F) inferInstance hmem
      exact P.prop_of_iso (preservesColimitIso F D).symm h
    · intro L hL
      exact (localizingClosure_exists (integralCoefficientRing l E) X
        (constantModelBoundedConstructible (integralCoefficientRing l E) X)).2.2.2.2.1
          _ (hbc L hL)

end AlgebraicGeometry.ProEtale.CondensedRing
