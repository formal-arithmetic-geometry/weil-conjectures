/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Forgetting scalars and derived restriction kernels

Source: Stacks Project, sites-cohomology.tex, Tags 093X and 03FD; injectives.tex,
Tag 01DU; derived.tex, Tags 013K, 070J, 070I, 05TI and 05TH; homology.tex, Tags 0117
and 05QB (blueprint: lem-pur-module-restriction-kernel-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w uB vB uD vD
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ModuleRestrictionKernel

open ConstantLeftModuleInverseImage LeftModuleDerivedEvaluation

/-- The actual kernel of module restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [Ring A] [HasWeakSheafify J RingCat.{u}]
    {W T : C} (m : W ⟶ T) : ConstantLeftModuleInverseImage.Modules J A ⥤ ModuleCat.{u} A := by
  let r := LeftModuleDerivedEvaluation.restriction J A m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G J A T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

/-- The actual kernel of abelian restriction, with the induced action on morphisms.
Source: Stacks, 093X and the restriction-kernel refinement of 03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def S₀
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {W T : C} (m : W ⟶ T) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} := by
  let r := LeftModuleDerivedEvaluation.restriction₀ J m
  exact {
    obj := fun M => kernel (r.app M)
    map := fun {M N} f => kernel.lift (r.app N)
      (kernel.ι (r.app M) ≫ (LeftModuleDerivedEvaluation.G₀ J T).map f) (by
        rw [Category.assoc, r.naturality f]
        rw [← Category.assoc, kernel.condition, zero_comp])
    map_id := by
      intro M
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp
    map_comp := by
      intro M N P f g
      apply (cancel_mono (kernel.ι _)).1
      rw [kernel.lift_ι]
      simp [Category.assoc]
  }

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] [HasWeakSheafify J RingCat.{u}]
  {W T : C} (m : W ⟶ T)

/-- Additivity of module restriction kernels.
Source: Stacks, 03DA and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation and restriction are additive; the induced kernel maps preserve
addition because their composites with the monic kernel inclusion do. -/
theorem sAdditiveProof : (S J A m).Additive := by
  sorry

/-- Additivity of the actual module restriction-kernel functor.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance sAdditive : (S J A m).Additive :=
  sAdditiveProof J A m

/-- Additivity of abelian restriction kernels.
Source: Stacks, 01FT and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation is additive. Composing the induced maps with the monic kernel
inclusion reduces addition to sectionwise addition. -/
theorem s₀AdditiveProof : (S₀ J m).Additive := by
  sorry

/-- Additivity of the actual abelian restriction-kernel functor.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance s₀Additive : (S₀ J m).Additive :=
  s₀AdditiveProof J m

/-- Left exactness of module restriction kernels.
Source: Stacks, 03DA and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: evaluation preserves finite limits. Kernels commute with finite limits,
so taking the kernel of the restriction natural transformation does also. -/
theorem sLeftExact : PreservesFiniteLimits (S J A m) := by
  sorry

/-- Left exactness of abelian restriction kernels.
Source: Stacks, 01FT and 093X
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: finite limits of sheaves are sectionwise; taking a kernel commutes with
finite limits. Therefore the restriction-kernel functor preserves them. -/
theorem s₀LeftExact : PreservesFiniteLimits (S₀ J m) := by
  sorry

/-- The canonical scalar-forgetting kernel isomorphism on each object.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentityObj (M : Modules J A) :
    (v A).obj ((S J A m).obj M) ≅ (S₀ J m).obj ((V J A).obj M) :=
  PreservesKernel.iso (v A) ((restriction J A m).app M)

/-- Naturality of the kernel-preservation comparison.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: compose both maps with the monic target kernel inclusion. Both composites
are the underlying section map followed by the source inclusion; kernel
uniqueness gives the equation. -/
theorem kernelIdentity_naturality {M N : Modules J A} (f : M ⟶ N) :
    (S J A m ⋙ v A).map f ≫ (kernelIdentityObj J A m N).hom =
      (kernelIdentityObj J A m M).hom ≫ (V J A ⋙ S₀ J m).map f := by
  sorry

/-- The underived identity, expressed by canonical kernel preservation rather than
an equality between chosen categorical limit objects.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelIdentity : S J A m ⋙ v A ≅ V J A ⋙ S₀ J m :=
  NatIso.ofComponents (kernelIdentityObj J A m) (kernelIdentity_naturality J A m)

/-- Enough injectives for constant module sheaves on the small site.
Source: Stacks, Injectives, 01DU
(blueprint: lem-pur-module-restriction-kernel-comparison).
Proof: module sheaves form a Grothendieck abelian category. The functorial
injective embedding theorem embeds every object monomorphically into an
injective object. The abelian structure is Mathlib's sectionwise-kernel,
sheafified-cokernel structure on `SheafOfModules`. -/
theorem moduleEnoughInjectivesProof : EnoughInjectives (Modules J A) := by
  sorry

/-- Enough injectives, installed from the separately named existence theorem.
Source: Stacks, 03DA/093X/01DU
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
instance moduleEnoughInjectives : EnoughInjectives (Modules J A) :=
  moduleEnoughInjectivesProof J A

variable [HasDerivedCategory.{w} (Modules J A)]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- The canonical derived comparison induced by the identity on restriction kernels.
Source: Stacks, 03FD/05TI/05TH, restriction-kernel refinement
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def comparison :
    (S J A m).rightDerivedFunctorPlus ⋙ (v A).mapDerivedCategoryPlus ⟶
      (V J A).mapDerivedCategoryPlus ⋙ (S₀ J m).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (kernelIdentity J A m).hom

/-- A restriction-kernel row, with its specified kernel inclusion.
Source: Stacks, 093X (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def row (M : Sheaf J AddCommGrpCat.{u}) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (kernel.ι ((restriction₀ J m).app M))
    ((restriction₀ J m).app M) (kernel.condition _)

/-- The unit computation on a bounded-below complex, with no chosen resolution.
Source: Stacks, 05TI/05TH
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
abbrev compute {B : Type uB} {D : Type uD} [Category.{vB} B] [Category.{vD} D]
    [Abelian B] [Abelian D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D] [EnoughInjectives B]
    (F : B ⥤ D) [F.Additive] (L : CochainComplex.Plus B) :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) ⟶
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L) :=
  F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj L)

/-- The underived kernel identity applied to every term of a bounded-below complex.
Source: Stacks, 03DA/03FD
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelComplexIdentity (L : CochainComplex.Plus (Modules J A)) :
    (v A).mapCochainComplexPlus.obj ((S J A m).mapCochainComplexPlus.obj L) ≅
      (S₀ J m).mapCochainComplexPlus.obj ((V J A).mapCochainComplexPlus.obj L) :=
  (CochainComplex.Plus.ι AddCommGrpCat.{u}).preimageIso
    ((NatIso.mapHomologicalComplex (kernelIdentity J A m) (.up ℤ)).app L.obj)

/-- The computation map for the scalar-forgotten module kernel complex.
Source: Stacks, 05TI/05TH, using the exact scalar-forgetting localization factor
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def forgetCompute (F : Modules J A ⥤ ModuleCat.{u} A) [F.Additive]
    (L : CochainComplex.Plus (Modules J A)) :
    DerivedCategory.Plus.Q.obj
        ((v A).mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj L)) ⟶
      (v A).mapDerivedCategoryPlus.obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) :=
  (v A).mapDerivedCategoryPlusFactorsh.inv.app
      (F.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (Modules J A)).obj L)) ≫
    (v A).mapDerivedCategoryPlus.map (compute F L)

/-- The chain map on actual scalar-forgotten module kernel complexes induced by `q`.
Source: Stacks, 093X/03FD and homology 0117
(blueprint: lem-pur-module-restriction-kernel-comparison). -/
def kernelMap (L : CochainComplex.Plus (Modules J A))
    (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (q : (V J A).mapCochainComplexPlus.obj L ⟶ N) :
    (v A).mapCochainComplexPlus.obj ((S J A m).mapCochainComplexPlus.obj L) ⟶
      (S₀ J m).mapCochainComplexPlus.obj N :=
  (kernelComplexIdentity J A m L).hom ≫ (S₀ J m).mapCochainComplexPlus.map q

/-- The identity on underlying evaluated complexes.
Source: Stacks, 03FD (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def evaluationComplexIdentity (U : C) (L : CochainComplex.Plus (Modules J A)) :
    (v A).mapCochainComplexPlus.obj ((G J A U).mapCochainComplexPlus.obj L) ≅
      (G₀ J U).mapCochainComplexPlus.obj ((V J A).mapCochainComplexPlus.obj L) :=
  (CochainComplex.Plus.ι AddCommGrpCat.{u}).preimageIso
    ((NatIso.mapHomologicalComplex (evaluationIdentity J A U) (.up ℤ)).app L.obj)

/-- The evaluation of the specified comparison map, retaining scalar forgetting.
Source: Stacks, 03FD (blueprint: lem-pur-module-restriction-kernel-comparison). -/
def evaluationMap (U : C) (L : CochainComplex.Plus (Modules J A))
    (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
    (q : (V J A).mapCochainComplexPlus.obj L ⟶ N) :
    (v A).mapCochainComplexPlus.obj ((G J A U).mapCochainComplexPlus.obj L) ⟶
      (G₀ J U).mapCochainComplexPlus.obj N :=
  (evaluationComplexIdentity J A U L).hom ≫ (G₀ J U).mapCochainComplexPlus.map q

/-- Forgetting constant module scalars compares the derived restriction kernels,
including all representative normalizations.

Source: Stacks, sites-cohomology.tex, 093X and 03FD, and injectives.tex, 01DU;
agent-formulated restriction-kernel refinement of the ordinary evaluation comparison
(blueprint: lem-pur-module-restriction-kernel-comparison).

Proof:
1. Module sheaves are abelian and Grothendieck, hence have enough injectives.
Evaluation and the two kernel functors are additive and left exact. Forgetting
scalars is exact and preserves the kernels, giving `kernelIdentity`.
2. Apply 093X to an injective module sheaf and to an injective abelian sheaf viewed
as a sheaf of integer modules. Their restriction maps are surjective, so their
restriction-kernel rows are short exact. This does not make the underlying
abelian sheaf of an injective module sheaf injective.
3. The ordinary evaluation comparison 03FD shows that the underlying abelian
sheaf of a module-injective is acyclic for evaluation at T and W.
4. Resolve that abelian sheaf by injectives. The degreewise short exact kernel
sequence gives a long exact cohomology sequence. Evaluation acyclicity kills
all positive degrees except possibly degree one; surjectivity in step 2 kills
that degree as well. Thus it is acyclic for the abelian kernel functor.
5. Bounded-below injective representatives L and N compute the two derived
kernel functors via their right-derived units (05TI/05TH). Maps into the
abelian K-injective representative N realize the chosen derived identification
by a quasi-isomorphism q (070I).
6. Naturality of q gives a morphism of the short exact restriction-kernel rows.
The two evaluated maps are quasi-isomorphisms by 03FD.
7. Apply the natural long exact sequence to the row morphism. In the five-term
window around each kernel cohomology group the other four maps are isomorphisms.
The five lemma makes the kernel map a quasi-isomorphism in every integer degree.
8. Naturality of the right-derived unit identifies this kernel map with the
canonical `comparison`. Maps between injective representatives are unique up
to homotopy; additive functors preserve homotopies. This proves independence
of all representatives and naturality in K. The same unit argument identifies
the two evaluations with the recorded ordinary comparisons. Degree zero is
the identity on actual kernels, expressed by kernel preservation when categorical
limits have been chosen. No flatness over the integers is used. -/
theorem moduleRestrictionKernelComparison [Mono m] :
    (∀ (I : Modules J A), Injective I →
      Function.Surjective ((restriction J A m).app I)) ∧
    (∀ (I : Modules J A), Injective I → ∀ q : ℕ, 0 < q →
      IsZero (((S₀ J m).rightDerived q).obj ((V J A).obj I))) ∧
    IsIso (comparison J A m) ∧
    (Functor.whiskerRight (S J A m).toRightDerivedZero (v A) ≫
        Functor.rightDerivedBaseChange (kernelIdentity J A m).hom 0 =
      (kernelIdentity J A m).hom ≫
        Functor.whiskerLeft (V J A) (S₀ J m).toRightDerivedZero) ∧
    (∀ (K : DerivedCategory.Plus (Modules J A))
      (L : CochainComplex.Plus (Modules J A))
      (N : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}))
      (_hL : ∀ i : ℤ, Injective (L.obj.X i))
      (_hN : ∀ i : ℤ, Injective (N.obj.X i))
      (eL : DerivedCategory.Plus.Q.obj L ≅ K)
      (eN : DerivedCategory.Plus.Q.obj N ≅ (V J A).mapDerivedCategoryPlus.obj K)
      (q : (V J A).mapCochainComplexPlus.obj L ⟶ N)
      (_hq : QuasiIso q.hom)
      (_he : (V J A).mapDerivedCategoryPlus.map eL.hom ≫ eN.inv =
        (V J A).mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient (Modules J A)).obj L) ≫
          DerivedCategory.Plus.Q.map q),
      (∀ i : ℤ,
        (row J m ((V J A).obj (L.obj.X i))).ShortExact ∧
        (row J m (N.obj.X i)).ShortExact ∧
        (S₀ J m).map (q.hom.f i) ≫ (row J m (N.obj.X i)).f =
          (row J m ((V J A).obj (L.obj.X i))).f ≫ (G₀ J T).map (q.hom.f i) ∧
        (G₀ J T).map (q.hom.f i) ≫ (row J m (N.obj.X i)).g =
          (row J m ((V J A).obj (L.obj.X i))).g ≫ (G₀ J W).map (q.hom.f i)) ∧
      QuasiIso (kernelMap J A m L N q).hom ∧
      QuasiIso (evaluationMap J A T L N q).hom ∧
      QuasiIso (evaluationMap J A W L N q).hom ∧
      (forgetCompute J A (S J A m) L ≫
          (v A).mapDerivedCategoryPlus.map ((S J A m).rightDerivedFunctorPlus.map eL.hom) ≫
          (comparison J A m).app K =
        DerivedCategory.Plus.Q.map (kernelMap J A m L N q) ≫ compute (S₀ J m) N ≫
          (S₀ J m).rightDerivedFunctorPlus.map eN.hom) ∧
      (∀ U : C, U = T ∨ U = W →
        forgetCompute J A (G J A U) L ≫
            (v A).mapDerivedCategoryPlus.map ((G J A U).rightDerivedFunctorPlus.map eL.hom) ≫
            (LeftModuleDerivedEvaluation.comparison J A U).app K =
          DerivedCategory.Plus.Q.map (evaluationMap J A U L N q) ≫ compute (G₀ J U) N ≫
            (G₀ J U).rightDerivedFunctorPlus.map eN.hom)) := by
  sorry

end CategoryTheory.ModuleRestrictionKernel
