/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Adjoint chain maps on restriction kernels: maps and homotopies

Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67; Stacks Project, Derived Categories, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence).
-/

@[expose] public section

noncomputable section

universe u v u' v' w w' w₀ wQ wQc wQd

open CategoryTheory CategoryTheory.Limits CategoryTheory.ShortComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable (Jc : GrothendieckTopology C) (Jd : GrothendieckTopology D)
variable [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]

/-- A monomorphic pair of objects in a site. Source: Milne, Section 9, Theorem 9.4
(blueprint: lem-pur-support-pair-chain-coherence). -/
structure SupportPair where
  /-- The subobject on which sections are restricted. -/
  V : C
  /-- the ambient object -/
  T : C
  /-- The inclusion of the restriction subobject. -/
  m : V ⟶ T
  /-- the inclusion is a monomorphism -/
  mono_m : Mono m

attribute [instance] SupportPair.mono_m

/-- The section functor of sheaves of abelian groups at an object of a site.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def sectionFunctor (J : GrothendieckTopology C) (X : C) :
    Sheaf J AddCommGrpCat.{w₀} ⥤ AddCommGrpCat.{w₀} :=
  (sheafSections J AddCommGrpCat.{w₀}).obj (Opposite.op X)

/-- Evaluation preserves zero maps. Source: Milne, Section 9, Theorem 9.4
(blueprint: lem-pur-support-pair-chain-coherence). -/
instance sectionFunctorPreservesZeroMorphisms (J : GrothendieckTopology C) (X : C) :
    (sectionFunctor J X).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- The restriction map of sections along a morphism of site objects.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def sectionRestriction (J : GrothendieckTopology C) {V T : C} (m : V ⟶ T) :
    sectionFunctor J T ⟶ sectionFunctor J V :=
  (sheafSections J AddCommGrpCat.{w₀}).map m.op

/-- The restriction-kernel complex of a sheaf complex for a pair.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportKernel (J : GrothendieckTopology C) (P : SupportPair (C := C))
    (I : HomologicalComplex (Sheaf J AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)) :
    HomologicalComplex AddCommGrpCat.{w₀} (ComplexShape.up ℤ) :=
  kernel ((NatTrans.mapHomologicalComplex
    (sectionRestriction J P.m) (ComplexShape.up ℤ)).app I)

/-- The three-term restriction diagram associated to a pair and a sheaf complex.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportDiagram (J : GrothendieckTopology C) (P : SupportPair (C := C))
    (I : HomologicalComplex (Sheaf J AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)) :
    ShortComplex (HomologicalComplex AddCommGrpCat.{w₀} (ComplexShape.up ℤ)) :=
  { f := kernel.ι ((NatTrans.mapHomologicalComplex
      (sectionRestriction J P.m) (ComplexShape.up ℤ)).app I)
    g := (NatTrans.mapHomologicalComplex (sectionRestriction J P.m)
      (ComplexShape.up ℤ)).app I
    zero := by simp }

/-- A complex is bounded below when it vanishes in all sufficiently negative degrees.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def BoundedBelow {A : Type w} [Category.{w'} A] [HasZeroMorphisms A] (I :
    HomologicalComplex A (ComplexShape.up ℤ)) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n → IsZero (I.X i)

/-- The degreewise adjoint of a chain map under an adjunction.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def degreewiseAdjoint {A : Type w} {B : Type w'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [L.Additive]
    {I : HomologicalComplex A (ComplexShape.up ℤ)}
    {J : HomologicalComplex B (ComplexShape.up ℤ)}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) (n : ℤ) :
    I.X n ⟶ R.obj (J.X n) :=
  (adj.homEquiv (I.X n) (J.X n)) (h.f n)

/-- The component equations characterizing the map induced by an adjoint chain map.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportPairMapCondition
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    {I : HomologicalComplex (Sheaf Jc AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)}
    {K : HomologicalComplex (Sheaf Jd AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K) : Prop :=
  (∀ n : ℤ, φ.τ₂.f n =
    (sectionFunctor Jc P.T).map (degreewiseAdjoint L
      (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) adj h n) ≫
      (sectionRestriction Jd t).app (K.X n)) ∧
  (∀ n : ℤ, φ.τ₃.f n =
    (sectionFunctor Jc P.V).map (degreewiseAdjoint L
      (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) adj h n) ≫
      (sectionRestriction Jd s).app (K.X n))

/-- The standard derived localization used for the representative clause.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def standardDerivedQ {A : Type w} [Category.{w'} A] [Abelian A]
    [HasDerivedCategory.{wQ} A] : CochainComplex A ℤ ⥤ DerivedCategory A :=
  DerivedCategory.Q

/-- The ordinary diagram map induced by a map of sheaf complexes, specified by its
section components. Source: Milne, Section 9, Theorem 9.4, pair functoriality
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportOrdinaryMapCondition (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ} (g : I ⟶ K)
    (α : supportDiagram J P I ⟶ supportDiagram J P K) : Prop :=
  α.τ₂ = ((sectionFunctor J P.T).mapHomologicalComplex (ComplexShape.up ℤ)).map g ∧
  α.τ₃ = ((sectionFunctor J P.V).mapHomologicalComplex (ComplexShape.up ℤ)).map g

/-- Equality on each of the three cohomology groups, in every integer degree.
Source: Milne, Section 9, Theorem 9.4, and the node's Step 5
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportCohomologyEqual
    {S T : ShortComplex (CochainComplex AddCommGrpCat.{w₀} ℤ)} (φ ψ : S ⟶ T) : Prop :=
  ∀ n : ℤ,
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₁ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₁ ∧
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₂ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₂ ∧
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₃ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₃

/-- The three component maps give identifications on cohomology in every degree.
Source: Milne, Section 9, Theorem 9.4, and the node's Step 5
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportCohomologyIsIso
    {S T : ShortComplex (CochainComplex AddCommGrpCat.{w₀} ℤ)} (φ : S ⟶ T) : Prop :=
  ∀ n : ℤ,
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₁) ∧
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₂) ∧
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₃)

/--
Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67, pair functoriality; Stacks Project, Derived Categories, Tag 070I.
(blueprint: lem-pur-support-pair-chain-coherence)

Step 1. Take the degreewise adjoint of `h`. Naturality in both sheaf variables
makes it a chain map. Since the right adjoint is the actual precomposition
functor, its evaluations commute with restriction; use `square` to obtain
commuting T- and V-component chain maps.
Step 2. The universal property of the kernel supplies the unique first
component, giving the unique diagram map with those section components.
Step 3. Adjoin each component of the degree -1 homotopy `z`, evaluate, and
restrict along `t,s`. Naturality makes these degree -1 maps compatible with
restriction, so they restrict to the kernel. The homotopy equation passes
through the adjunction, giving the three cochain homotopies below, compatible
with inclusion and restriction. They induce equal maps on all cohomology groups.
Step 4. Bounded-below injective complexes are K-injective by
`CochainComplex.isKInjective_of_injective`. The K-injective comparison
`CochainComplex.IsKInjective.Qh_map_bijective` supplies representatives of every
derived morphism and homotopies between any two representatives of the same one.
Step 5. The adjoint of the composite `L.map g ≫ h ≫ g'`
is `R(g')` composed with the adjoint of `h` and with `g`. Thus the diagram map
of `L.map g ≫ h ≫ g'` is the composite of the ordinary diagram maps and the
map of `h`. A derived isomorphism between bounded-below injective complexes
has a chain representative and a homotopy inverse by the same K-injective
comparison. Evaluation and the kernel construction preserve these homotopies.
Consequently the ordinary diagram maps of `g,g'` induce the canonical
cohomology identifications. Step 3 makes them independent of the representatives
of the given derived identifications. The last equality says exactly that
transport by those identifications preserves the maps induced by `a`.
-/
theorem supportPairChainCoherence
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{wQc} (Sheaf Jc AddCommGrpCat.{w₀})]
    [HasDerivedCategory.{wQd} (Sheaf Jd AddCommGrpCat.{w₀})]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t) :
    ∀ (I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
      (K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ),
      (∀ h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K,
        (∃! φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K,
          supportPairMapCondition Jc Jd u L adj P P' t s h φ) ∧
        (∀ (h' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
            (z : _root_.Homotopy h h'),
          ∃ (φ φ' : supportDiagram Jc P I ⟶ supportDiagram Jd P' K),
            supportPairMapCondition Jc Jd u L adj P P' t s h φ ∧
            supportPairMapCondition Jc Jd u L adj P P' t s h' φ' ∧
            ∃ (H₁ : _root_.Homotopy φ.τ₁ φ'.τ₁)
              (H₂ : _root_.Homotopy φ.τ₂ φ'.τ₂)
              (H₃ : _root_.Homotopy φ.τ₃ φ'.τ₃),
              ∀ i j : ℤ,
                H₁.hom i j ≫ (supportDiagram Jd P' K).f.f j =
                  (supportDiagram Jc P I).f.f i ≫ H₂.hom i j ∧
                H₂.hom i j ≫ (supportDiagram Jd P' K).g.f j =
                  (supportDiagram Jc P I).g.f i ≫ H₃.hom i j ∧
                H₂.hom i j = (sectionFunctor Jc P.T).map
                  ((adj.homEquiv (I.X i) (K.X j)) (z.hom i j)) ≫
                    (sectionRestriction Jd t).app (K.X j) ∧
                H₃.hom i j = (sectionFunctor Jc P.V).map
                  ((adj.homEquiv (I.X i) (K.X j)) (z.hom i j)) ≫
                    (sectionRestriction Jd s).app (K.X j))) ∧
      (∀ (hI : BoundedBelow I) (hK : BoundedBelow K)
          (hinjI : ∀ n : ℤ, Injective (I.X n))
          (hinjK : ∀ n : ℤ, Injective (K.X n)),
        (∀ a : (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj
              ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj K,
          ∃ h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K,
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h = a) ∧
        (∀ (h₁ h₂ : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K),
          (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h₁ =
              (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h₂ →
            Nonempty (_root_.Homotopy h₁ h₂) ∧
            ∀ (φ ψ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K),
              supportPairMapCondition Jc Jd u L adj P P' t s h₁ φ →
              supportPairMapCondition Jc Jd u L adj P P' t s h₂ ψ →
              supportCohomologyEqual φ ψ) ∧
        (∀ (I' : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
            (K' : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ)
            (hI' : BoundedBelow I') (hK' : BoundedBelow K')
            (hinjI' : ∀ n : ℤ, Injective (I'.X n))
            (hinjK' : ∀ n : ℤ, Injective (K'.X n))
            (g : I' ⟶ I) (g' : K ⟶ K'),
          IsIso ((standardDerivedQ (A := Sheaf Jc AddCommGrpCat.{w₀})).map g) →
          IsIso ((standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map g') →
          ∀ (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
            (h' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I' ⟶ K'),
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h' =
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map
                  ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h ≫
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map g' →
            ∀ (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
              (ψ : supportDiagram Jc P I' ⟶ supportDiagram Jd P' K'),
              supportPairMapCondition Jc Jd u L adj P P' t s h φ →
              supportPairMapCondition Jc Jd u L adj P P' t s h' ψ →
              ∃ (α : supportDiagram Jc P I' ⟶ supportDiagram Jc P I)
                (β : supportDiagram Jd P' K ⟶ supportDiagram Jd P' K'),
                supportOrdinaryMapCondition Jc P g α ∧
                supportOrdinaryMapCondition Jd P' g' β ∧
                supportCohomologyIsIso α ∧ supportCohomologyIsIso β ∧
                supportCohomologyEqual (α ≫ φ ≫ β) ψ)) := by
  sorry

end CategoryTheory
