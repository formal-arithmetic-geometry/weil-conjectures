/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
public import Sheaf.Paper.ProEtaleConstantModuleEncoding
public import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.ProEtaleConstantModulePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Intrinsic finite-coefficient derived pullback

Source: Bhatt--Scholze, Lemmas 6.5.8(2), 6.5.9(5), finite discrete specialization,
and the intrinsic stratification argument isolated from Lemma 6.7.11;
Stacks Project, Tags 04JC, 015F, 010N, 054I, 03D8, 093R and 05V1
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

These are ordinary uncompleted derived categories of constant-ring module sheaves.
The pullback uses the existing tensor extension along the canonical constant-section map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The specified constant-coefficient module pullback is additive and exact.
Source: Bhatt--Scholze, Lemma 6.5.9(5), finite discrete case; Stacks Tag 04JC
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 1): lem-pur-proetale-constant-coefficient-comparison identifies the
canonical constant-section coefficient map with an isomorphism. The fixed-ring
inverse image of lem-pe-constant-left-module-inverse-image is exact. Identify its
transported action with the tensor pullback by n tensor a mapping to a n, with
inverse n mapping to n tensor 1. Both actions agree on constant scalars and extend
by sheafification. This gives additivity and preservation of finite limits and colimits. -/
theorem intrinsicFiniteModulePullback_exact {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A] :
    (proEtaleConstantModulePullbackFunctor h A).Additive ∧
      PreservesFiniteLimits (proEtaleConstantModulePullbackFunctor h A) ∧
      PreservesFiniteColimits (proEtaleConstantModulePullbackFunctor h A) := by
  sorry

/-- Termwise pullback descends to the ordinary unbounded derived category and
commutes naturally with every cohomology functor.
Source: Stacks Tags 015F and 010N; Bhatt--Scholze, Lemma 6.5.9(5), finite discrete case
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 2): apply lem-weil-pbc-exact-functor-derived-factorization to the
exact pullback. It preserves quasi-isomorphisms, so localization gives the displayed
factorization. The unbounded cohomology comparison in
lem-weil-pbc-exact-functor-bounded-below gives the natural isomorphism for every
integer q; the assertion does not require a bounded-below input. -/
theorem intrinsicFiniteModulePullback_derived {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A] :
    Nonempty (DerivedCategory.Q ⋙
      (proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory ≅
        (proEtaleConstantModulePullbackFunctor h A).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    ∀ q : ℤ, Nonempty
      ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) q ≅
        DerivedCategory.homologyFunctor
            (proEtaleRingModules Y (proEtaleConstantRing Y A)) q ⋙
          proEtaleConstantModulePullbackFunctor h A) := by
  sorry

/-- Every given intrinsic witnessing stratification pulls back to a witnessing
stratification, with the same finite models on the actual base-changed covering.
The strata and their immersion maps are exactly `s.pullback h`, defined by fibre
products. Its number of strata is `s.n`, so it stays positive even when X is empty.
Source: Stacks Tags 054I, 03D8, 093R and 05V1; Bhatt--Scholze, Lemma 6.5.8(2)
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node steps 3--7): lemma-constructible-pullback-stratification constructs
s.pullback h using the actual fibre products and projection immersions.
lem-pur-scheme-constructible-preimage makes its strata constructible; preimages
preserve their disjointness and covering union. Retain all strata, including empty
ones, so the positive index remains available when X is empty. Composition of the
canonical coefficient pullbacks (lem-pur-proetale-constant-module-pullback-composition)
and the Cartesian equation give the displayed restriction isomorphism. Base change
preserves weakly etale arrows and fpqc coverings
(lem-weil-pbc-weakly-etale-composition-base-change and
lem-galois-fpqc-covering-base-change). Localize this inverse image using
lem-weil-pbc-localize-ringed-site-morphism and
lem-weil-proetale-weakly-etale-localization. Pullback of each constant model is the
same model by lem-sfb-geometric-inverse-image-constant-module. Finally
lem-pur-proetale-inverse-image-stalk identifies the new stalk with the old one;
naturality for multiplication by every constant scalar makes that identification
linear. Finite stalks over a finite field are finite-dimensional. On an empty
scheme the empty-cover sheaf condition makes every module sheaf zero; the retained
empty strata therefore have the constant zero module as a local model. -/
theorem intrinsicFiniteModulePullback_stratification {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (s : Stratification Y) (_hn : 0 < s.n)
    (_hs : ∀ i : Fin s.n,
      IsLocallyConstantProEtaleModuleSheaf (s.domain i) A
          (proEtaleConstantModulePullback (s.immersion i) A F) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ s.domain i),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (s.domain i) A)
            (proEtaleConstantModulePullback (s.immersion i) A F))) :
    ∀ i : Fin s.n,
      IsLocallyConstantProEtaleModuleSheaf ((s.pullback h).domain i) A
          (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (x : Spec (.of Ω) ⟶ (s.pullback h).domain i),
        Finite (proEtaleGeometricModuleStalk x
          (proEtaleConstantRing ((s.pullback h).domain i) A)
          (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F))) ∧
        Module.Finite (ULift.{u + 1, u} A)
          (proEtaleGeometricFixedModuleStalk x (ULift.{u + 1, u} A)
            ((proEtaleModuleRestriction ((s.pullback h).domain i) A).obj
              (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
                (proEtaleConstantModulePullback h A F))))) ∧
      Nonempty
        (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F) ≅
          proEtaleConstantModulePullback (pullback.fst (s.immersion i) h) A
            (proEtaleConstantModulePullback (s.immersion i) A F)) ∧
      ∀ (I : Type (u + 1)) (U : I → (s.domain i).ProEt)
        (a : ∀ j : I, U j ⟶ ProEt.mk (𝟙 (s.domain i))),
        Presieve.ofArrows U a ∈ (ProEt.precoverage (s.domain i)).coverings _ →
        ∀ M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          (∀ j : I, Finite (M j)) →
          (∀ j : I, Nonempty
            ((proEtaleConstantModulePullback (s.immersion i) A F).over (U j) ≅
              proEtaleConstantModuleSheafOver (s.domain i) A (U j) (M j))) →
          ∃ b : ∀ j : I,
              (proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j) ⟶
                ProEt.mk (𝟙 ((s.pullback h).domain i)),
            Presieve.ofArrows
                (fun j : I ↦
                  (proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) b ∈
              (ProEt.precoverage ((s.pullback h).domain i)).coverings _ ∧
            ∀ j : I, Nonempty
              ((proEtaleConstantModulePullback ((s.pullback h).immersion i) A
                  (proEtaleConstantModulePullback h A F)).over
                    ((proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) ≅
                proEtaleConstantModuleSheafOver ((s.pullback h).domain i) A
                  ((proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) (M j)) := by
  sorry

/-- Intrinsic constructibility is preserved for every scheme morphism.
Source: Bhatt--Scholze, Lemmas 6.5.8(2) and 6.5.9(5), finite discrete specialization
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node steps 3--7): unpack the positive finite witnessing stratification,
base-change its strata and local trivializing covers, and use the restriction
composition isomorphism and the same constant module models as above. Stalk
comparison preserves their finiteness. The number of strata remains positive,
including for the empty scheme, whose module sheaf is zero. These data satisfy
exactly def-weil-proetale-constructible-sheaf. -/
theorem intrinsicFiniteModulePullback_constructible {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (_hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf X A (proEtaleConstantModulePullback h A F) := by
  sorry

/-- Ordinary derived pullback preserves bounded intrinsic constructibility with
any specified cohomological vanishing interval unchanged.
Source: Bhatt--Scholze, Lemma 6.5.9(5), R = A and m = 0; Stacks Tag 015F
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 8): use the natural cohomology isomorphism of step 2. The pullback
of each constructible cohomology sheaf is constructible by steps 3--7. Outside
[a,b] its source is zero, so exact additive pullback is zero too. Thus the same
interval works. The earlier arguments use arbitrary scheme maps and ordinary
constant-ring modules; no characteristic restriction, cohomological-dimension
bound or Noetherian hypothesis occurs. -/
theorem intrinsicFiniteDerivedPullback_bounded_constructible
    {X Y : Scheme.{u}} (h : X ⟶ Y) (A : Type u) [Field A] [Finite A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) (_hab : a ≤ b)
    (_hvanish : ∀ q : ℤ, (q < a ∨ b < q) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) q).obj K))
    (_hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf Y A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) q).obj K)) :
    (∀ q : ℤ, (q < a ∨ b < q) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory.obj K))) ∧
    ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
