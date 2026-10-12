/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.HomologySequence
public import Sheaf.CategoryTheory.DeltaFunctor
import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift
import Sheaf.CategoryTheory.Abelian.HorseshoeResolutions

/-!
# Horseshoe connecting morphisms for right derived functors

Source: Weibel, *An Introduction to Homological Algebra*, Theorem 2.4.6 and
Lemma 2.2.8; Stacks Project, Derived Categories, Tags 013T and 0117
(blueprint: lem-weil-pbc-horseshoe-delta-functor).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The connecting morphisms obtained from every compatible (horseshoe) injective
resolution make the right derived functors into a cohomological delta-functor.
The comparison equation identifies `G.delta` with the snake-lemma boundary for every
horseshoe, transported by `isoRightDerivedObj`. The `eqToHom` maps only identify the
objects of `G.F` with the objects of `v.rightDerived` using `hF`. Thus `G.naturality`
gives naturality for any two horseshoes, and the identity ladder gives independence.

Source: Weibel, Theorem 2.4.6 with Lemma 2.2.8; Stacks Project, Derived Categories,
Tag 013T and Homology, Tags 0117 and 010Q.
(blueprint: lem-weil-pbc-horseshoe-delta-functor)

Proof:
1. Choose injective resolutions and lifts of two maps. Their sum lifts the sum of the
maps. Additivity of `v` and homology, with the comparison rule of
lem-weil-pbc-derived-functor-map-via-lift, gives additivity of each right derived functor
(lem-weil-pbc-left-exact-injective-resolution-degree-zero,
lem-weil-pbc-injective-resolution-lift-exists).
2. Each horseshoe row splits since its first object is injective: extend its identity
across the first map and factor the complementary projection through the cokernel.
Additivity preserves the splitting identities, so applying `v` gives short exact rows.
The snake lemma defines the cohomology boundary; transport it by `isoRightDerivedObj`
(lem-weil-pbc-complex-ses-homology-long-exact, def-sp-injective-resolutions).
3. Lift a morphism of short exact sequences to the endpoint resolutions and use
lem-weil-pbc-horseshoe-morphism-lift for the middle map. Apply `v` and naturality of the
homology boundary (lem-weil-pbc-complex-ses-long-exact-naturality). The comparison rule
of lem-weil-pbc-derived-functor-map-via-lift yields naturality of the transported maps.
4. Apply Step 3 to the identity morphism between two horseshoes of the same sequence.
The right derived functors preserve identities, so the transported maps are equal.
5. Choose a horseshoe (lem-weil-pbc-injective-resolution-ses) and transport its long
exact cohomology sequence using lem-weil-pbc-derived-functor-map-via-lift. The zeroth
cohomology is a kernel, since the complexes vanish in negative degrees; its first map
is monic because the degree-zero horseshoe map is split monic. Thus the sequence is
exact including the initial zero (lem-weil-pbc-complex-ses-homology-long-exact).
6. Package additivity, exactness, and naturality as the delta-functor of
def-weil-pbc-delta-functor. Step 4 identifies its boundary with that of every horseshoe.
-/
theorem exists_horseshoe_rightDerived_deltaFunctor
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] :
    ∃ (G : CohomologicalDeltaFunctor A B)
      (hF : G.F = (fun n : ℕ ↦ v.rightDerived n)),
      ∀ (S : ShortComplex A) (hS : S.ShortExact)
        (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
        (IC : InjectiveResolution S.X₃)
        (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
        (hαβ : α ≫ β = 0)
        (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
        (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
        (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact),
        ∃ hvH : ((ShortComplex.mk α β hαβ).map
          (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact,
          ∀ n : ℕ,
            G.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) =
              eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫
                (IC.isoRightDerivedObj v n).hom ≫ hvH.δ n (n + 1) rfl ≫
                  (IA.isoRightDerivedObj v (n + 1)).inv := by
  sorry

end CategoryTheory
