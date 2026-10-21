/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.CategoryTheory.DerivedTensorComparison
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-! # Normalization of exact derived tensor comparisons

Source: Stacks Project, `sites-cohomology.tex`, Tags 0FPQ and 0FPT, and the explicit
cross-functor cancellation argument of the DAG node
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

The derived monoidal structures are the fixed K-flat structures. The comparison is
assumed natural and normalized on K-flat pairs only. The normalization below uses the
native lax tensorator, the inverse of the model isomorphism in the node. Multiplying
by the two model isomorphisms gives precisely the node's displayed equation.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{wC} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [IsGrothendieckAbelian.{vD} D] [HasDerivedCategory.{wD} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution D]

/-- The prescribed inverse unit comparison of the exact derived functor.
Source: Stacks 0FPQ, 0FPT; the unit formula in
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

The two composites of `singleFunctorIsoCompQ` and `singleFunctorObjUnitIso` are the
native maps `u_C` and `u_D` from the localized unit complex to the derived unit.
`mapCochainComplexεIso.inv` is exactly `e_F⁻¹[0]`, with its termwise single-complex
identification. Thus this composite is `E(u_C⁻¹); κ_I; Q_D(e_F⁻¹[0]); u_D`.
All data are actual composites of the existing canonical isomorphisms. -/
noncomputable def exactDerivedTensorUnitIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsLeftAdjoint]
    [F.Monoidal] :
    F.mapDerivedCategory.obj (𝟙_ (DerivedCategory C)) ≅ 𝟙_ (DerivedCategory D) :=
  F.mapDerivedCategory.mapIso
      (((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app (𝟙_ C) ≪≫
        DerivedCategory.singleFunctorObjUnitIso C).symm) ≪≫
    F.mapDerivedCategoryFactors.app (𝟙_ (CochainComplex C ℤ)) ≪≫
    DerivedCategory.Q.mapIso F.mapCochainComplexεIso.symm ≪≫
    (DerivedCategory.singleFunctorIsoCompQ D 0).symm.app (𝟙_ D) ≪≫
    DerivedCategory.singleFunctorObjUnitIso D

/-- A normalized exact derived tensor comparison is invertible and satisfies the native
associativity and both unit equations, and its inverses form a strong monoidal structure.
Source: Stacks 0FPQ and 0FPT, with the explicit abstract cross-functor argument in
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

Proof:
1. Grothendieck categories have small colimits. Closedness and symmetry make both tensor
functors left adjoints. The given left adjoint F preserves colimits. Apply
`lem-sfb-termwise-strong-monoidal` (the existing `mapCochainComplexMonoidal` instance)
to obtain the signed total comparison τ and its associativity and both unit equations.
2. By `lem-sfb-abstract-kflat-resolution`, every derived object has a K-flat model.
The complex unit is K-flat by its unitors. Reassociation shows that the tensor of two
K-flat complexes is K-flat. Their F-images are K-flat by the explicit hypothesis.
3. On a K-flat pair, solve the normalization for t by cancelling the source tensor
counit and the two exact-functor factorization isomorphisms. The target counit and τ
are isomorphisms as well, so t is invertible there. The defined unit is already an iso.
4. The native associator and unitors obey the localized complex coherence equations:
this is the lax monoidal coherence of Q, with the invertible model maps cancelled.
5. For associativity on P,Q,R, precompose by E of the left-associated model comparison
and postcompose by κ_P tensor (κ_Q tensor κ_R). Naturality of t and κ, its normalization
twice, and the native equations of step 4 reduce both sides to Q_D of the two termwise
associativity composites. These agree by step 1; cancel the model isomorphisms.
6. For the left unit at Q_C P, precompose by E of (u_C tensor 1) m_{I,P} and postcompose
by κ_P. Substitute the unit formula and normalization at I,P. Naturality of the target
model map and its left-unit equation reduce to the termwise left-unit equation.
7. Repeat on P,I with (1 tensor u_C) m_{P,I}; the termwise right-unit equation gives the
right-unit identity. No braiding compatibility of F is used in either calculation.
8. Transport invertibility and these three equations from K-flat models to arbitrary
objects by naturality of t and the native constraints, cancelling model isomorphisms.
9. Invert t and the prescribed unit iso. Naturality and the three inverted coherence
equations give `CoreMonoidal`, whose forward maps are precisely these inverses. -/
theorem exactDerivedTensorComparison_normalization
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat]
    (hKFlat : ∀ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatForTotalTensor ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (t : ∀ K L : DerivedCategory C,
      F.mapDerivedCategory.obj (K ⊗ L) ⟶
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L)
    (ht : ∀ (K K' L L' : DerivedCategory C) (a : K ⟶ K') (b : L ⟶ L'),
      F.mapDerivedCategory.map (a ⊗ₘ b) ≫ t K' L' =
        t K L ≫ (F.mapDerivedCategory.map a ⊗ₘ F.mapDerivedCategory.map b))
    (hnorm : ∀ P Q : CochainComplex C ℤ,
      P.IsKFlatForTotalTensor → Q.IsKFlatForTotalTensor →
      F.mapDerivedCategory.map (LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (F.mapCochainComplexμIso P Q).inv =
      t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          F.mapDerivedCategoryFactors.hom.app Q) ≫
        LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)) :
    (∀ K L : DerivedCategory C, IsIso (t K L)) ∧
    (∀ K L M : DerivedCategory C,
      F.mapDerivedCategory.map (α_ K L M).hom ≫ t K (L ⊗ M) ≫
          (F.mapDerivedCategory.obj K ◁ t L M) =
        t (K ⊗ L) M ≫ (t K L ▷ F.mapDerivedCategory.obj M) ≫
          (α_ (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)
            (F.mapDerivedCategory.obj M)).hom) ∧
    (∀ K : DerivedCategory C,
      F.mapDerivedCategory.map (λ_ K).hom = t (𝟙_ _) K ≫
        ((F.exactDerivedTensorUnitIso).hom ▷ F.mapDerivedCategory.obj K) ≫
        (λ_ (F.mapDerivedCategory.obj K)).hom) ∧
    (∀ K : DerivedCategory C,
      F.mapDerivedCategory.map (ρ_ K).hom = t K (𝟙_ _) ≫
        (F.mapDerivedCategory.obj K ◁ (F.exactDerivedTensorUnitIso).hom) ≫
        (ρ_ (F.mapDerivedCategory.obj K)).hom) ∧
    (∃ s : F.mapDerivedCategory.CoreMonoidal,
      s.εIso = (F.exactDerivedTensorUnitIso).symm ∧
        ∀ K L : DerivedCategory C, (s.μIso K L).inv = t K L) := by
  sorry

end CategoryTheory.Functor
