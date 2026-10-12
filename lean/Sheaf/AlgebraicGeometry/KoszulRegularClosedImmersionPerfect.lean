/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.PerfectClosedImmersion
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import Sheaf.Paper.KoszulComplex

/-!
# Koszul-regular closed immersions are perfect

Source: Stacks Project, More on Morphisms, Lemma 37.61.7, Tag 068C
(blueprint: lem-sc-koszul-regular-closed-immersion-perfect).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed immersion locally cut out by finite Koszul-regular sequences has a local
Koszul resolution by finite free modules, is a perfect closed immersion, and its
pushed-forward structure sheaf is perfect in `D(𝒪_Y)`.
Source: Stacks Project, Tag 068C, Lemma 37.61.7
(blueprint: lem-sc-koszul-regular-closed-immersion-perfect).

Proof: (1) On an affine open `U`, the quotient-spectrum identification of
`def-weil-closed-immersion` identifies the restricted pushforward with the sheaf
associated to `A/I`. (2) `def-weil-pbc-koszul-regular-sequence` gives vanishing of
positive Koszul homology. In degree zero, the differential of
`def-weil-pbc-koszul-complex` has image `I`, so the augmentation to `A/I` is a
quasi-isomorphism. Exactness of sheafification preserves this quasi-isomorphism.
(3) Exterior-power bases make the Koszul terms finite free, and terms above the
length vanish. The resulting local strictly perfect representatives give
`def-pc-perfect-complex`. (4) These bounded finite free quotient resolutions
satisfy `def-sc-perfect-closed-immersion`. No Noetherian hypothesis is required. -/
theorem koszulRegular_closedImmersion_perfect {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      ∃ (I : Ideal (Γ(Y, U))) (r : ℕ) (f : Fin r → Γ(Y, U)),
        I = Ideal.span (Set.range f) ∧ RingTheory.Sequence.IsKoszulRegular f ∧
        ∃ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
            Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
          i ∣_ U ≫ U.toSpecΓ =
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (∀ (U : Y.Opens) (hU : IsAffineOpen U),
      ∀ (I : Ideal (Γ(Y, U))) (r : ℕ) (f : Fin r → Γ(Y, U)),
        I = Ideal.span (Set.range f) → RingTheory.Sequence.IsKoszulRegular f →
        ∀ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
            Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
          i ∣_ U ≫ U.toSpecΓ =
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) →
          (∃ q : ((tilde.functor Γ(Y, U) ⋙
                Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
                  (ComplexShape.down ℕ)).obj
                    (ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f) ⟶
              (ChainComplex.single₀ U.toScheme.Modules).obj
                ((Scheme.Modules.restrictFunctor U.ι).obj
                  ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            QuasiIso q) ∧
          (∀ n : ℕ, Module.Free (Γ(Y, U) : Type u)
              ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n) ∧
            Module.Finite (Γ(Y, U) : Type u)
              ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n)) ∧
          (∀ n : ℕ, r < n →
            IsZero ((ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f).X n))) ∧
    IsPerfectClosedImmersion i ∧
    Scheme.IsPerfect Y
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) := by
  sorry

end AlgebraicGeometry
