/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Right derived functors after an exact functor

Source: Weil conjectures blueprint, `lem-sc-ext-locally-free`, standard homological algebra
parenthetical; Stacks Project, Tag 015M (blueprint: lem-sc-ext-derived-composite).
-/

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- (blueprint: lem-sc-ext-derived-composite) An exact functor `T` whose injective images
are `U`-acyclic can be pulled inside every right derived functor of the left exact functor `U`.
The isomorphism is canonical: for any injective resolutions `I` of `M` and `J` of `T(M)`,
its forward map is the cohomology map of any lift `φ : T(I) ⟶ J` of the identity, transported
through the injective-resolution identifications and the complex-composition isomorphism.

Source: blueprint `lem-sc-ext-locally-free`, standard homological algebra parenthetical;
Stacks Project, Tag 015M, proof (using Tag 015E).

Proof: choose an injective resolution `M ⟶ I` (def-sp-injective-resolutions). Exactness of
`T` makes `T(M) ⟶ T(I)` a resolution, although its terms need not be injective. The hypothesis
makes every term `T(Iⁿ)` acyclic (def-sp-acyclic). Apply the acyclic-resolution comparison of
lemma-weil-pbc-leray-acyclicity, item 2: any lift to an injective resolution `J` identifies
`RⁱU(T(M))` with `Hⁱ(U(T(I)))`. The composite `T ⋙ U` is left exact and its right derived
functor, computed with `I`, is the same cohomology object (def-sp-left-exact-additive).
Transporting the comparison gives the claimed isomorphism, with the displayed formula for
all choices of resolutions and lifts; homotopy uniqueness makes the formula independent
of those choices. -/
theorem exists_rightDerived_exact_comp_iso
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
    (T : A ⥤ B) (U : B ⥤ C) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] [U.Additive] [PreservesFiniteLimits U]
    (hTU : ∀ (I : A), Injective I → U.rightAcyclic (T.obj I)) (M : A) (i : ℕ) :
    ∃ e : ((T ⋙ U).rightDerived i).obj M ≅ (U.rightDerived i).obj (T.obj M),
      ∀ (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
        (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex),
        T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0 →
        e.hom = (I.isoRightDerivedObj (T ⋙ U) i).hom ≫
          HomologicalComplex.homologyMap
            ((mapHomologicalComplexCompIso (Iso.refl (T ⋙ U))
              (ComplexShape.up ℕ)).inv.app I.cocomplex) i ≫
          HomologicalComplex.homologyMap
            ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i ≫
          (J.isoRightDerivedObj U i).inv := by
  sorry

end CategoryTheory.Functor
