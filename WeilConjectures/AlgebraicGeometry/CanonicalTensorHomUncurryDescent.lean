/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension

/-! # Localization of componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Componentwise uncurrying descends to functions on derived morphisms.
The family obeys the localization equation and transport along isomorphisms.
Naturality for noninvertible morphisms is not asserted here.
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. -/
theorem exists_tensorHomUncurry_descent (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom := by
  let := schemeDerivedTensorMonoidal X
  obtain ⟨t, ht⟩ := exists_tensorHomUncurry_descent_representative X
  obtain ⟨s, hs, hi⟩ := exists_tensorHomUncurry_descent_extension X t ht
  refine ⟨s, ?_, hi⟩
  intro P L M hP φ
  exact (hs P L M hP φ).trans (ht P L M hP φ)

end AlgebraicGeometry
