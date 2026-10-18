/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Restriction of derived direct image to bounded constructibles

Source: Weil conjectures blueprint, sec-proper-base-change/sk-thm-properbasechange,
order 1302; Stacks Project, Tags 05TC, 08J5, 09AK and 09AL
(blueprint: prop-weil-pbc-restriction-direct-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The restriction uses the canonical shift comparison of ordinary K-injective direct
image. Source: Stacks Project, Section 07A5
(blueprint: prop-weil-pbc-restriction-direct-image). -/
noncomputable instance finiteCoefficientDerivedDirectImage_commShift
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientDerivedDirectImage f Λ).CommShift ℤ :=
  inferInstanceAs ((finiteCoefficientModuleDirectImage f Λ).rightDerivedFunctor.CommShift ℤ)

/-- The ambient ordinary derived functor preserves distinguished triangles, with its
canonical shift comparison. Source: Stacks Project, Section 07A5
(blueprint: prop-weil-pbc-restriction-direct-image). -/
instance finiteCoefficientDerivedDirectImage_isTriangulated
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientDerivedDirectImage f Λ).IsTriangulated :=
  inferInstanceAs ((finiteCoefficientModuleDirectImage f Λ).rightDerivedFunctor.IsTriangulated)

/-- The etale-origin bounded constructible property is triangulated in the actual finite
coefficient module category. Source: Stacks Project, Tags 09AL and 06UQ
(blueprint: prop-weil-pbc-restriction-direct-image).

Proof: finite coefficient rings are Noetherian. Constructible etale module sheaves
form a weak Serre class: refine the finitely many stratifications in a short exact
sequence, then trivialize the finite locally constant terms on etale covers, where
kernels, cokernels and extensions again have finite module values. The exact
comparison identifies bounded etale-origin complexes with bounded complexes having
constructible pro-etale cohomology (Tag 09AL). Shifts preserve this property, and the
long exact cohomology sequence shows it is closed under distinguished triangles.
The zero complex belongs to the property, so it is a triangulated object property. -/
theorem finiteCoefficientBoundedConstructible_isTriangulated
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    : letI : TopologicalSpace Λ := ⊥
      letI : DiscreteTopology Λ := ⟨rfl⟩
      (isBoundedConstructibleFiniteCoefficient T Λ).IsTriangulated := by
  sorry

attribute [instance] finiteCoefficientBoundedConstructible_isTriangulated

/-- Under the specified FIN bound, ordinary derived direct image restricts, on all
objects and all morphisms, to an exact triangulated functor between the recorded full
bounded constructible subcategories. Cohomological intervals change from [a,b] to
[a,b+c], including the zero object when a>b.
Source: blueprint order 1302; Stacks Project, Tags 05TC, 08J5, 09AK and 09AL
(blueprint: prop-weil-pbc-restriction-direct-image).

Proof: the canonical coefficient structure is locally an isomorphism on constant
scalars. Direct image is additive and preserves kernels sectionwise, so its ordinary
right derived functor agrees on bounded below objects with the bounded below right
derived functor. Negative cohomology on a sheaf placed in degree zero therefore
vanishes (Tag 05TC). Finite-ring comparison identifies each constructible cohomology
sheaf of K with a constructible etale-origin sheaf (Tags 09AK and 09AL). FIN gives
constructibility of its higher direct images in nonnegative degrees and vanishing
above c, hence an image in degrees [0,c]. After a shift by -q, the interval is [q,q+c].

If a>b, K is acyclic and is zero in the localization, and its additive derived image
is zero. Otherwise use successive canonical truncation triangles from degree a to b
(Tag 08J5). The initial truncation is zero; each successive quotient is H^q(K)[-q].
Induction on these triangles, using the long exact cohomology sequence and the
triangulated closure of bounded constructibles, puts the image in [a,b+c] and makes
it bounded constructible. The last truncation is isomorphic to K. Finally restrict
the ambient functor to these full subcategories: its morphism maps are unchanged,
its shift isomorphisms restrict, and its images of distinguished triangles are
distinguished because this is true in the ambient category. Mathlib's lift of the
composite of the inclusion and ambient functor records precisely this restriction. -/
theorem restrictionDirectImage
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    (n : ℕ+) {S T : Scheme.{u}} [IsNoetherian T]
    (hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (horder : ∀ (a : A ⧸ I ^ (n : ℕ)) (t : T),
      IsUnit (addOrderOf a : T.presheaf.stalk t))
    (f : S ⟶ T) (c : ℕ)
    (hfin : ConstructibleDirectImageFiniteness A I hI htorsion hperfect n hdim horder f c) :
    letI : TopologicalSpace (A ⧸ I ^ (n : ℕ)) := ⊥
    letI : DiscreteTopology (A ⧸ I ^ (n : ℕ)) := ⟨rfl⟩
    ∃ h : ∀ K : FiniteCoefficientBoundedConstructibleDerivedCategory S (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient T (A ⧸ I ^ (n : ℕ))
        ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K.obj),
      ((isBoundedConstructibleFiniteCoefficient T (A ⧸ I ^ (n : ℕ))).lift
        ((isBoundedConstructibleFiniteCoefficient S (A ⧸ I ^ (n : ℕ))).ι ⋙
          finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))) h).IsTriangulated ∧
      ∀ (K : FiniteCoefficientBoundedConstructibleDerivedCategory S (A ⧸ I ^ (n : ℕ)))
        (a b : ℤ),
        (∀ i : ℤ, (i < a ∨ b < i) → IsZero
          ((DerivedCategory.homologyFunctor
            (FiniteCoefficientModules S (A ⧸ I ^ (n : ℕ))) i).obj K.obj)) →
        ∀ i : ℤ, (i < a ∨ b + (c : ℤ) < i) → IsZero
          ((DerivedCategory.homologyFunctor
            (FiniteCoefficientModules T (A ⧸ I ^ (n : ℕ))) i).obj
              ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale
