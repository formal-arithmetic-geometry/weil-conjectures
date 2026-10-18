/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.DerivedPullbackTensorHom

/-!
# Derived pro-etale pullback along a scheme isomorphism

Source: Stacks Project, Derived Categories, Tag 015F, and Pro-etale Cohomology,
Tag 09A5; the equivalence assembly is the node's agent-written proof
(blueprint: lem-weil-isomorphism-derived-pullback-equivalence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite-level derived pullback, specialized to the recorded quotient
`A_{E,n} = O_E / (varpi_E^n)`. This abbreviation is the existing exact termwise
module pullback on the full small pro-etale derived categories. The coefficient
identification is the canonical constant-section map, rather than a supplied isomorphism.
Source: Weil blueprint, derived pullback, order 1467, finite-level clause; Stacks
Tags 03D2 and 015F (blueprint: lem-weil-isomorphism-derived-pullback-equivalence). -/
noncomputable abbrev finiteTorsionDerivedPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI := discreteTopology_bot
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
  letI : IsIso (proEtaleCoefficientInverseImageMap g
      (Padic.coefficientExtensionRing l E n)) :=
    ProEtale.finiteCoefficientCommRingMap_isIso g
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
  proEtaleRingDerivedPullback g
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))
    (asIso (proEtaleCoefficientInverseImageMap g (Padic.coefficientExtensionRing l E n)))

/-- Pullback along a scheme isomorphism is fully faithful and essentially surjective
on the ambient unbounded derived categories of finite-torsion coefficient modules.
The equivalence has the specified pullback as its functor and termwise canonical
module direct image as its inverse, expressed by a natural factorization through
derived localization. The latter is naturally isomorphic to derived pullback along
the inverse scheme isomorphism.
Source: Stacks Project, Tag 015F applied to the exact sheaf equivalence of Tag 09A5
(blueprint: lem-weil-isomorphism-derived-pullback-equivalence).
Proof plan:
1. Use lem-weil-proetale-isomorphism-inverse-image to identify inverse image along g
   with the exact module equivalence inverse to canonical direct image. The coefficient
   map is the constant-preserving isomorphism; tensor cancellation sends m tensor a
   to a m and has inverse m to m tensor 1. Equivalences preserve kernels and cokernels,
   so direct image is exact and both functors are additive.
2. By lem-weil-pbc-exact-functor-derived-factorization, both exact functors descend
   termwise through the unbounded derived localizations. This is precisely the finite
   clause of def-weil-derived-pullback-tensor-hom, already implemented by the displayed
   specialization of proEtaleRingDerivedPullback.
3. Apply the sheaf equivalence unit and counit degreewise. Descend their natural
   isomorphisms by lem-weil-pbc-localization-universal-property. Their triangles hold
   degreewise, and localization detects their equality. These are the equivalence data.
4. The unit conjugates the inverse functor's map into the inverse of each Hom map;
   the counit supplies an object preimage up to isomorphism. Thus the functor is fully
   faithful and essentially surjective, as encoded by the displayed equivalence.
5. For h = inverse g, identify X times_Y V with V over X via h and its projection.
   The coefficient maps agree on constants, hence agree by sheafification uniqueness.
   This is a module-linear natural identification of g_* with h inverse image.
   Applying it degreewise and descending identifies the inverse functor with Lh^*.
No boundedness, constructibility, nonemptiness, or finite-type assumption is used. -/
theorem finiteTorsionDerivedPullback_isEquivalence_of_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ e : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ≌
        proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n),
      e.functor = finiteTorsionDerivedPullback l E n hn g ∧
      Nonempty (DerivedCategory.Q ⋙ e.inverse ≅
        (proEtaleConstantModuleDirectImage g
          (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q) ∧
      Nonempty (e.inverse ≅ finiteTorsionDerivedPullback l E n hn (inv g)) := by
  sorry

end AlgebraicGeometry.Scheme
