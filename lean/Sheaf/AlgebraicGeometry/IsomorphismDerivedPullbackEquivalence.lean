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
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

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

-- The adjoint of the canonical inverse-image coefficient map is the original rho.
private noncomputable def constantPullbackAdjunction
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    proEtaleConstantRingPullback A g ⊣ proEtaleConstantModuleDirectImage g A := by
  have he : proEtaleRingDirectImageMap g (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison g A) =
        proEtaleCoefficientDirectImageMap g A := by
    change (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap g A)) = _
    exact Equiv.apply_symm_apply _ _
  have hd : proEtaleConstantRingPushforward A g = proEtaleConstantModuleDirectImage g A := by
    unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
    rw [he]
    rfl
  exact (proEtaleConstantRingAdjunction A g).ofNatIsoRight (eqToIso hd)

-- Uniqueness of left adjoints identifies the two ordinary pullback constructions.
private noncomputable def constantPullbackModel
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    proEtaleConstantRingPullback A g ≅ sfIntrinsicPullback A g :=
  (constantPullbackAdjunction A g).leftAdjointUniq (sfIntrinsicConstantModuleAdjunction g A)

-- Keep the categorical assembly abstract so kernel checking does not unfold sheaf data.
private theorem derivedEquivalenceWithInverse
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (H R : D ⥤ C) [F.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : F ⋙ H ≅ 𝟭 C) (b : H ⋙ F ≅ 𝟭 D) (adj : F ⊣ R) :
    ∃ e : DerivedCategory C ≌ DerivedCategory D,
      e.functor = F.mapDerivedCategory ∧
      Nonempty (DerivedCategory.Q ⋙ e.inverse ≅
        R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty (e.inverse ≅ H.mapDerivedCategory) := by
  let e₀ : C ≌ D := CategoryTheory.Equivalence.mk F H a.symm b
  have : e₀.functor.Additive := ‹F.Additive›
  have : e₀.inverse.Additive := ‹H.Additive›
  let q : H ≅ R := e₀.toAdjunction.rightAdjointUniq adj
  refine ⟨e₀.mapDerivedCategory, rfl, ?_, ⟨Iso.refl _⟩⟩
  exact ⟨H.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex q (ComplexShape.up ℤ))
      DerivedCategory.Q⟩

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
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := proEtaleConstantRingPullback A g
  let H : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A) :=
    proEtaleConstantRingPullback A (inv g)
  let f : F ≅ sfIntrinsicPullback A g := constantPullbackModel A g
  let h : H ≅ sfIntrinsicPullback A (inv g) := constantPullbackModel A (inv g)
  let a : F ⋙ H ≅ 𝟭 _ :=
    Functor.isoWhiskerRight f H ≪≫ Functor.isoWhiskerLeft (sfIntrinsicPullback A g) h ≪≫
      (sfIntrinsicPullbackComp A (inv g) g).symm ≪≫
      eqToIso (congrArg (sfIntrinsicPullback A) (IsIso.inv_hom_id g)) ≪≫
      sfIntrinsicPullbackId A Y
  let b : H ⋙ F ≅ 𝟭 _ :=
    Functor.isoWhiskerRight h F ≪≫ Functor.isoWhiskerLeft (sfIntrinsicPullback A (inv g)) f ≪≫
      (sfIntrinsicPullbackComp A g (inv g)).symm ≪≫
      eqToIso (congrArg (sfIntrinsicPullback A) (IsIso.hom_inv_id g)) ≪≫
      sfIntrinsicPullbackId A X
  exact derivedEquivalenceWithInverse F H (proEtaleConstantModuleDirectImage g A) a b
    (constantPullbackAdjunction A g)

end AlgebraicGeometry.Scheme
