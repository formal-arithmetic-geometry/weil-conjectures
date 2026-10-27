/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.Paper.PointHeartFiniteStageData

/-! # A step of the exact point-heart and finite-stage argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The two specified point-heart functors are fully faithful and additive, and
have exactly the finite-dimensional vector spaces in their essential images.
Source: BBD 1.3.3--1.3.6; Stacks Tags 06XS, 08J5; steps 1--3, 5--6 of
lem-zl-point-heart-finite-stage (blueprint: lem-zl-point-heart-essential-images).

Proof: exact sections and exact localization commute with cohomology, so the
rational point-fibre equivalence preserves the standard halves. It reflects them:
the complementary truncation has zero image, and full faithfulness reflects zero
objects. Thus the equivalence restricts to hearts. On the module heart the canonical
roof C <- tauLE(0) C -> H^0(C)[0] consists of quasi-isomorphisms. The derived single
embedding is fully faithful and its H^0 is the original module. This gives the
rational assertion. For the common-stage assertion, replace each object by its
finite-stage tauGE(0) tauLE(0) model. Finite scalar extension preserves these models.
Hom is the filtered colimit of the finite-stage linear Hom groups. In finite bases,
a map over Omega is a finite matrix, so its entries lie in one finite extension;
a finite-stage matrix which vanishes over Omega already vanishes. Free spaces over
the base field give essential surjectivity. Sections, scalar extension and cohomology
are additive, so both restrictions are additive. The zero space is covered by the
empty matrix and the identity coefficient extension obeys the same formulas. -/
theorem zl_point_heart_essential_images :
    (∀ A : Padic.FiniteCoefficientFields l Ω,
      (zlPointHeartOmega D l hl A.val).Full ∧
      (zlPointHeartOmega D l hl A.val).Faithful ∧
      (zlPointHeartOmega D l hl A.val).Additive ∧
      (∀ V : ModuleCat.{u} A.val, FiniteDimensional A.val V →
        ∃ X, Nonempty ((zlPointHeartOmega D l hl A.val).obj X ≅ V))) ∧
    (zlPointCommonHeartOmega D l hl Ω).Full ∧
    (zlPointCommonHeartOmega D l hl Ω).Faithful ∧
    (zlPointCommonHeartOmega D l hl Ω).Additive ∧
    (∀ V : ModuleCat.{u} Ω, FiniteDimensional Ω V →
      ∃ X, Nonempty ((zlPointCommonHeartOmega D l hl Ω).obj X ≅ V)) := by sorry

end WeilConjectures
