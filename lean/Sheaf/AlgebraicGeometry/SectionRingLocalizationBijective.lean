/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Sheaf.AlgebraicGeometry.InvertSCOhomology

/-! # The section-ring localization comparison

Source: Stacks Project, Properties, Lemma 01PW, and Cohomology of Schemes,
Lemma 09MR in degree zero (blueprint: lem-sc-section-ring-localization-bijective).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A ring map satisfying the restriction-and-division formula on a nonvanishing open
is bijective. No affineness or ampleness hypothesis is needed.
Source: Stacks Project, Properties, Lemma 01PW(2), used in Lemma 01Q1;
Cohomology of Schemes, Lemma 09MR, degree zero.
(blueprint: lem-sc-section-ring-localization-bijective).

Apply `invertS_cohomology` with the invertible module `L.tensorPow d`, the structure
module, and cohomological degree zero. Identify degree-zero module cohomology with
sections, remove the structure-module tensor factor by the left unitor, and use the
canonical tensor-power associativity isomorphisms to identify the degree `n` numerator
with sections of `L.tensorPow (n • d)`. The fraction relations identify this additive
fraction presentation with `HomogeneousLocalization.Away (sectionRingGrade L) s.val`:
both identify a numerator divided by `s^n` with its product by `s^b` divided by
`s^(n+b)`, and equality of fractions means equality after a further power of `s`.
The nonvanishing opens supplied by 09MR and by `hU` are equal by extensionality.
Transport the additive equivalence of 09MR along these identifications. Its formula
says its image of each fraction, multiplied by the restriction of `s^n`, is the
restricted numerator. The section `s` freely generates `L.tensorPow d` on `U`, so
multiplication by its tensor powers is injective, even on an empty open. Thus `hφ`
identifies `φ` with this additive equivalence on every fraction. Every element of the
homogeneous localization has such a fraction representative, so `φ` is bijective.
-/
theorem sectionRing_localization_bijective
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d)
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (φ : CommRingCat.of (HomogeneousLocalization.Away (sectionRingGrade L) s.val) ⟶
      Γ(X, U))
    (hφ : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      (φ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property)) •
        (L.tensorPow (n • d)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op (ξ.val (n • d))) :
    Function.Bijective φ := by sorry

end AlgebraicGeometry.Scheme.Modules
