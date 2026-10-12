/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent
import Sheaf.RingTheory.EtaleSectionIdempotentSplitting

/-!
# Lifting étale sections over the colimit of pair neighbourhoods

Source: Stacks Project, More on Algebra, Tag 0A02, the paragraph verifying
condition (2) of Tag 09XI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Every étale section modulo the extended ideal lifts over a colimit of all étale
neighbourhoods of a pair whose quotient is the original quotient.
Source: Stacks Project, More on Algebra, Tag 0A02, verification of condition (2)
of Tag 09XI (blueprint: lem-weil-pbc-pair-henselization-sections).

Proof: Pass to a small equivalent filtered category and forget to commutative rings;
forgetting rings under B preserves this connected colimit. The given quotient
bijection identifies H/JH with R = B/J. Descend an étale H-algebra A to an étale
C-algebra D at a stage C, using Tag 00U2 and the colimit comparison isomorphism.
Restrict the given section to D to obtain a C-algebra map s : D to R. It kills JD.
The induced étale R-algebra D/JD has a section to R. Split this section by the
idempotent splitting theorem, obtaining e in D/JD whose image in R is 1 and whose
localization is R. Choose g in D lifting e. Localization at g is étale over D, hence
over B, and its quotient by J is R since localization commutes with quotient.
Consequently D[1/g] is an object of the original neighbourhood category, and C to
D[1/g] is a morphism in that category. Its coprojection to H therefore restricts
to the original coprojection from C. The tensor-product universal property gives
an H-algebra map A = H tensor_C D to H. Its reduction equals the chosen section:
s(g) = 1 makes s extend to D[1/g], and this extension equals the unique B-algebra
map from that object to R. This uniqueness follows by factoring through the
quotient isomorphism B/J to D[1/g]/JD[1/g]. Compare the maps on D and on H and use
the tensor-product universal property once more. Transport along the descent
isomorphism to obtain the required lift of the original section. -/
theorem pair_henselization_sections (B : Type u) [CommRing B] (J : Ideal B)
    [EssentiallySmall.{u} (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map))))]
    [IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map))))]
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c)
    (hq : Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
      (Ideal.le_comap_map)))
    (A : Type u) [CommRing A] [Algebra c.pt.right A] [Algebra.Etale c.pt.right A]
    (σ : A →ₐ[c.pt.right] c.pt.right ⧸ J.map c.pt.hom.hom) :
    ∃ τ : A →ₐ[c.pt.right] c.pt.right,
      (Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).comp τ = σ := by
  sorry

end RingTheory
