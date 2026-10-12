/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Kernel of a successive lower truncation transition

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations).
(blueprint: lem-pc-lower-truncation-transition-kernel)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Source: Stacks Tag 0118 (homology-section-truncations).
(blueprint: lem-pc-lower-truncation-transition-kernel)

Since the projections are epimorphisms, the factorization determines `q` uniquely.
In degree `m` its target is zero, and its kernel is the source, identified with
opcycles. In degree `m+1`, cancel the invertible degree component of the first
projection: `q` is the opcycles quotient, whose kernel is the image of `d m (m+1)`.
In higher degrees both projections are invertible, so the kernel is zero; below
`m` the source is zero. The chain map identity identifies the remaining kernel
differential with the epimorphism from opcycles onto the image of the differential.
The inclusion of homology into opcycles therefore defines the map `φ`, using the
kernel universal property and the constructor for maps from a single complex.
This component and the kernel inclusion determine `φ` uniquely. Its degree `m`
homology map is the identity of cycles modulo boundaries; degree `m+1` homology
vanishes because the kernel differential is epi; all other degrees are zero.
Thus `φ` is a quasi-isomorphism. These arguments apply also to the zero complex,
zero differentials, and acyclic complexes; no boundedness assumption is needed.
-/
theorem exists_lowerTruncationTransitionKernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (m : ℤ)
    (q : K.truncGE m ⟶ K.truncGE (m + 1))
    (hq : K.πTruncGE m ≫ q = K.πTruncGE (m + 1)) :
    ∃ (φ : ((singleFunctor C m).obj (K.homology m)) ⟶ kernel q),
      (∃ (e₀ : (kernel q).X m ≅ K.opcycles m)
            (e₁ : (kernel q).X (m + 1) ≅
              Abelian.image (K.d m (m + 1))),
            e₀.inv ≫ (kernel.ι q).f m =
              (K.truncGEXIsoOpcycles m).inv ∧
            e₁.inv ≫ (kernel.ι q).f (m + 1) ≫
              (K.truncGEXIso m (m + 1)).hom =
                Abelian.image.ι (K.d m (m + 1)) ∧
            e₀.inv ≫ (kernel q).d m (m + 1) ≫ e₁.hom ≫
              Abelian.image.ι (K.d m (m + 1)) =
                K.fromOpcycles m (m + 1) ∧
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
                (K.homology m)).inv ≫ φ.f m ≫ e₀.hom =
                  K.homologyι m) ∧
      (∀ (r : ℤ), r ≠ m → r ≠ m + 1 → IsZero ((kernel q).X r)) ∧
      QuasiIso φ := by sorry

end CochainComplex
