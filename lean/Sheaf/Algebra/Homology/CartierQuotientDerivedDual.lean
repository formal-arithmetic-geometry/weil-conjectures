/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
import Sheaf.RingTheory.LineModuleDuality
import Sheaf.Algebra.Homology.DerivedHomProjectiveResolution
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Sheaf.CategoryTheory.DerivedDegreeZeroNormalization

/-! # Derived dual of a quotient by an invertible ideal

Source: Stacks Project, dualizing.tex, Tag 0BZH
(lemma-compute-for-effective-Cartier-algebraic), and Tag 0A71 (lemma-RHom-ext)
(blueprint: lem-trf-cartier-quotient-derived-dual).
-/

@[expose] public section

set_option autoImplicit false

universe u wS wB

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

/-- Derived coinduction of S along its quotient by a finite projective rank-one ideal
is the ordinary dual conormal module in cohomological degree one. Scalar extension is
written B ⊗[S] I, with its usual left B-action; tensor symmetry identifies this with
I ⊗[S] B, with B acting on the right factor. No Noetherian or nonzero assumption is made.

Source: Stacks Project, dualizing.tex, Tags 0BZH and 0A71
(blueprint: lem-trf-cartier-quotient-derived-dual).

Proof:
1. Finite generation and projectivity split a finite free surjection onto I, using
   def-weil-pbc-projective-module. Apply lem-trf-line-module-duality with the given
   local rank-one equivalences: scalar multiplication identifies S with Hom_S(I,I).
2. Exactness of Hom_S(I,-) applied to 0 → I → S → B → 0 gives an injection
   u : S → Hom_S(I,S), u(s)(x) = sx, and cokernel Hom_S(I,B). Tensor adjunction
   identifies this cokernel with Hom_B(B ⊗[S] I,B): send h to (b ⊗ x ↦ b h(x)),
   with inverse ν ↦ (x ↦ ν(1 ⊗ x)). The composites are identities on pure tensors.
3. Resolve B by E with I in degree -1, S in degree 0, and differential minus inclusion.
   It is a bounded-above projective resolution. By lem-sc-derived-hom-projective-resolution
   and def-sc-module-total-hom-complex its dual is S → Hom_S(I,S), with differential u,
   in degrees 0 and 1. Thus only degree-one cohomology survives and is the dual conormal.
4. By lem-trf-derived-coinduction-adjunction restriction of the claimed left object is
   RHom_S(B,S). Exact scalar restriction commutes with cohomology and reflects zero.
   The resulting degree-one S-linear identification is B-linear: lift b ∈ B to s ∈ S
   and use α(bz) = α(sz) = sα(z) = bα(z). Its inverse is B-linear in the same way.
5. Shift coinduction by 1. It is concentrated in degree zero with cohomology the dual
   conormal. Apply lem-amb-derived-degree-zero-normalization in Mod_B and shift back.
   This includes B = 0. For I = S the dual differential is the identity and both sides
   vanish. If I = 0, scalar endomorphism duality forces S = 0, already included. -/
theorem cartier_quotient_derived_dual
    (S : Type u) [CommRing S] (I : Ideal S)
    [Module.Finite S I] [Module.Projective S I]
    (hlocal : ∀ (p : Ideal S) [p.IsPrime],
      Nonempty (LocalizedModule p.primeCompl I ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime p))
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (S ⧸ I))] :
    Nonempty
      ((derivedCoinduction (Ideal.Quotient.mk I)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (S ⧸ I)) 0).obj
          (ModuleCat.of (S ⧸ I) (Module.Dual (S ⧸ I) ((S ⧸ I) ⊗[S] I))))⟦(-1 : ℤ)⟧) := by
  sorry

end ModuleCat
