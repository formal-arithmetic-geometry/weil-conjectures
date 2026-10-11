/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Scheme-theoretic union of two closed subschemes

Source: Stacks Project, Morphisms, Definition 0C4H and Lemma 0C4J,
and Lemma 01QP; Algebra, Lemma 00E0 (9)
(blueprint: lem-weil-pbc-scheme-theoretic-union).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Definition 0C4H and Lemma 0C4J (first sentence and
its affine-local description), Lemma 01QP; Algebra, Lemma 00E0 (9).
(blueprint: lem-weil-pbc-scheme-theoretic-union)

The quasi-coherent ideal sheaves of the two closed immersions are `i'.ker` and `i''.ker`.
Their infimum is again quasi-coherent by the type `X.IdealSheafData`, and on every affine
open its ideal is the intersection of the two ideals (`IdealSheafData.ideal_inf`). Its
canonical closed subscheme is the scheme-theoretic union, locally the quotient spectrum.

Proof following the three steps of the node:
1. The kernels are quasi-coherent by def-sbc-closed-immersion-ideal-sheaf. Their
   intersection is quasi-coherent by lem-weil-pbc-quasi-coherent-ideal-intersection.
   By lem-weil-pbc-quasi-coherent-ideal-closed-subscheme it defines a closed immersion
   whose kernel is this intersection and whose affine pullback is the quotient spectrum.
2. On each affine open identify its points with primes by
   lem-weil-pbc-affine-open-spec-points. Use
   lem-weil-pbc-closed-immersion-image-zero-locus for the three closed immersions and
   lem-weil-pbc-zero-locus-ideal-intersection to identify the image as the union.
   The affine opens cover the ambient scheme (def-pc-scheme), so this equality is global.
3. The intersection is contained in each kernel. Apply
   lem-weil-pbc-closed-immersion-factor-ideal-inclusion to each of the two original
   immersions to obtain closed immersions into the union with the stated equations. -/
theorem scheme_theoretic_union
    {X Z' Z'' : Scheme.{u}} (i' : Z' ⟶ X) (i'' : Z'' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i''] :
    IsClosedImmersion (i'.ker ⊓ i''.ker).subschemeι ∧
      (i'.ker ⊓ i''.ker).subschemeι.ker = i'.ker ⊓ i''.ker ∧
      (∀ U : X.affineOpens,
        IsPullback ((i'.ker ⊓ i''.ker).subschemeCover.f U)
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk ((i'.ker ⊓ i''.ker).ideal U))))
          (i'.ker ⊓ i''.ker).subschemeι U.2.fromSpec) ∧
      Set.range (i'.ker ⊓ i''.ker).subschemeι.base =
        Set.range i'.base ∪ Set.range i''.base ∧
      (∃ a' : Z' ⟶ (i'.ker ⊓ i''.ker).subscheme,
        IsClosedImmersion a' ∧
          a' ≫ (i'.ker ⊓ i''.ker).subschemeι = i') ∧
      (∃ a'' : Z'' ⟶ (i'.ker ⊓ i''.ker).subscheme,
        IsClosedImmersion a'' ∧
          a'' ≫ (i'.ker ⊓ i''.ker).subschemeι = i'') := by
  sorry

end AlgebraicGeometry
