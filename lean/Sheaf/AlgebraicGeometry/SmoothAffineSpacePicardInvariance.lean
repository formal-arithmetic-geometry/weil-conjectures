/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial

/-! # Picard homotopy invariance for smooth affine varieties

Source: Stacks Project, varieties.tex, Tag 0BEH, proof; divisors.tex, Tags 0BD7 and
0BDA; chow.tex, Tag 02TT and divisors.tex, Tag 0BE9
(blueprint: lem-sfb-smooth-affine-space-picard-invariance).

The existing scheme Picard group writes tensor product multiplicatively. The equivalence
below specifies both pullback homomorphisms, including the zero-section inverse.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The zero section of the product of an `F`-scheme with affine `n`-space over `F`.
Its second component has all coordinate functions zero.
Source: Stacks Project, Tag 0BEH, proof with the rational point zero
(blueprint: lem-sfb-smooth-affine-space-picard-invariance). -/
noncomputable def affineSpaceProductZeroSection
    {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) (n : ℕ) :
    X ⟶ pullback f (AffineSpace (ULift.{u} (Fin n)) (Spec (CommRingCat.of F)) ↘
      Spec (CommRingCat.of F)) :=
  pullback.lift (𝟙 X) (AffineSpace.homOfVector f (fun _ ↦ 0))
    (by simp only [Category.id_comp, AffineSpace.homOfVector_over])

/-- Projection to a smooth geometrically integral affine variety induces a Picard group
isomorphism, with inverse given by its zero section, over any field.
Source: Stacks Project, Tag 0BEH, proof; Tags 0BD7, 0BDA, 056S and 0569
(blueprint: lem-sfb-smooth-affine-space-picard-invariance).

Proof plan:
1. By `lem-weil-pbc-smooth-scheme-over-field-regular`, X is regular and locally
   Noetherian. By `rem-pc-regular-normal`, it is normal. Geometric integrality at the
   identity field extension makes X nonempty and integral.
2. The affine fibre-product calculation `lem-weil-pbc-fibre-product-affine-spectra`
   identifies the product over Spec R with Spec R[t_1,...,t_n]. Its projection is flat
   by `lem-nagata-polynomial-projection-flat` and locally of finite type by its finite
   polynomial generators (`def-weil-finite-type-morphism`). Thus its source is locally
   Noetherian by `pqf-lem-locnoeth-lft`.
3. Each fibre is affine n-space over the residue field, by the same fibre-product
   calculation. Its polynomial ring is a nonzero domain by `lem-sfb-polynomial-field-ufd`.
   Its spectrum is nonempty, reduced and irreducible, so all fibres are integral.
4. Tensor pullback preserves local rank-one frames, using `def-sc-invertible-module`,
   `def-pc-module-pullback` and `lem-pc-scheme-pullback-monoidal-existing`. On the generic
   fibre every line is trivial by `lem-sfb-affine-space-invertible-trivial`. Apply
   `lem-sfb-normal-noetherian-generic-line-pullback` with the properties in steps 1--3:
   every line on the product is pulled back from X, giving surjectivity on Picard groups.
5. The zero section followed by projection is the identity, by `def-pc-fibre-product`.
   Pullback composition and identity comparisons (`def-pc-module-pullback`) give a left
   inverse on Picard classes. Thus projection pullback is also injective. Both maps are
   homomorphisms by `lem-pc-scheme-pullback-monoidal-existing`. Surjectivity then makes
   zero-section pullback the two-sided inverse. For n = 0 both maps are inverse scheme
   isomorphisms. None of these arguments requires a perfect field.
-/
theorem smooth_affineSpace_picard_invariance
    (F : Type u) [Field F] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of F))
    [IsAffine X] [Smooth f] [GeometricallyIntegral f]
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    ∃ e : X.Pic ≃*
        (pullback f (AffineSpace (ULift.{u} (Fin n)) (Spec (CommRingCat.of F)) ↘
          Spec (CommRingCat.of F))).Pic,
      e.toMonoidHom = Scheme.Pic.mapHom
        (pullback.fst f (AffineSpace (ULift.{u} (Fin n)) (Spec (CommRingCat.of F)) ↘
          Spec (CommRingCat.of F))) ∧
      e.symm.toMonoidHom = Scheme.Pic.mapHom (affineSpaceProductZeroSection f n) := by
  sorry

end AlgebraicGeometry
