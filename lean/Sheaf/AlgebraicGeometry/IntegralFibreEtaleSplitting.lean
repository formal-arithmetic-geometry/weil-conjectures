/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSplitResiduePoints
import Sheaf.RingTheory.LiftIdempotentUpstairs
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.RingTheory.LiftIdempotentUpstairs

/-!
# Étale splitting of an integral morphism with finite fibre

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`, with finite residue extensions
(blueprint: lem-weil-pbc-integral-fibre-etale-splitting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An integral morphism of affine schemes with finite fibre and finite residue extensions
splits after a pointed affine étale base change into clopen affine pieces with singleton,
purely inseparable fibres. The base field in the last clause is written at the image of `v`;
the preceding equality identifies that image with `u`. The number of pieces may be zero.

Source: Stacks Project, More on Morphisms, Tag 0BSR,
`lemma-etale-makes-integral-split`
(blueprint: lem-weil-pbc-integral-fibre-etale-splitting).

Proof:
1. Enumerate the finite fibre and apply `exists_etale_split_residue_points` (02LM).
   Shrink to an affine neighbourhood of the marked point (04HX). The new fibre consists of
   distinct points with finite purely inseparable residue extensions.
2. Write the pullback as Spec B over Spec A. Its fibre ring is B tensor κ(u).
   Integrality makes every prime of this fibre ring maximal (00GS); its finite spectrum is
   therefore discrete. Localization and quotient preserve the residue fields at these points.
3. The clopen-idempotent correspondence (00EE) gives orthogonal idempotents for the singleton
   fibre points, with sum one. This also holds for an empty spectrum, whose ring is zero.
4. Descend the finitely many idempotents and their equations by clearing denominators outside
   the marked prime. After an affine shrink they form a complete orthogonal family modulo
   the extended prime ideal of A. The marked point and its residue field are unchanged.
5. Apply `exists_etale_lift_isIdempotentElem` (07M4) finitely many times, preserving the
   quotient of A by the marked prime. Pull back previous lifts at each step. Integrality
   survives base change, and the composite is étale. The quotient isomorphism retains the
   marked prime and identifies its residue field and fibre ring with the preceding ones.
6. Orthogonalize the lifts f_i by e_i = f_i times the product of (1-f_j) for j < i.
   The remaining idempotent is the product of all (1-f_i). Telescoping gives sum one;
   restriction gives the original singleton idempotents and zero for the remainder.
7. Their basic opens are disjoint clopen affine subschemes (00EE, 01I3). Each coordinate
   ring is a quotient by (1-e_i), hence integral over A. Each chosen piece has its unique
   fibre point and the residue extension from step 1; the remainder has empty fibre.
8. The integral remainder has closed image (00GU), missing the marked point. Choose a
   basic open around that point avoiding the image (00E0, 00E4), and shrink the base there.
   The remainder disappears. Base change preserves affineness, integrality and the clopen
   decomposition. When there are no fibre points this makes the entire pullback empty.
-/
theorem exists_integral_fibre_etale_splitting
    {T S : Scheme.{u}} [IsAffine T] [IsAffine S] (π : T ⟶ S) [IsIntegralHom π]
    (s : S) (hfibre : Set.Finite {b : T | π b = s})
    (hresidue : ∀ b : T, π b = s → (π.residueFieldMap b).hom.Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧
      ∃ (m : ℕ) (V : Fin m → (pullback π g).Opens),
        (∀ i, IsClosed (V i : Set ↥(pullback π g))) ∧
        (∀ i, IsAffineOpen (V i)) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
        (⨆ i, V i) = ⊤ ∧
        ∀ i, IsIntegralHom ((V i).ι ≫ pullback.snd π g) ∧
          ∃ v : (V i).toScheme,
            ((V i).ι ≫ pullback.snd π g) v = u ∧
            (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd π g) w = u → w = v) ∧
            @IsPurelyInseparable
              (U.residueField (((V i).ι ≫ pullback.snd π g) v))
              ((V i).toScheme.residueField v) _ _
              (((V i).ι ≫ pullback.snd π g).residueFieldMap v).hom.toAlgebra := by
  sorry

end AlgebraicGeometry
