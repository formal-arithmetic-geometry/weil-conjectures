/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite

/-!
# Normal refinement of an absolute Noetherian approximation

Source: Stacks Project, Tag 0EZJ, normal approximation paragraph.
(blueprint: lem-sbc-normal-noetherian-refinement)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- An ordinary Noetherian approximation of a normal integral scheme admits a normal
integral refinement with dominant projections.

Source: Stacks Project, Tag 0EZJ, first two approximation paragraphs; Tags 01ZA,
035E, 035N and 035L for approximation and normalization.
(blueprint: lem-sbc-normal-noetherian-refinement)

Proof: For every stage of N take the scheme-theoretic image of its projection from S.
It is integral and of finite type over the integers. Normalize it in its own function
field. On affine charts the normalization is finite by finiteness of the integral closure
of a finite type integer domain, hence the new stages are Noetherian. Their stalks are
integrally closed and they are integral. Normality of S factors each projection through
this normalization. The factors are dominant; the unique factorization of dominant maps
through normalization defines the transition maps and proves the functor and cone laws.
The new transitions are affine: their composites with the finite normalization maps
are affine and these finite maps are separated, so affineness descends to the first factor.
For the limit assertion, pull back an affine chart of a fixed original stage. Its image
rings embed into the corresponding ring of S, and so do their integral closures since
S is normal. The new rings contain the original image rings, whose filtered union is
the ring of S. Thus their union is also that ring. The affine spectrum calculation gives
the limiting cone on each chart. These comparisons agree on overlaps and glue to give
S as the limit. Every Noetherian scheme is quasi-separated. -/
theorem exists_normal_noetherian_refinement {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (N : S.NoetherianApproximation) :
    ∃ (I : Type u) (hcat : SmallCategory I),
      letI : SmallCategory I := hcat
      ∃ (hco : IsCofiltered I) (X : I ⥤ Scheme.{u})
        (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
        (hI : ∀ i, IsIntegral (X.obj i)),
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)) ∧
        (∀ i, IsDominant (α.app i)) ∧
        (∀ i, IsNoetherian (X.obj i) ∧ QuasiSeparatedSpace (X.obj i) ∧
          ∀ x : X.obj i, IsIntegrallyClosed ((X.obj i).presheaf.stalk x)) := by sorry

end AlgebraicGeometry.Scheme
