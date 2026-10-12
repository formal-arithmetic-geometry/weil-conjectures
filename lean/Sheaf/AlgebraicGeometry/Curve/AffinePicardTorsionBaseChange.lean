/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Affine Picard torsion under extension of algebraically closed fields

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance, affine case.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pullback on the `n`-torsion of the Picard group of a smooth connected affine curve
is bijective under extension of algebraically closed fields.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-ext-invariance/
_section.md, affine case (blueprint: lem-sc-affine-picard-torsion-base-change).

Proof: Choose a smooth proper compactification by lem-sc-compactification and its Jacobian by
thm-sc-jacobian-representability. Its boundary is nonempty by lem-sc-pic-affine-quotient; choose a
rational boundary point. The boundary is a finite set of rational points and is unchanged by
algebraically closed field extension. The affine Picard base-change compatibility theorem identifies
the two Picard groups with G/Lambda and G'/Lambda', where G and G' are the points of the two
Jacobians; the Jacobian comparison carries Lambda isomorphically onto Lambda'. The abelian-variety
estimate gives surjectivity of multiplication by n and bijectivity on n-torsion. The point map G ->
G' is injective: equality after field extension recovers the image point and residue-field map of
each k-point, since k -> k' is injective. If a class in G/Lambda maps to zero, its representative
maps into Lambda'; lift this boundary element to Lambda and use injectivity to see the original
class is zero. For surjectivity, represent a torsion class by y in G'. Then ny belongs to Lambda'.
Lift it to lambda in Lambda and choose x in G with nx = lambda by divisibility. The difference
y-j(x) is n-torsion and therefore comes from G[n]. Adding that lift to x produces a representative
in G of the given class, whose n-fold multiple lies in Lambda. Quotient compatibility identifies
this map with Pic.map. Transport from the chosen categorical pullback to any pullback square via its
canonical isomorphism. For n=1 the torsion groups are trivial; nonzero n prime to the characteristic
is exactly the hypothesis needed for the Jacobian torsion comparison. -/
theorem affine_picard_torsion_base_change
    (k k' : Type u) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (P : Scheme.{u}) (π : P ⟶ C) (g : P ⟶ Spec (.of k'))
    (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
    Function.Bijective (fun x : {x : C.Pic // x ^ n = 1} =>
      (⟨Scheme.Pic.map π x.1, by
        change (Scheme.Pic.mapHom π x.1) ^ n = 1
        rw [← map_pow, x.2, map_one]⟩ : {x : P.Pic // x ^ n = 1})) := by sorry

end AlgebraicGeometry
