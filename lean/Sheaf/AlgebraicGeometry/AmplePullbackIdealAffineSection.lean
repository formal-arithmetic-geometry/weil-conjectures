/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.AmpleIdealSection
import Sheaf.AlgebraicGeometry.AffineCapSectionOpen

/-! # Ideal-supported affine sections of ample pullbacks

Source: Stacks Project, Properties, Proposition 01Q3 and Lemma 01PV.
(blueprint: lem-sc-ample-pullback-ideal-affine-section).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample pullback admits ideal-supported affine power sections outside the ideal support.

Source: Stacks Project, Properties, Proposition 01Q3 and Lemma 01PV;
Varieties, Lemma 09NX, final paragraph.
(blueprint: lem-sc-ample-pullback-ideal-affine-section).

Proof: write M = f^* L. The ample ideal section theorem supplies a section of
J tensor M^p, with p positive, whose image is nonvanishing at y. Ampleness supplies
a section of M^q, q positive, with affine nonvanishing locus through y. Tensor these
sections and use the associator and the tensor-power addition isomorphism to obtain
a section of J tensor M^(p+q). Its image has locus the intersection of the two
original loci, since the modules are invertible and their fibres have rank one.
The affine-cap-section-open theorem makes this intersection affine. The ideal
inclusion has zero fibre at every point of its support, so the intersection avoids
that support. The canonical monoidal pullback isomorphism identifies M^(p+q) with
f^*(L^(p+q)); transport both the ideal-supported section and its image through this
isomorphism. Naturality of the left unitor identifies the transported image with
the ideal inclusion tensored with the identity followed by the left unitor.
An isomorphism preserves the maximal-ideal submodules of stalks, hence preserves
the nonvanishing locus. The exponent p+q is positive. -/
theorem exists_ample_pullback_ideal_affine_section
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [L.IsInvertible]
    [((tensorPullback f).obj L).IsInvertible]
    (hL : IsAmple Y ((tensorPullback f).obj L)) (J : Y.IdealSheafData)
    (y : Y) (hy : y ∉ (J.support : Set Y)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ v : Γ(J.toModules ⊗ (tensorPullback f).obj (L.tensorPow n), ⊤),
        ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V ∧
          (V : Set Y) = nonvanishingLocus ((tensorPullback f).obj (L.tensorPow n))
            ((J.toModulesι ▷ (tensorPullback f).obj (L.tensorPow n) ≫
              (λ_ ((tensorPullback f).obj (L.tensorPow n))).hom).app ⊤ v) ∧
          Disjoint (V : Set Y) (J.support : Set Y) := by sorry

end AlgebraicGeometry.Scheme.Modules
