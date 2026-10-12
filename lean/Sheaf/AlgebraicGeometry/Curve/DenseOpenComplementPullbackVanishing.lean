/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Vanishing for a dense-open closed complement after open restriction

Source: Stacks Project, Tag 0GJA, proof and remark (d).
(blueprint: lem-pbc-k2-dense-open-complement-pullback-vanishing)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- A sheaf pushed forward from the closed complement of a dense open in a curve
has no positive cohomology after restriction along an open immersion.
Source: Stacks Project, Tag 0GJA, proof and remark (d).
(blueprint: lem-pbc-k2-dense-open-complement-pullback-vanishing)

Proof: The finite-type curve X is Noetherian. Its finitely many irreducible components
have generic points, all in the dense open U. Every chain of two distinct points in the
closed complement would extend upward to a generic point outside the complement,
contradicting dimension at most one. Thus the complement has dimension at most zero.
A closed immersion is a homeomorphism onto its range, so Z is zero-dimensional,
Noetherian and of finite type over k. It has finitely many points, all closed, whose
residue fields are k by the algebraically closed Nullstellensatz. Its reduction is a
finite disjoint union of copies of Spec k. Nilpotent invariance identifies its etale
site with that of its reduction; sheaves there have no positive cohomology.
For a:W -> X open, form Z_W = W times_X Z. This is an open subscheme of Z, hence
again a finite disjoint union of algebraically closed points after reduction.
Direct image along the closed immersion i is exact, and it commutes with open
restriction: on an etale V over W both sides evaluate G on V times_X Z.
Forgetting module coefficients commutes with this direct image, and inverse image
commutes with forgetting. Finite exact direct image and the global-sections
comparison identify the displayed cohomology with that of G restricted to Z_W,
which vanishes in positive degrees. Empty complements and empty W give the zero
sheaf; neither torsion nor constructibility is needed. -/
theorem dense_open_complement_pullback_vanishing (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (U : X.Opens) (hU : Dense (U : Set X))
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : Set.range i.base = (U : Set X)ᶜ)
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a] :
    ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H (((a)^*[AddCommGrpCat.{u + 1}]).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (((i)_*[ModuleCat.{u + 1} Λ]).obj G))) q) := by sorry

end AlgebraicGeometry.IsCurve
