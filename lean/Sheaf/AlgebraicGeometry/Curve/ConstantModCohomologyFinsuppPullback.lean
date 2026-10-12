/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Functorial direct-sum coordinates for constant coefficients modulo a prime -/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A single prime-field basis of Λ/pΛ gives direct-sum coordinates on both sides
of a cohomology pullback, and pullback acts separately on every coordinate.
Source: Stacks Project, Tags 03Q5 and 0739, together with the coefficient-basis
construction of `lem-sc-constant-mod-charp-finite-sum-colimit`.
(blueprint: lem-pbc-constant-mod-cohomology-finsupp-pullback)

Proof: Give Λ/pΛ its canonical module structure over the lifted prime field
ULift (ZMod p), and choose a basis I. Its basis representation identifies the underlying
additive coefficient group with the direct sum of I copies of ULift (ZMod p).
Apply the constant abelian sheaf functor and its comparison with coefficient forgetting
to get the coproduct decomposition of the source sheaf. Express that coproduct as
the filtered colimit of its finite subcoproducts. On a qcqs scheme, Sheaf.H in degree q
preserves this colimit by the large filtered-colimit theorem, and its additive functor
preserves the finite biproducts. The colimit of these finite sums in abelian groups is
I →₀ H^q(X,Z/p); its universal property gives a. The inverse-image functor preserves
colimits, so the identical decomposition pulls back to Y. Apply the same argument
there to obtain b. Naturality of cohomologyMap with respect to each summand inclusion
makes the two maps agree on every single-coordinate class. Every finitely supported
family is a finite sum of such classes; additivity gives the coordinate equation.
The zero coefficient ring or zero quotient gives an empty I and zero groups. The
argument allows infinite bases, arbitrary q, and empty schemes, and needs no smoothness,
properness, characteristic assumption on the schemes, or bijectivity of pullback. -/
theorem exists_constantModSheaf_cohomology_finsupp_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : Y ⟶ X) (p : ℕ) [Fact p.Prime] (q : ℕ) :
    ∃ (I : Type (u + 1))
      (a : Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p)) q ≃+ (I →₀ Sheaf.H (X.constantZMod p) q))
      (b : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p))) q ≃+
        (I →₀ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj (X.constantZMod p)) q)),
      ∀ x i, b (cohomologyMap g
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p)) q x) i =
        cohomologyMap g (X.constantZMod p) q (a x i) := by sorry

end AlgebraicGeometry.Etale
