/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Extension by zero on pro-étale sheaves: adjunction and exactness

For an open immersion `j : U ⟶ X` the extension by zero `j_!` of pro-étale sheaves with values in
a Grothendieck abelian category `A` (for instance sheaves of modules over a finite ring) is left
adjoint to the restriction `j^*` (`AlgebraicGeometry.ProEtale.openImmersionLowerShriekHomEquiv`)
and exact (`AlgebraicGeometry.ProEtale.shortExact_map_openImmersionLowerShriek`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `lem-weil-extension-by-zero-adjunction`: for an open immersion `j`, maps
`j_! M ⟶ N` from the extension by zero of a pro-étale sheaf `M` on `U` correspond to maps
`M ⟶ j^* N`, naturally in both arguments: the hom-equivalence of the adjunction
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`. Since `j` is a
monomorphism, `j_!` is the left Kan extension along the localization functor `U_proét ⥤ X_proét`
(the presheaf being zero on objects not over `U`) followed by sheafification. -/
noncomputable def openImmersionLowerShriekHomEquiv (M : Sheaf (Scheme.ProEt.topology U) A)
    (N : Sheaf (Scheme.ProEt.topology X) A) :
    ((j)_!open[A].obj M ⟶ N) ≃ (M ⟶ (j)^*[A].obj N) :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv M N

lemma openImmersionLowerShriekHomEquiv_naturality_left
    {M M' : Sheaf (Scheme.ProEt.topology U) A} {N : Sheaf (Scheme.ProEt.topology X) A}
    (a : M' ⟶ M) (b : (j)_!open[A].obj M ⟶ N) :
    openImmersionLowerShriekHomEquiv A j M' N ((j)_!open[A].map a ≫ b) =
      a ≫ openImmersionLowerShriekHomEquiv A j M N b :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv_naturality_left a b

lemma openImmersionLowerShriekHomEquiv_naturality_right
    {M : Sheaf (Scheme.ProEt.topology U) A} {N N' : Sheaf (Scheme.ProEt.topology X) A}
    (b : (j)_!open[A].obj M ⟶ N) (c : N ⟶ N') :
    openImmersionLowerShriekHomEquiv A j M N' (b ≫ c) =
      openImmersionLowerShriekHomEquiv A j M N b ≫ (j)^*[A].map c :=
  (openImmersionLowerShriekUpperStarAdjunction A j).homEquiv_naturality_right b c

/-- Blueprint `lem-weil-extension-by-zero-exact`: the extension by zero `j_!` along an open
immersion is exact, i.e. it carries short exact sequences of pro-étale sheaves on `U` to short
exact sequences on `X`. It preserves finite colimits as a left adjoint, and finite limits since
the presheaf-level extension by zero and sheafification are left exact
(`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`). -/
theorem shortExact_map_openImmersionLowerShriek
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology U) A)} (hS : S.ShortExact) :
    (S.map (j)_!open[A]).ShortExact :=
  hS.map_of_exact _

end AlgebraicGeometry.ProEtale
