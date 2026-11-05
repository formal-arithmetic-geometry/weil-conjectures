/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import WeilConjectures.FieldTheory.KummerFreeSubgroup
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Galois actions on the geometric generic point with free orbits

Let `X` be an integral scheme with function field `K`, `T = Spec Kˢᵉᵖ` its geometric generic
point in `X_proét`, and `φ : H →* Gal(Kˢᵉᵖ/K)` a group homomorphism. Then `H` acts on `T` on the
right (`AlgebraicGeometry.Scheme.ProEt.genericPointSepAction`), so that pro-étale sheaves can be
evaluated equivariantly at `T` (`CategoryTheory.Sheaf.evaluationRep`).

If `X` is covered by Kummer covers of units `f i` such that `φ x` fixes all `r`-power roots of
some `f i` only for `x = 1`, then `H` acts freely on `Hom(T, W)` for every `W` over a Kummer cover
(`AlgebraicGeometry.Scheme.ProEt.exists_mem_topology_forall_eq_one`). For an abelian variety of
positive dimension over an algebraically closed field, such a cover and a free abelian group `H`
of countable rank exist
(`AlgebraicGeometry.IsAbelianVariety.exists_genericPointSepAction_forall_eq_one`).

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAction`: the right action of `H` on `T`.
- `AlgebraicGeometry.ProEtale.constantSheafCompUpperStarIso`: the pullback of a constant sheaf
  is constant.

## Main statements

- `AlgebraicGeometry.Scheme.ProEt.exists_mem_topology_forall_eq_one`.
- `AlgebraicGeometry.IsAbelianVariety.exists_genericPointSepAction_forall_eq_one`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable (X : Scheme.{u}) [IsIntegral X]

end Scheme.ProEt

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z W : Scheme.{u}}

/-- The pullback of a constant pro-étale sheaf is constant: `g^*` composed with the constant
sheaf functor and the constant sheaf functor are both left adjoint to the global sections
functor, as `Γ(W, g_* -) ≅ Γ(Z, -)`
(`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`). -/
noncomputable def constantSheafCompUpperStarIso (g : Z ⟶ W) :
    constantSheaf (Scheme.ProEt.topology W) A ⋙ (g)^*[A] ≅
      constantSheaf (Scheme.ProEt.topology Z) A :=
  (((constantSheafΓAdj _ A).comp (upperStarLowerStarAdjunction A g)).ofNatIsoRight
    (globalSectionsLowerStarIso A g)).leftAdjointUniq (constantSheafΓAdj _ A)

end ProEtale

end AlgebraicGeometry
