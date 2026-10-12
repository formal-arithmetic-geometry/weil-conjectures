/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget

/-!
# Reduction of constant module coefficients to cyclic abelian coefficients

Source: the coefficient reduction in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`, using
Stacks Project, Tags 03Q8, 03Q5 and 03FD.
(blueprint: lem-sbc-constant-module-higher-direct-image-cyclic-reduction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Vanishing for every cyclic group whose order divides d implies vanishing for
constant coefficients Λ/dΛ, with no finiteness assumption on Λ.

Source: the coefficient reduction in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`, using
Stacks Project, Tags 03Q8, 03Q5 and 03FD.
(blueprint: lem-sbc-constant-module-higher-direct-image-cyclic-reduction).

Proof: Forget the module action on Λ/dΛ and express its additive group as the
filtered union of its finitely generated subgroups. If d > 0, each subgroup is a
finite abelian group killed by d, hence a finite direct sum of Z/e with e dividing
d. If d = 0, a finitely generated subgroup is a finite sum of finite cyclic groups
and copies of Z; every positive e divides zero and Z is ZMod 0 with 0 dividing 0.
Constant sheafification preserves these colimits and finite sums. Higher direct
images along the quasi-compact quasi-separated h commute with filtered colimits,
and are additive, so the higher direct image of this constant abelian sheaf is a
filtered colimit of zero objects by H, hence is zero. Finally, forgetting the
Λ-action computes higher direct images on underlying abelian sheaves: use a
module-injective resolution, whose underlying sheaves are acyclic on every
etale object, to obtain the cohomology comparison by Tag 03FD and then
the higher-direct-image comparison by Tag 03Q8. The forgetful functor
reflects zero objects, so the module higher direct image is zero as well. The
argument includes d = 1, degree zero, the zero ring, and the empty scheme. -/
theorem isZero_constantModHigherDirectImage_of_cyclic
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (d q : ℕ)
    (H : ∀ e : ℕ, e ∣ d →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (Y.constantZMod e))))) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  sorry

end AlgebraicGeometry.Etale
