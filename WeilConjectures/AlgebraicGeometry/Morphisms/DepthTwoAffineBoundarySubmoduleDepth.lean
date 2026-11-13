/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.Finiteness
import WeilConjectures.RingTheory.DepthOneOfMaximalNotAssociated
import WeilConjectures.AlgebraicGeometry.Morphisms.BoundaryMaximalNotAssociated

/-! # Positive depth of finite boundary submodules

Source: Stacks Project, Tags 0AV8, 0AVN and 0E9I.
(blueprint: lem-sbc-affine-restriction-boundary-submodule-depth)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Positive depth of finite boundary submodules.

Source: Stacks Project, Tags 0AV8, 0AVN, 0E9I, 01LC, 05AM and 00LL.
(blueprint: lem-sbc-affine-restriction-boundary-submodule-depth)

Proof: The affine V is Noetherian. Cover U intersect V by finitely many
basic opens D(f_i) contained in it. Since the point of p lies outside U,
every f_i belongs to p. The direct image is quasi-coherent by Tag 01LC;
its section module P therefore localizes on D(f_i) to P[1/f_i]. Since its
sections are sections on U intersect V, sheaf separatedness makes the map
P → product_i P[1/f_i] injective. Localize this injection at p, using
exactness and commutation with finite products. If z in P_p is killed by
the maximal ideal pR_p, each f_i kills z. But f_i is a unit in the i-th
factor, so every component of z is zero, and injectivity gives z = 0.
The same holds in S_p because S_p injects into P_p. Thus the maximal ideal
is not an associated prime of S_p. Finiteness follows from S.FG and
localization. If S_p is nonzero, Tag 00LL supplies a regular element in the
maximal ideal; its singleton is a regular sequence, giving depth at least
one. If S_p is zero (in particular when the cover is empty), its depth is
infinite. This is the finite basic-open form of the argument of Tag 0AVN. -/
theorem depth_one_affine_boundary_submodule
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    ∃ hfinite : Module.Finite (Localization.AtPrime p) (LocalizedModule.AtPrime p S),
      letI := hfinite
      (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
        (LocalizedModule.AtPrime p S) := by
  classical
  let R := L.presheaf.obj (op V)
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite R S := Module.Finite.of_fg hS
  have hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p S) := inferInstance
  refine ⟨hfinite, ?_⟩
  exact depth_one_of_finite_localized_module_of_no_maximal_associated
    (boundary_maximal_not_associated U N hqc V hV S hS p hy)

end AlgebraicGeometry.Scheme
