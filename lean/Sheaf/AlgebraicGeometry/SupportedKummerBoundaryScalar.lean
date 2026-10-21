/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Sheaf.AlgebraicGeometry.SupportedKummerScalarSource
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence

/-!
# Derived scalar extension of the supported Kummer boundary

Source: blueprint lem-amb-cartier-kummer-map; Stacks 03PL and 0A45
(blueprint: lem-asd-supported-kummer-boundary-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Match the stored instances of the boundary and scalar interfaces.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2


/-- The normalized supported boundary over A is the derived scalar extension of
its normalized Z/N boundary, with the sectionwise coefficient maps.
Source: Stacks 07A4, 03PL; blueprint lem-amb-cartier-kummer-map, final paragraph
(blueprint: lem-asd-supported-kummer-boundary-scalar).

Proof: the supported constant over Z/N has geometric stalk Z/N on D and zero off
D, so its degree-zero complex is K-flat. Its derived extension to A is i_* A_D,
with coefficient unit r mapped to its image in A. The etale roots line is locally
free of rank one over Z/N. Thus its derived extension is the ordinary root tensor
line over A, and the unit sends a pure tensor r tensor z to its coefficient image
tensor z. These give both unbounded scalar-unit universal properties, without
assuming A flat over Z/N. Applying the derived scalar-extension functor to the
relative torsor Kummer boundary produces the relative boundary over A: the torsor
extension and abelian Kummer boundary are unchanged and the root map is extended
on pure tensors. The relative boundary uniquely determines its Ext representative.
The resulting functoriality square is exactly SupportedKummerScalar. -/
theorem supported_kummer_boundary_scalar (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    [NeZero N]
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ)
    (κ₀ : Ext
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
        (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
      (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} (ZMod N))
        (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
          (ZMod.natCast_self N))) 2)
    (hκ₀ : SupportedKummerBoundary (ULift.{u + 1} (ZMod N)) N
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) i hI hT κ₀) :
    SupportedKummerScalar
      ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) hA i κ₀ κ := by
  sorry

end AlgebraicGeometry.Etale
