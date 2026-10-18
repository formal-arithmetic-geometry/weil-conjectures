/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
/-! # The coefficient line comparison for a divisible torsion exponent -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

/-- The roots power map becomes an isomorphism after extension to an m-torsion ring.
Source: Stacks Project, Etale Cohomology, Tag 03PK, section-kummer; Modules on
Sites, Tag 03EK (blueprint: lem-asd-finite-twist-exponent-line).
Proof: Choose an etale cover carrying a primitive m'-root zeta and its cyclic
basis for mu[m']. Write k=m'/m. The kernel of m on the cyclic module ZMod m'
is k times ZMod m', so zeta^k is a cyclic basis for mu[m]. In these bases the
power map is reduction ZMod m' -> ZMod m, sending the chosen basis to the
chosen basis. Its normalization through the kernel inclusions determines q
uniquely, so the supplied q is exactly this power map. Extend scalars on the
source along ZMod m' -> A and on the target along ZMod m -> A; balancing holds
because mA=0. In the two cyclic bases the induced A-linear map is the identity
on A. It is therefore invertible on the cover, and hence globally. The maps
are defined by a tensor z -> a tensor q(z), so they glue and have exactly the
displayed generator formula after sheafification. No finiteness or flatness
of A is needed. For m=1 the ring A is the zero ring and the same argument
identifies both zero coefficient modules. -/
theorem finiteEtaleTwistExponentLine (A : Type (u + 1)) [CommRing A]
    (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m' : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hq : q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf)) :
    ∃ e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA,
      ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        e.hom.hom.app W (finiteEtaleTateOneGenerator A m' T hA' W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z) := by sorry

end AlgebraicGeometry.Scheme
