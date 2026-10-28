/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap

/-! # Invertibility of the derived signed action of a perfect coefficient complex

Source: the finite-free calculation in paragraph 1 of
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 08J7, 08J9 and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The signed chain map induces an isomorphism into derived internal Hom when
its coefficient object is isomorphic to a two-term complex of units. The map
into derived Hom is essential: the target Hom complex need not compute it by itself.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 08J7, 08J9 and 0A8X.
(blueprint: lem-sf-perfect-coefficient-signed-hom-action).

Proof: first take the coefficient complex to be the two-term unit complex Q0.
Its signed exchange is invertible in every degree by the finite-coordinate
calculation. Tensoring a K-injective complex with this bounded complex of
finite free modules is K-injective: its terms are finite sums of shifts and
its differential is assembled by a mapping cone. Hence homModelMap is an
isomorphism in this case. For a general K-flat Q with the given derived
isomorphism to Q0, represent that isomorphism by a roof of quasi-isomorphisms
between K-flat complexes. Tensoring an arbitrary complex with a
quasi-isomorphism between K-flat complexes is a quasi-isomorphism: its cone is
acyclic and K-flat. Thus both source tensoring with Hom(P,I) and target
tensoring with I descend on this roof. Derived Hom preserves the target
isomorphisms. The signed formula determines the exchange map uniquely by
Hom projections and tensor-sheafification descent, so its naturality gives
a commutative square on each leg of the roof. Transport invertibility from
Q0 through this square. This proves invertibility of the displayed composite,
without claiming K-injectivity of I tensor Q or invertibility of f alone.
The same proof includes zero complexes and the empty site. -/
theorem perfectCoefficient_signedHomAction_isIso
    (P I Q Q0 : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) (hI : I.IsKInjective)
    (hQ : flat.{t, u} Y R Q) (hQ0 : flat.{t, u} Y R Q0)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q0.X k))
    (eNeg : Q0.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q0.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eQ : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q0)
    (f : ((totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor.{t, u} Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) :
    IsIso (DerivedCategory.Q.map f ≫
      homModelMap.{t, u} Y R P (((totalTensor.{t, u} Y R).obj I).obj Q)) := by sorry

end WeilConjectures.IntegralHom
