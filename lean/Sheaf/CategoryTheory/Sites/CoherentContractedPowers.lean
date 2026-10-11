/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation

/-!
# Coherent integer powers of a Zariski torsor

Source: blueprint `sec-curve-estimates/sk-prop-hilbert90/lem-sc-torsor-h1.md`,
contracted-product group law (blueprint: def-sc-coherent-contracted-powers).
-/

@[expose] public section

universe uCP wCP

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory.Sheaf.Torsor

/-- Coherent powers, specified by their sheaf quotient presentations. `product m n` exhibits
`power (m+n)` as the contracted product of the two powers: equivalently it specifies the
canonical torsor isomorphism from that quotient. The cases `(k,1)` and `(-k,-1)` recursively
specify the iterated contracted powers. Degree zero and one are literally the prescribed
torsors, and degree minus one has the same sheaf with the negated action. Coherence is stated
on representatives; universality extends these identities to the quotient sheaves.
Source: blueprint `lem-sc-torsor-h1`, coherent integer-power construction.
(blueprint: def-sc-coherent-contracted-powers) -/
structure CoherentContractedPowers (X : AlgebraicGeometry.Scheme.{uCP})
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{wCP}} (T : Torsor G) where
  power : ℤ → Torsor G
  zero : power 0 = trivial G
  one : power 1 = T
  inverse_sheaf : (power (-1)).sheaf = T.sheaf
  inverse_vadd (U : (Opens X)ᵒᵖ) (g : G.obj.obj U)
      (s : (power (-1)).sheaf.obj.obj U) :
    cast (congrArg (fun F : Sheaf (Opens.grothendieckTopology X) (Type wCP) => F.obj.obj U)
      inverse_sheaf) ((power (-1)).vadd U g s) =
    T.vadd U (-g)
      (cast (congrArg (fun F : Sheaf (Opens.grothendieckTopology X) (Type wCP) => F.obj.obj U)
        inverse_sheaf) s)
  product (m n : ℤ) : BinaryContractedProductPresentation X (power m) (power n) (power (m+n))
  left_unit (n : ℤ) (U : (Opens X)ᵒᵖ) (g : (power 0).sheaf.obj.obj U)
      (t : (power n).sheaf.obj.obj U) :
    cast (congrArg (fun k : ℤ => (power k).sheaf.obj.obj U) (Int.zero_add n))
      ((product 0 n).quotient U g t) =
    (power n).vadd U
      (cast (congrArg (fun P : Torsor G => P.sheaf.obj.obj U) zero) g) t
  right_unit (n : ℤ) (U : (Opens X)ᵒᵖ) (t : (power n).sheaf.obj.obj U)
      (g : (power 0).sheaf.obj.obj U) :
    cast (congrArg (fun k : ℤ => (power k).sheaf.obj.obj U) (Int.add_zero n))
      ((product n 0).quotient U t g) =
    (power n).vadd U
      (cast (congrArg (fun P : Torsor G => P.sheaf.obj.obj U) zero) g) t
  associative (l m n : ℤ) (U : (Opens X)ᵒᵖ) (x : (power l).sheaf.obj.obj U)
      (y : (power m).sheaf.obj.obj U) (z : (power n).sheaf.obj.obj U) :
    cast (congrArg (fun k : ℤ => (power k).sheaf.obj.obj U) (Int.add_assoc l m n))
      ((product (l+m) n).quotient U ((product l m).quotient U x y) z) =
    (product l (m+n)).quotient U x ((product m n).quotient U y z)
  commutative (m n : ℤ) (U : (Opens X)ᵒᵖ)
      (x : (power m).sheaf.obj.obj U) (y : (power n).sheaf.obj.obj U) :
    cast (congrArg (fun k : ℤ => (power k).sheaf.obj.obj U) (Int.add_comm n m))
      ((product n m).quotient U y x) = (product m n).quotient U x y
  cancellation (U : (Opens X)ᵒᵖ) (t : (power 1).sheaf.obj.obj U)
      (s : (power (-1)).sheaf.obj.obj U) :
    T.vadd U
      (cast (congrArg (fun P : Torsor G => P.sheaf.obj.obj U) zero)
        (cast (congrArg (fun k : ℤ => (power k).sheaf.obj.obj U)
          (add_neg_cancel (1 : ℤ))) ((product 1 (-1)).quotient U t s)))
      (cast (congrArg (fun F : Sheaf (Opens.grothendieckTopology X) (Type wCP) => F.obj.obj U)
        inverse_sheaf) s) =
    cast (congrArg (fun P : Torsor G => P.sheaf.obj.obj U) one) t

end CategoryTheory.Sheaf.Torsor
