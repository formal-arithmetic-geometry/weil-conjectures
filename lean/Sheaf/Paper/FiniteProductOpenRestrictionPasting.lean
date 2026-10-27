module

public import Sheaf.Paper.FiniteTripleProductDefinitions

/-! # Pasting the normalized binary open restriction

Source: the open-unit calculation in Step 2 of the finite triple-product argument,
blueprint lem-sf-kunneth-coherence, clause (ii).
(blueprint: lem-pur-finite-product-open-restriction-pasting).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteTripleProduct

/-- A binary open comparison preserves supplied restriction identifications.
Source: Step 2 of lem-pur-finite-triple-product-normal-forms, the pullback/tensor
pasting of normalized open units; blueprint lem-sf-kunneth-coherence, clause (ii).
(blueprint: lem-pur-finite-product-open-restriction-pasting).

Proof: expand the two-stage open comparison into open base change, inverse open
projection and the extension compositor. The unit-normalized base-change squares
identify its restriction with the tensor of the two open units. Naturality of
pullback composition and of its tensor comparison moves m and n past the supplied
restriction arrows s and t. Replace the resulting factor restrictions by hs and ht.
The two inverse pullback compositors cancel their forward compositors; the tensor
comparison cancels its inverse. The remaining composite is precisely the unit of
the product open adjunction. This is a binary calculation, on arbitrary unbounded
objects; it uses no proper-image product or compact-support comparison. Identity
opens give tensor functoriality, and zero objects or an empty product give the same
unit equation without any nonemptiness assumption. -/
theorem restrictPair_pasting (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (G : FiniteProductGeometry f g) (M : D A X) (N : D A Y)
    (H : D A G.cf.Z) (J : D A G.cg.Z)
    (s : M ⟶ L(upperStar (ModuleCat.{u + 1} A) G.cf.i).obj H)
    (t : N ⟶ L(upperStar (ModuleCat.{u + 1} A) G.cg.i).obj J)
    (m : H ⟶ (extend A G.cf.i).obj M)
    (n : J ⟶ (extend A G.cg.i).obj N)
    (hs : s ≫ L(upperStar (ModuleCat.{u + 1} A) G.cf.i).map m =
      (openAdj A G.cf.i).unit.app M)
    (ht : t ≫ L(upperStar (ModuleCat.{u + 1} A) G.cg.i).map n =
      (openAdj A G.cg.i).unit.app N) :
    restrictPair A G M N H J s t ≫
      L(upperStar (ModuleCat.{u + 1} A) (finiteProductCompactification G).i).map
        (externalMap A G.r G.t m n ≫
          finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N) =
      (openAdj A (finiteProductCompactification G).i).unit.app (external A G M N) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteTripleProduct
