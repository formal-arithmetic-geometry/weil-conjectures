/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.KoszulConormalCyclePresentation

/-! # Alternating Koszul products before conormal descent

Source: Stacks Project, Tags 09PQ and 00LS.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Before descent modulo I², ideal elements have alternating products in the
I-annihilated part of resolution homology, realized by a suitable family of
Koszul maps. No factorization through the conormal module is asserted.
Source: Stacks Project, Tag 09PQ, Lemma 23.6.12; Tag 00LS, part (1).
(blueprint: new-t4-koszul-ideal-alternating-products).

Proof: Take a free strictly commutative Tate resolution Q of A/I. For each x
in I choose a degree-one lift with differential x. Its class after tensoring
is independent of the lift: the difference is a cycle in Q, hence a boundary.
Adding or scaling lifts proves A-linearity of this assignment on I, without
yet identifying its kernel. Multiply n such classes in Q tensor A/I. The
product is multilinear and alternating, since odd elements square to zero
in a strictly commutative Tate algebra, also in characteristic two. Each
class is annihilated by I because the tensor factor A/I is. Compare Q with P
by an augmentation-preserving map and transport the products on homology;
this gives F with values in the I-torsion submodule. For each tuple g send
the Koszul generators to its chosen degree-one lifts in Q and compose with
the comparison to P. These maps b preserve augmentation and evaluate each
wedge as the product defining F. Linearity handles arbitrary vectors v.
The actual cycle z is unique for its prescribed image since iCycles is
monic. For n=0 use the empty product, the quotient unit, which is still
annihilated by I. If I=A the homology is zero; I=0 and characteristic two
need no exclusions. Descent modulo I² and independence from the chosen
family b are proved separately in KoszulConormalCycleRelations. -/
theorem koszul_ideal_alternating_products (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))) :
    ∃ (b : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
      (F : I [⋀^Fin n]→ₗ[A]
        (Submodule.torsionBySet A
          ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
            P.complex).homology n) (I : Set A))),
      (∀ (r : ℕ) (g : Fin r → I), (b r g).f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) ∧
      (∀ s : KoszulConormalWedgeCycle A I n,
        (F (fun j ↦ Finsupp.linearCombination A s.g (s.v j))).val =
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
            (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
              (b s.r s.g)))
            ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
              (.down ℕ)).obj
              (ExteriorAlgebra.koszulComplex A s.r
                (fun j ↦ (s.g j : A)))).homologyπ n s.z)) := by sorry

end AlgebraicGeometry
