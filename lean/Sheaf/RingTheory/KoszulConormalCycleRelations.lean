/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.KoszulConormalCyclePresentation

/-! # Conormal relations vanish in Koszul-to-resolution homology

Source: Stacks Project, Tags 09PQ and 00LS.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Evaluate formal wedge-cycle generators in the homology of one resolution,
using a specified family of chain maps. This is an actual finite linear combination. -/
noncomputable def koszulConormalCycleEvaluation (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex) :
    (KoszulConormalWedgeCycle A I n →₀ A) →ₗ[A]
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        P.complex).homology n :=
  Finsupp.linearCombination A fun s ↦
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
        (a s.r s.g)))
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A s.r (fun j ↦ (s.g j : A)))).homologyπ n s.z)

/-- Every exterior-conormal relation among Koszul wedge cycles evaluates to zero
in resolution homology. There is no comparison map or derived-functor object in
this assertion: it is a kernel inclusion for two explicitly constructed linear maps.
Source: Stacks Project, Tag 09PQ (strict Tor product), Tag 00LS (comparison homotopies).
(blueprint: new-e1-koszul-conormal-cycle-relations).

Proof: Compute the homology using a free strictly commutative Tate resolution Q.
An element x of I lifts to degree one with differential x; its homology class
after tensoring with A/I depends only on x modulo I². Additivity and the A/I
scalar rule follow by adding and scaling lifts; changing a lift changes its
class by a boundary, by exactness before tensoring. Products of these degree-one
classes are alternating, including in characteristic two, since the Tate algebra
is strictly commutative. Therefore they satisfy the additive, balanced, and
alternating relations defining the exterior power of I/I² over A/I. Choose
Koszul-to-Q dg algebra maps by lifting the tuple elements in degree one; on a
wedge they give exactly these products. A comparison Q -> P induces an
isomorphism after tensoring and passing to homology. Its composite with each
Koszul map is homotopic to the specified a by Tag 00LS, because Koszul terms
are free and both maps preserve augmentation. Tensoring preserves the homotopy,
so their homology maps agree. Thus the specified evaluation also respects all
the relations, proving the kernel inclusion by linearity. Cycle representatives
with the same image under iCycles agree because iCycles is monic. In degree
zero the empty product is the quotient unit and is killed by I; for I=A all
quotient tensor complexes vanish; for I=0 all positive conormal wedges vanish. -/
theorem koszulConormalCycleEvaluation_ker (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
    (ha : ∀ (r : ℕ) (g : Fin r → I), (a r g).f 0 ≫ P.π.f 0 =
      ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) :
    LinearMap.ker (koszulConormalCyclePresentation A I n) ≤
      LinearMap.ker (koszulConormalCycleEvaluation A I n P a) := by sorry

end AlgebraicGeometry
