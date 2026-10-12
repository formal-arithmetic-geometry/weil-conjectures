/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.RingTheory.PairHenselization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.PairHenselizationFiltered
import Sheaf.RingTheory.PairHenselizationEssentiallySmall
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The idempotent selecting a pair henselization fibre component

Source: Stacks Project, More on Algebra, Tags 0AH1 and 0AH3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The canonical map of fibres is a surjective projection with idempotent kernel annihilator.

Source: Stacks Project, More on Algebra, Tag 0AH1 and the product calculation in Tag 0AH3.
(blueprint: lem-weil-pbc-pair-henselization-fiber-projection).

Proof: Filteredness and essential smallness of the pair-etale category allow its
colimit to be represented by a small filtered diagram of commutative A-algebras.
Tag 0AH1 gives the canonical finite product decomposition of the fibre over p into
residue fields at all primes above p. Each component sends x tensor b to rho(x) times
the image of b. Thus this ring equivalence respects the c.pt.right-algebra structures
(on the source through the second tensor factor), so it can be tensored over
c.pt.right with C.
Tensor cancellation and distribution over a finite product identify p.Fiber C with
that product of fibres. On pure tensors its q projection is exactly phi by the
specified compatibility, so equality on all tensors follows by additive generation.
In that product select the element equal to one at q and zero elsewhere and pull it
back to an element e of p.Fiber C. Componentwise multiplication proves idempotence
and phi(e)=1. Extend any element in the q factor by zero to prove surjectivity.
A kernel element has zero q coordinate, so multiplication by e kills it in every
coordinate. The argument also works when the q factor is the zero ring. The given
prime q supplies an index even if other fibres are empty. -/
theorem pair_henselization_fiber_projection
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (C : Type u) [CommRing C] (g : c.pt.right →+* C)
    (q : Ideal c.pt.right) [q.IsPrime] :
    letI := c.pt.hom.hom.toAlgebra
    letI := g.toAlgebra
    letI := (g.comp c.pt.hom.hom).toAlgebra
    letI : IsScalarTower A c.pt.right C :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let p := q.comap c.pt.hom.hom
    ∀ (ρ : p.ResidueField →ₐ[A] q.ResidueField),
      ρ = Ideal.ResidueField.mapₐ p q (Algebra.ofId A c.pt.right) rfl →
    ∀ (φ : p.Fiber C →+* q.Fiber C),
      (∀ (x : p.ResidueField) (y : C),
        φ (TensorProduct.tmul A x y) = TensorProduct.tmul c.pt.right (ρ x) y) →
      ∃ e : p.Fiber C, IsIdempotentElem e ∧ φ e = 1 ∧
        Function.Surjective φ ∧ ∀ x, φ x = 0 → e * x = 0 := by sorry

end RingTheory
