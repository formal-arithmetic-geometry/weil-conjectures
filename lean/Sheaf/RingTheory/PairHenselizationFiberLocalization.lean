/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.RingTheory.PairHenselization
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.PairHenselizationFiltered
import Sheaf.RingTheory.PairHenselizationEssentiallySmall
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Localization description of a fibre of a pair henselization

Source: Stacks Project, More on Algebra, Tags 0AH1 and 0AH3, the product-of-fibres
calculation. (blueprint: lem-weil-pbc-pair-henselization-fiber-localization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The residue extension at a prime of a Noetherian pair henselization is separable,
and its fibre after any map to C is a localization of the contracted-prime fibre.

Source: Stacks Project, More on Algebra, Tags 0AH1 and 0AH3, displayed fibre product
and its following paragraph.
(blueprint: lem-weil-pbc-pair-henselization-fiber-localization).

Proof: The pair-etale indexing category is filtered by Tag 0A02. Transport the colimit
along the equivalence between rings under A and commutative A-algebras. Reindex
along a small equivalent category, using essential smallness of the pair-etale
category (its fully faithful embedding into finitely generated A-algebras). Tag 0AH1
identifies the fibre over p with the finite product of the residue fields of all
primes over p, by the canonical component maps, and proves each residue extension
separable algebraic. Tensor this decomposition over B with C. Tensor cancellation
identifies the source with p.Fiber C; tensor distribution over the finite product
identifies the target with the product of the q_i.Fiber C, with the canonical maps.
The q projection is localization at the idempotent equal to one at q and zero at
all other factors. Its image in p.Fiber C generates the required submonoid M.
Indeed denominators map to one, each element of the factor lifts by extending it
by zero, and the kernel of projection is killed by the idempotent. These are the
localization axioms. A prime q supplies an index, so an empty product never occurs;
if q.Fiber C is zero the same localization axioms still hold. -/
theorem pair_henselization_fiber_localization
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
    letI := ρ.toRingHom.toAlgebra
    letI := φ.toAlgebra
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      ∃ M : Submonoid (p.Fiber C), IsLocalization M (q.Fiber C) := by sorry

end RingTheory
