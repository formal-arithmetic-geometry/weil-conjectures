/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.RingTheory.PairHenselization
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.PairHenselizationFiltered
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Sheaf.RingTheory.LocalizationOfRegularRing
import Sheaf.RingTheory.GeometricRegularitySeparableExtension
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Regular fibres after an ind-etale extension

Source: Stacks Project, More on Algebra, Tag 0AH3, final fibre calculation,
using Tag 0AH1 and Algebra Tag 07QH.
(blueprint: lem-weil-pbc-pair-henselization-regular-fibers).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- A map out of a Noetherian henselization colimit has geometrically regular fibres
if its composite with the base structure map is regular. No completion, henselian
pair, or G-ring hypothesis is involved in this fibre calculation.

Source: Stacks Project, More on Algebra, Tag 0AH3, displayed product-of-fibres
calculation and its following paragraph; Tag 0AH1; Algebra Tag 07QH.
(blueprint: lem-weil-pbc-pair-henselization-regular-fibers).

Proof: The indexing category is filtered by Tag 0A02. Regard its diagram and colimit
as A-algebras, and apply Tag 0AH1. For a prime q of B = c.pt.right, with contraction
p in A, this gives B tensor_A kappa(p) as a finite product of residue fields at all
primes above p, and kappa(q)/kappa(p) is separable algebraic. Tensor this product
with C over B. The resulting algebra kappa(p) tensor_A C is the finite product
of kappa(q_i) tensor_B C. The projection onto the q component is localization at
an idempotent. Regularity of the composite makes the product geometrically regular
over kappa(p); localization commutes with every finite purely inseparable base
extension, so its q component is geometrically regular over kappa(p) too. Its
Noetherianity follows as a quotient of the Noetherian product. Apply Tag 07QH to
replace kappa(p) by its separable algebraic extension kappa(q). This proves the
required geometric regularity. If the product has no factors, there is no prime q
to check; a zero component has vacuous regularity and causes no exception. -/
theorem pair_henselization_regular_fibers
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (C : Type u) [CommRing C] (g : c.pt.right →+* C)
    (hregular : (g.comp c.pt.hom.hom).IsRegular) :
    letI := g.toAlgebra
    ∀ (q : Ideal c.pt.right) [q.IsPrime],
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := by sorry

end RingTheory
