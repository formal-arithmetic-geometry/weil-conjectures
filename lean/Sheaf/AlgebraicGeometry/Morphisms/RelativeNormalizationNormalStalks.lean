/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.NormalSectionsFiniteProduct
import Sheaf.RingTheory.IntegralClosureFiniteNormalProduct

/-!
# Normal stalks of relative normalization in a locally Noetherian normal source

Source: Stacks Project, Tag 035L.
(blueprint: lem-sbc-relative-normalization-normal-stalks)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Relative normalization in a locally Noetherian scheme with normal local rings has
normal local rings.

Source: Stacks Project, Tag 035L, with Tags 0357, 0358 and 034L.
(blueprint: lem-sbc-relative-normalization-normal-stalks)

Proof: For an affine open V = Spec A of Y, its inverse image W in X is quasi-compact.
Local Noetherianness implies W has finitely many irreducible components. Normal local
rings make these components disjoint open normal integral schemes W_i (Tag 0357).
Their section rings B_i are integrally closed domains (Tag 0358). The sections over W
are the finite product of the B_i, and the integral closure of A in that product is
its product of integral closures A_i in B_i: projection preserves integrality, and
the product of the finitely many monic annihilating polynomials annihilates a tuple
of integral elements. Each A_i is a normal domain (Tag 034L):
an element of its fraction field integral over A_i is integral over A by transitivity;
viewing it in Frac(B_i), normality places it in B_i, and integrality over A puts it
in A_i. The normalization over V is Spec of this product, so it is the disjoint union
of the Spec A_i. The stalk at any point is a prime localization of some normal domain
A_i, hence an integrally closed domain. These affine inverse images cover the
normalization. If W is empty its section ring is the zero ring and its normalization
chart is empty, so it contributes no points. -/
theorem relativeNormalization_normal_stalks {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ z : f.normalization, IsDomain (f.normalization.presheaf.stalk z) ∧
      IsIntegrallyClosed (f.normalization.presheaf.stalk z) := by
  intro z
  obtain ⟨U, hU, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f.fromNormalization z)
      (U := ⊤) trivial
  obtain ⟨n, B, hB, ⟨eB⟩⟩ :=
    normal_sections_finite_product hX (f ⁻¹ᵁ U) (f.isCompact_preimage hU.isCompact)
  let (i : Fin n) : IsDomain (B i) := (hB i).1
  let (i : Fin n) : IsIntegrallyClosed (B i) := (hB i).2
  let := (f.app U).hom.toAlgebra
  let V := f.fromNormalization ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  let p := (hV.primeIdealOf ⟨z, hzU⟩).asIdeal
  let e := (f.normalizationObjIso hU).commRingCatIsoToRingEquiv
  let q := p.map e.toRingHom
  let : q.IsPrime := Ideal.map_isPrime_of_equiv e
  obtain ⟨hd, hi⟩ := integralClosure_normal_localizations_of_finite_product
    (fun i ↦ B i) eB q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  let epq := Localization.localRingEquiv p q e
    (p.comap_map_of_bijective e.toRingHom e.bijective).symm
  let := f.normalization.presheaf.algebra_section_stalk (⟨z, hzU⟩ : V)
  have := hV.isLocalization_stalk ⟨z, hzU⟩
  let es := (IsLocalization.algEquiv p.primeCompl
    (f.normalization.presheaf.stalk z) (Localization.AtPrime p)).toRingEquiv
  let ez := es.trans epq
  exact ⟨ez.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv ez.symm⟩

end AlgebraicGeometry.Scheme
