/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Localization.Basic
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Regularity through localization

Source: Stacks Project, More on Algebra, proof of Lemma Tag 07PT, line 12392
(blueprint: lem-weil-pbc-regular-through-localization).
-/

@[expose] public section

universe u v w

namespace RingHom

/-- If a ring map out of a localization is regular after precomposition with the
localization map, then the map out of the localization is regular. Here ψ is
`algebraMap A' C` and the composite ψ ∘ λ is `algebraMap A C` through
`IsScalarTower A A' C`. Source: Stacks
Project, More on Algebra, proof of Lemma Tag 07PT, line 12392
(blueprint: lem-weil-pbc-regular-through-localization).

Proof:
1. Flatness of the composite implies flatness of C over A' by
`lem-weil-pbc-flat-over-localization` with M = C, using the localization axioms;
thus ψ is flat (`def-weil-pbc-flat-ring-map`, Algebra 00HT (2)).
2. For a prime q' of A', its inverse image q in A is prime and misses W.
The localization induces an A-algebra isomorphism σ from κ(q) to κ(q') = k
by `lem-weil-pbc-localization-prime-residue-field-iso` (Algebra 00E3, 00C9).
3. The identity maps on C and k are module localizations at W: denominators
act invertibly and the fraction and kernel conditions hold with denominator 1.
By `lem-weil-pbc-localization-tensor-product` (Algebra 00DL), the canonical map
C ⊗[A] k → C ⊗[A'] k is a localization. W already acts invertibly on its source,
so that map is bijective and respects multiplication, the unit, and k-scalars.
4. Tensoring σ with the identity on C and composing with the map of step 3
gives a ring isomorphism Θ from the composite's fibre to ψ's fibre, compatible
with σ on residue-field scalars (`def-weil-pbc-localization-at-prime`).
5. The composite's fibre is Noetherian and geometrically regular. Transport
Noetherianity across Θ. A finite purely inseparable extension k'/k is also
such an extension of κ(q) via σ. The scalar-compatible Θ induces mutually
inverse maps between the two base-changed fibre rings. Their regularity is
therefore identical (`def-weil-pbc-noetherian-ring`,
`def-weil-pbc-finite-purely-inseparable-extension`, `def-weil-regular-scheme`;
Algebra 0382). Hence ψ's fibre is geometrically regular over k.
6. Flatness from step 1 and the fibre conditions from steps 2–5 give regularity
of ψ by `def-weil-pbc-g-ring` (More on Algebra 07BZ).
-/
theorem isRegular_of_comp_algebraMap_localization
    {A : Type u} {A' : Type v} {C : Type w}
    [CommRing A] [CommRing A'] [CommRing C]
    [Algebra A A'] [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    (W : Submonoid A) [IsLocalization W A']
    (hψ : (algebraMap A C).IsRegular) :
    (algebraMap A' C).IsRegular := by
  sorry

end RingHom
