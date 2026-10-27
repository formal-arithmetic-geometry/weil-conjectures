/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Flatness of the strict-local refinement

Source: Stacks Project, Algebra, Tag 08HV (lemma-strictly-henselian-functorial-improve),
with the canonical local map characterized in Tag 04GU
(blueprint: lem-sfb-strict-local-refinement-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Algebra

/-- The multiplication map from the base change of a strict henselization to the target
strict henselization is flat. The given local map `h` is the canonical one: it extends
`R → A` as an `R`-algebra map, and its residue map is the specified embedding `ι`.
These are exactly the characterizing conditions of Stacks Tag 04GU; no arbitrary
comparison map or flatness assumption on `R → A` is used.

Source: Stacks Project, Algebra, Tag 08HV
(blueprint: lem-sfb-strict-local-refinement-flat).

Proof:
1. By def-sc-ring-strict-henselization and lem-weil-pbc-strict-henselization-triples,
   both presentations are filtered colimits of etale algebras of finite presentation.
   A pointed etale algebra gives the triple consisting of its pointing kernel and
   the induced residue-field embedding, and a triple gives its composite pointing.
   These mutually inverse descriptions preserve the morphisms. Thus both structural
   maps are ind-etale in the sense of def-weil-pbc-ind-etale-algebra.
2. By the base-change clause of lem-weil-pbc-ind-etale-stability, the algebra
   `A ⊗[R] H` is ind-etale over `A`, without any flatness hypothesis on `R → A`.
3. The universal base-change map `AlgHom.liftEquiv R A H C h` sends `a ⊗ r` to
   `algebraMap A C a * h r`. It is the multiplication map of the statement, since
   `h` agrees with the structural map on `R`. Its source and target are ind-etale
   over `A`; the relative clause of lem-weil-pbc-ind-etale-stability makes this
   `A`-algebra map ind-etale, and hence weakly etale.
4. Weak etaleness includes flatness of this ring map, by
   def-weil-pbc-ind-etale-algebra and def-weil-pbc-flat-ring-map. -/
theorem strictLocalRefinement_flat
    (R : Type u) (A : Type v) (KR H : Type (max u w)) (KA C : Type (max v z))
    [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Field KR] [Algebra (IsLocalRing.ResidueField R) KR]
    [IsSepClosure (IsLocalRing.ResidueField R) KR]
    [Algebra R KR] [IsScalarTower R (IsLocalRing.ResidueField R) KR]
    [Field KA] [Algebra (IsLocalRing.ResidueField A) KA]
    [IsSepClosure (IsLocalRing.ResidueField A) KA]
    [Algebra A KA] [IsScalarTower A (IsLocalRing.ResidueField A) KA]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [CommRing C] [IsLocalRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (P : StrictHenselizationPresentationIn.{u, w} R KR H)
    (Q : StrictHenselizationPresentationIn.{v, z} A KA C)
    (ι : KR →+* KA)
    (_hι : ι.comp (algebraMap (IsLocalRing.ResidueField R) KR) =
      (algebraMap (IsLocalRing.ResidueField A) KA).comp
        (IsLocalRing.ResidueField.map (algebraMap R A)))
    (h : H →ₐ[R] C) [IsLocalHom h.toRingHom]
    (_hres : Q.residueMap.comp h.toRingHom = ι.comp P.residueMap) :
    (AlgHom.liftEquiv R A H C h).toRingHom.Flat := by
  sorry

end Algebra
