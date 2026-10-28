/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.EtaleUniversalNormalization

/-! # Universal scalar arrows on an etale source

Source: Stacks Project, Tags 06YS, 0G7E, 0D6D and 03ED.
(blueprint: lem-weil-pbc-etale-source-normalization-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- An initial coefficient arrow stays initial on every etale source.

Source: `sites-cohomology.tex`, K-flat resolutions (06YS), their pullback (0G7E),
and composition of derived pullbacks (0D6D); the small etale site (03ED).
(blueprint: lem-weil-pbc-etale-source-normalization-universal).

Proof: pass from fixed-ring module sheaves to modules over their constant ring
sheaves. Let L be derived extension along q, left adjoint to exact restriction.
Initiality of the supplied arrow identifies its target with L applied to its
source, with the arrow equal to the adjunction unit followed by that isomorphism.
Choose a K-flat resolution with flat terms. Inverse image to an etale source
preserves K-flatness and flatness. Both applying inverse image before extension
and applying extension before inverse image are represented by the same
sheafified balanced tensor complex. This gives an invertible inverse scalar mate.
The tensor unit x maps to 1 tensor x, so its unit identity is exactly the localized
normalizationPullbackIso used in etaleIsomorphismNormalizationArrow. Consequently
the displayed arrow is the new adjunction unit followed by the tensor comparison
and the pulled target isomorphism. Transport of the initial unit gives its
universality. No boundedness, flatness of S over R, or nonemptiness of the source
is needed; zero objects and zero coefficient rings are included.
-/
theorem etaleSourceNormalization_universal (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {C' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology q).obj C')
    (h : Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk δ : StructuredArrow _
        (normalizationRestrict Z.smallEtaleTopology q))))
    (V : Z.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Z q δ V))) := by
  sorry

end AlgebraicGeometry.Scheme
