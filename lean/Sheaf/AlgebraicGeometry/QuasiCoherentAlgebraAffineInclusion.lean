/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-!
# Quasi-coherent algebras on nested affine opens

Source: Stacks Project, Constructions, Lemmas 01LN and 01LO
(blueprint: lem-weil-pbc-quasi-coherent-algebra-affine-inclusion).

The tensor comparison is expressed as a pushout square of commutative rings.
By `CommRingCat.isPushout_tensorProduct`, this says exactly that the canonical map
`A(V) ⊗[𝒪(V)] 𝒪(U) → A(U)` is an isomorphism; its pure-tensor formula is
`a ⊗ r ↦ res(a) * σ_U(r)`. This avoids choosing extra algebra instances for sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On nested affine opens, the canonical tensor comparison for a quasi-coherent algebra
is an isomorphism (the ring square is a pushout). Its spectrum square, using the canonical
charts `U.2.isoSpec`, is cartesian. The spectrum restriction is an open immersion whose image
is the inverse image of the smaller open in the larger one, with the structure map to `U`
given by that square. Spectrum restrictions compose and the self-restriction is the identity.
Source: Stacks Project, Constructions, Lemmas 01LN and 01LO
(blueprint: lem-weil-pbc-quasi-coherent-algebra-affine-inclusion).

Proof: (1) Apply lem-weil-pbc-quasi-coherent-affine-section-base-change to `A.toModule`.
The resulting module comparison respects products and units by the algebra-sheaf structure,
so the canonical tensor comparison is a ring isomorphism, or equivalently the ring square
is a pushout. (2) By lem-weil-pbc-fibre-product-affine-spectra the affine fibre product is
Spec of the tensor product; (1) identifies it with Spec A(U). Base change of the inclusion
U → V is an open immersion and identifies its image with the preimage of U, by
lem-weil-pbc-open-preimage-fibre-product. (3) Restriction maps compose and self-restrictions
are identities. Contravariant functoriality of Spec gives the last two equations. -/
theorem quasi_coherent_algebra_affine_inclusion
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent) :
    (∀ (U V : S.affineOpens) (hUV : U.1 ≤ V.1),
      IsPushout (A.hom.hom.app (op V.1)) (S.presheaf.map (homOfLE hUV).op)
        (A.right.obj.map (homOfLE hUV).op) (A.hom.hom.app (op U.1)) ∧
      IsPullback (Spec.map (A.right.obj.map (homOfLE hUV).op))
        (Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv)
        (Spec.map (A.hom.hom.app (op V.1)) ≫ V.2.isoSpec.inv) (S.homOfLE hUV) ∧
      IsOpenImmersion (Spec.map (A.right.obj.map (homOfLE hUV).op)) ∧
      Set.range (Spec.map (A.right.obj.map (homOfLE hUV).op)).base =
        (Spec.map (A.hom.hom.app (op V.1)) ≫ V.2.isoSpec.inv).base ⁻¹'
          Set.range (S.homOfLE hUV).base) ∧
    (∀ (U V W : S.affineOpens) (hUV : U.1 ≤ V.1) (hVW : V.1 ≤ W.1),
      Spec.map (A.right.obj.map (homOfLE hUV).op) ≫
        Spec.map (A.right.obj.map (homOfLE hVW).op) =
      Spec.map (A.right.obj.map (homOfLE (hUV.trans hVW)).op)) ∧
    (∀ U : S.affineOpens,
      Spec.map (A.right.obj.map (homOfLE (le_refl U.1)).op) =
        𝟙 (Spec (A.right.obj.obj (op U.1)))) := by
  sorry

end AlgebraicGeometry
