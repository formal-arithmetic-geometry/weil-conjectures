/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProfinitePointPullback

/-! # Components and geometric generic fibres

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, diagram (4.4).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

/-- The component-site base-change square and its geometric-field equivalence.
Source: HRS, proof of Theorem 4.13, diagram (4.4); Bhatt--Scholze Lemma 2.2.8
(blueprint: lem-zl-generic-component-site-comparison).

Proof: the affine tensor-product description and ind-etale base change make V affine
ind-etale over Ω. Classify these algebras as locally constant functions on profinite
sets. The spectrum homeomorphism identifies that parameter with the actual component
quotient. The affine ind-etale basis, with its finite jointly surjective covers,
is therefore the profinite site over that quotient. Restriction along the component
functor is the resulting equivalence, so its left adjoint is an equivalence too.
For E over π₀(U), base-changing U_E gives V_(E ×_π₀(U) π₀(V)): the spaces are the same
fibre product and their structure sheaves are inverse images of the same sheaf.
Uniqueness gives naturality, and taking adjunction mates gives the displayed square.
Likewise V ×_Ω Ω[E] = Ω[π₀(V) × E]. The geometric-field point equivalence therefore
identifies the structural inverse image with pullback along π₀(V) → *. No genericity
or w-contractibility is used in these site identities. Empty schemes are included. -/
theorem generic_component_site_comparison
    (X : Scheme.{u}) [IsAffine X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (genericComponentProjection V).inverse.IsEquivalence ∧
      Nonempty ((coherentTopology Profinite.{u}).overMapPullback
          (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ⋙
        (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙
            Scheme.proEtaleSheafInverseImage (pullback.fst U.hom η) (Type (u + 1))) ∧
      Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
          (genericComponentProjection V).inverse ≅
        AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage (Spec (.of Ω)) ⋙
          Scheme.proEtaleSheafInverseImage (pullback.snd U.hom η) (Type (u + 1))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
