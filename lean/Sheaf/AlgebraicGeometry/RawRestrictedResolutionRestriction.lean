module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData

/-! # Cohomology pullback on a fixed resolution

Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

/-- Etale chart pullback is the restriction on the chosen resolution's section homology.
Source: Stacks Project, Tag 03Q8, restriction of injective resolutions; Tag 03Q9,
final injective-complex paragraph.
(blueprint: lem-weil-pbc-raw-restricted-resolution-restriction).

Proof: Put W = V times_S X, W' = V' times_S X, a = t_X, g = W.hom,
and h = W'.hom. Write sigma_g for the exact inverse-image single comparison,
beta_g for the homology/localization comparison on Gamma(W,g^*I), and C_g for
the sections comparison formed using the inverse of Q(F[0]) -> Q(I).
Expanding the K-injective-resolution comparison gives its inverse as
beta_g.inv followed by C_g followed by H^q(RGamma(W).map sigma_g).
To verify this formula, naturality of the exact-localization comparison gives
Dg(Q(augmentation)) followed by the localization comparison on I equal to
sigma_g followed by Q of the restricted augmentation. Cancel the two augmentation
isomorphisms. The inverse right-derived comparison on g^*I is exactly the
sections unit because g^*I is K-injective.

Apply sectionsComparison_triangle_naturality to I and the isomorphism
Q(F[0]) -> Q(I). It gives C_g followed by derived chart restriction equal to
Q of termwise chart restriction followed by C_h. The single-complex comparison
commutes with inverse-image composition: naturality of the derived composition
isomorphism, followed by its single comparison and the coefficient composition
isomorphism, gives sigma_g followed by cohomology pullback equal to derived
chart restriction followed by sigma_h. Combine these squares and naturality of
beta. The result is inverse resolution comparison at W followed by cohomology
pullback equal to section-complex homology restriction followed by inverse
resolution comparison at W'.

It remains to identify section-complex restriction. Evaluate the inverse-image
adjunction unit at the terminal etale object of W' and use the localization
restriction isomorphism. The pullback diagonal identifies the unit at W with the
identity restriction of F. The composition unit equation identifies the unit at
W' with that unit followed by a^*. Naturality of the a-unit moves the diagonal
through a^*. The first unit followed by diagonal restriction is invertible,
since its localization image is the identity restriction of F(W). Cancel this
composite and the localization isomorphisms. The resulting map on sections is
precisely F.map(t_X.op). Apply this equality in each degree
of I. Naturality of homology under the resulting chain isomorphisms and
NatTrans.app_homology for evaluation identify the remaining two factors of
normalizationRestrictedIso with the presheaf's restriction. Compose with the
resolution square above and cancel the resolution isomorphisms. This proves the
displayed formula. The same equations cover degree zero and empty charts. -/
theorem rawRestrictedResolution_restriction {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (t : V' ⟶ V) :
    normalizationCohomologyRestriction f q F t ≫
        (normalizationRestrictedIso f q F (injectiveResolution F) V').hom =
      (normalizationRestrictedIso f q F (injectiveResolution F) V).hom ≫
        ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ)).map t.op := by
  sorry

end AlgebraicGeometry.Etale
