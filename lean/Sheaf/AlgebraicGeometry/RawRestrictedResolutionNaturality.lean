module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData

/-! # Raw evaluation on a fixed resolution

Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

/-- On the chosen injective resolution, evaluation is natural in the etale object.
Source: Stacks Project, Tag 03Q8, proof of higher direct images; Tags 072W and 0BKV.
(blueprint: lem-weil-pbc-raw-restricted-resolution-naturality).

Proof: Put A(V)=f^{-1}Z[V] and let I be the chosen injective resolution.
Compose the given raw morphism with F[0][q] -> Q(I)[q]. The target is K-injective,
so fullness of localization on maps into a K-injective complex and fullness of the
homotopy quotient give a chain representative A(V)[0] -> I[q]. For t:V' -> V,
precomposition with A(t)[0] represents the restriction of the original morphism.
Apply rawRestricted_resolution_evaluation to these two chain maps and the shifted
resolution. It identifies derived evaluation, followed by the resolution sections
comparison, with evaluation of the chain map at the represented identity generator.

In every degree, the inverse-image/direct-image, sheafification and free-abelian
adjunctions followed by Yoneda identify Hom(A(V),I^n) with I^n(V times_S X).
Under this identification, precomposition by A(t) is exactly restriction of a
section: the represented map sends the identity generator at V' to the restriction
of the generator at V. Thus the two evaluated chain maps give the same section
after restriction. These identifications commute with the differential, since
they are natural in I^n. Applying homology gives the square for the section
complexes. The termwise normalizationSectionsIso and the homology/evaluation
comparison are natural transformations, so their naturality moves restriction to
homology of normalizationPresheafComplex.

Finally undo the shift. The sections, localization and homology shift comparisons
commute with these maps by their naturality. Their factors are the ones in
normalizationRestrictedIso, including the augmentation comparison, so cancellation
of the inverse augmentation recovers the displayed square for the original raw
morphism. A different chain representative changes the evaluated cocycle by a
boundary; hence the equality descends to every raw class. Degree zero, identity
arrows and empty charts use the same calculation. -/
theorem rawRestrictedResolution_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        rawRestrictedCohomologyComparison f q F V'.unop ≫
          (normalizationRestrictedIso f q F (injectiveResolution F) V'.unop).hom =
      rawRestrictedCohomologyComparison f q F V.unop ≫
        (normalizationRestrictedIso f q F (injectiveResolution F) V.unop).hom ≫
          ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ)).map t := by
  sorry

end AlgebraicGeometry.Etale
