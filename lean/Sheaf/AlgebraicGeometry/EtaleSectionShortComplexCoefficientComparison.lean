/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone

/-! # A coefficient comparison of fixed normalized section complexes

Source: Stacks Project, Tag 0A50, functorial resolution proof, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-section-short-complex-coefficient-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A coefficient morphism induces a comparison of fixed section complexes.
Source: Stacks Project, Tag 0A50, resolution functoriality, and Tag 01F7.
(blueprint: lem-weil-pbc-etale-section-short-complex-coefficient-comparison)

Proof: Adjoint φ to F → f_*G. Inverse image is exact, so its right adjoint
preserves injectives. Extend the adjoint coefficient map from the augmentation
of I into f_*J in degree zero by injectivity. At each successor degree,
exactness of I makes the composite to the next term factor through the next
image, and injectivity extends this factor to the full resolution term.
This constructs an augmentation-preserving chain map I → f_*J. Apply
resolutionSectionShortComplexTransfer to it. Substitute hU and hV to identify
the target section complex with the one on the displayed target opens.
The equation hk and monicity of the source open inclusion identify k with
the restricted morphism f on the intersection.

For the whole-scheme homology map use the canonical coefficient transfer
identity, whose cocycle formula is normalized by cI and cJ. For the
intersection map represent a homology class by a cycle on U ∩ V. The
free-abelian-representable sections adjunction turns it into a Hom cocycle
into I. Exact inverse image followed by the adjoint chain map represents
pullback of its Ext class followed by φ. Evaluating its restriction on the
target intersection gives the transfer section. The two composition comparisons
along the square hk are exactly the first two factors of openSquareCoefficient;
restriction of φ gives its last factor. The open_cocycle fields of cI and cJ
therefore give the second identity. Homotopic lifts induce the same maps.
No covering hypothesis or connecting map is used. Zero coefficients, empty
opens, coincident opens and degree zero are included. -/
theorem etaleSectionShortComplex_coefficient_comparison
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U V : X.Opens) (U' V' : Y.Opens)
    (hU : U' = f ⁻¹ᵁ U) (hV : V' = f ⁻¹ᵁ V)
    (k : (U' ⊓ V').toScheme ⟶ (U ⊓ V).toScheme)
    (hk : (U' ⊓ V').ι ≫ f = k ≫ (U ⊓ V).ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (cI : ResolutionSectionCanonicalComparison F I)
    (cJ : ResolutionSectionCanonicalComparison G J) :
    ∃ α : etaleSectionShortComplex U V I.cocomplex ⟶
        etaleSectionShortComplex U' V' J.cocomplex,
      (∀ (q : ℕ) (x : (etaleSectionShortComplex U V I.cocomplex).X₁.homology q),
        cJ.globalEquiv q (HomologicalComplex.homologyMap α.τ₁ q x) =
          Sheaf.H.map φ q (cohomologyMap f F q (cI.globalEquiv q x))) ∧
      (∀ (q : ℕ) (x : (etaleSectionShortComplex U V I.cocomplex).X₃.homology q),
        cJ.openEquiv (U' ⊓ V') q (HomologicalComplex.homologyMap α.τ₃ q x) =
          Sheaf.H.map (openSquareCoefficient f (U ⊓ V).ι (U' ⊓ V').ι k hk F G φ) q
            (cohomologyMap k ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F) q
              (cI.openEquiv (U ⊓ V) q x))) := by sorry

end AlgebraicGeometry.Etale
