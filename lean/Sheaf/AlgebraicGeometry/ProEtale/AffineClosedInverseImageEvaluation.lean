/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.Etale.Pi
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage

/-!
# Inverse-image evaluation for an affine closed immersion

Source: Stacks Project, Tag 09BL, lemma-closed-immersion-affines-apply, (1) and (2)
(blueprint: lem-weil-pbc-affine-closed-inverse-image-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- Restricting the ordinary closed inverse image to the affine ind-etale basis is
naturally isomorphic to sheafification of evaluation along the canonical lift.
At a weakly contractible basis object, the sheafification unit is bijective.
Composing its inverse with the first natural isomorphism gives the asserted
inverse-image evaluation isomorphism, natural in sheaves and in such basis objects.
Weak contractibility is written as surjectivity of evaluation on all epimorphisms;
`Epi` means right cancellability, including for the empty basis object.

Source: Stacks Project, Tag 09BL, lemma-closed-immersion-affines-apply (1),(2)
(blueprint: lem-weil-pbc-affine-closed-inverse-image-evaluation).

Proof plan:
1. Cover-density and finite refinements from lem-weil-pbc-ind-etale-basis give
   restriction equivalences by lem-pc-fppf-dense-sheaf-equivalence. The direct
   image on bases is precomposition with closedSiteBaseChange.
2. The adjunction v ⊣ u of lem-weil-pbc-affine-closed-site-functor-properties
   identifies the presheaf left Kan extension with F(v(-)): (v(V), eta_V) is
   initial before taking opposites. The maps send a section at (U,phi) to its
   restriction along the unique adjoint v(V) → U, and conversely use eta_V.
   These maps are inverse by the colimit relations and natural by uniqueness.
   Apply lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction and
   lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection to obtain the first clause.
3. The lift preserves coverings, so F(v(-)) is separated. Local equality in
   lem-weil-pbc-site-sheafification-sections-local makes its unit injective.
4. Finite disjoint unions belong to both bases: express their coordinate rings
   as filtered colimits of finite products of etale finite-presentation algebras,
   using lem-weil-pbc-filtered-colimits-commute-finite-limits and
   lem-weil-pbc-etale-algebra-finite-product. The lift, being a left adjoint,
   preserves these coproducts. By lem-weil-pbc-proetale-qcqs-finite-family-geometry,
   F sends them to products, including the empty family.
5. Refine a cover of V to a finite basis cover, and take its disjoint union W.
   Ind-etale stability makes W → V weakly etale, and joint surjectivity makes
   it a singleton cover. Representables are sheaves and h_W → h_V is epi:
   Yoneda and the sheaf condition verify right cancellation. Weak contractibility
   lifts id_V to a section V → W. This also handles the empty cover of empty V.
6. A section of the sheafification locally lifts to F(v(-)). Refine finitely,
   combine these lifts into a section on W by step 4, and pull back along the
   section of step 5. This proves surjectivity. Injectivity is step 3.
   The resulting evaluation isomorphisms are induced by the natural unit, so
   they commute with sheaf maps and restrictions between contractible objects. -/
theorem affine_closed_inverseImage_evaluation (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty
      (proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          (Type (u + 1)) ⋙
        (toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous (Type (u + 1))
          (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I)))) ≅
      sheafToPresheaf (ProEt.topology (Spec (.of A))) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
          (closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙
        presheafToSheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) ∧
    (∀ (F : Sheaf (ProEt.topology (Spec (.of A))) (Type (u + 1)))
      (V : (Spec (.of (A ⧸ I))).AffineProEt),
      (∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) (f : P ⟶ Q),
        Epi f → Function.Surjective (f.hom.app (op V))) →
      Function.Bijective
        ((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙ F.obj)).app (op V))) := by
  sorry

end AlgebraicGeometry.Scheme.AffineProEt
