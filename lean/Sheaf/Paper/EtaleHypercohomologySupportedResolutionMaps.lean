/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Support-controlled filtered resolution maps

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-supported-resolution-maps).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- Elaborate the dependent presentation, stable-range and resolution-map families.
/-- Construct the filtered resolution comparison on every page in the support-controlled
stable range. The abutment map is expressed on K-injective resolutions; no derived
adjunction identification, identity law, composition law, or threshold selection is asserted.
Source: Stacks Project, Tags 015J (first spectral sequence), 015K (filtered functoriality),
and 0EZM (the common lower-bound argument).
(blueprint: lem-weil-pbc-supported-resolution-maps).

Proof:
1. Choose the supported CE resolution before constructing its presentation; an arbitrary
   existential presentation from exists_etaleHypercohomology_ce_total_maps does not suffice.
   If K is zero in all degrees, use the zero CE resolution. Otherwise its nonzero degrees
   have a least element b. Shift K so that b becomes zero, apply
   exists_cartanEilenberg_resolution, and reindex back. Its zero negative rows then give
   zero rows below b, hence below every lower bound a of K, simultaneously. Perform the
   filtered total and page construction on these resolutions. Extend the resolution index
   by zero; the second filtration L satisfies
   L^p Tot^i = 0 for p > i and L^p Tot^i = Tot^i
   for p ≤ a. The signed row comparisons give the displayed E₁ equation.
2. If r ≥ max(1,q-a+2,n-q+2), then q+r > n+1 and q-r+1 ≤ a.
   Hence the outer filtration steps in degrees n+1 and n-1 are respectively zero
   and the whole object. The cycle/boundary formulas are their stationary formulas.
   Apply stableSubquotient_at_bounds and transport the cohomology image filtration
   along the specified total-to-derived comparison c. Use the canonical representative
   quotient comparisons, rather than arbitrary isomorphisms. They depend only on q,n,r,
   and not on the witness a. Thus eInf is defined for the existential stable-range proof;
   proof irrelevance handles different witnesses and support bounds.
3. Exact inverse image and the CE comparison lift yield filtered total maps. Such a map
   sends a cycle representative in L^q to a cycle in the target L^q, and sends a boundary
   representative to a boundary. On the stationary quotient its map therefore sends the
   class of z to the class of its image. The cohomology image restriction sends the same
   class to the same image class. After quotienting by the next filtration step these
   maps agree by the cokernel universal property. This gives precisely the displayed
   cokernel map and proves its compatibility with the stationary comparisons.
4. For any supplied resolution lift j over v, the CE augmentation is a quasi-isomorphism
   by cartanEilenberg_augmentation_quasiIso. Precomposition into the target K-injective
   resolution is injective in the homotopy category, so the CE lift and comparison
   followed by j are homotopic. Apply Γ and precompose with the sectionwise unit.
   Its naturality and the finite-diagonal summand formulas identify the two endpoints
   with the total-section map and the presentation w followed by the supplied w.
   Homotopic maps have equal homology maps. Using c_formula cancels the source total
   comparison, giving precisely the displayed conjugate of H(w). Restrict to the image
   filtration for t and ht; naturality from step 3 gives the final equation for any hc.
   Empty schemes, zero complexes and bidegrees outside the support are included: all
   corresponding subquotients are zero and their comparisons are the unique maps.
-/
theorem exists_etaleHypercohomology_supported_resolution_maps :
    ∃ (D : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (n : ℤ),
        ∀ (j : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶ (D Y L).ρ.complex)
          (hj : Nonempty (Homotopy
            (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (D X K).ρ.map ≫ j) (v ≫ (D Y L).ρ.map))),
        ∀ (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D X K).ρ.complex ⟶
            ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (D Y L).ρ.complex)
          (hw : ∀ i : ℤ, w.f i =
            globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f ((D X K).ρ.complex.X i) ≫
              (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (j.f i)),
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
            ((@resolutionEtaleCohomologyIso.{u} X K.obj (D X K).ρ.complex
              (D X K).ρ.map (D X K).ρ.quasiIso (D X K).ρ.isKInjective n).inv ≫
            HomologicalComplex.homologyMap w n ≫
            (@resolutionEtaleCohomologyIso.{u} Y L.obj (D Y L).ρ.complex
              (D Y L).ρ.map (D Y L).ρ.quasiIso (D Y L).ρ.isKInjective n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r)
          (hY : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (L.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) := by sorry

end AlgebraicGeometry.Etale
