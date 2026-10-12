/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.CategoryTheory.CartanEilenbergFunctorial
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Pullback naturality of the termwise hypercohomology spectral sequence

Source: Stacks Project, Tags 0EZM, 015J and 015K
(blueprint: lem-weil-pbc-hypercohomology-e1-pullback-functorial).

Mathlib orders bidegrees as (filtration degree, complementary degree). Thus the
node's E₁^{p,q} is written `(q,p)`. Spectral sequence maps start at the intrinsic E₁
page; page zero depends on the chosen resolution.
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborating the dependent family of presentations and all its compatibility equations.
/-- Pullback and a map of bounded-below complexes induce compatible maps of first
hypercohomology spectral sequences and their finite filtered derived abutments.
Source: Stacks, Tags 0EZM, 015J, 015K
(blueprint: lem-weil-pbc-hypercohomology-e1-pullback-functorial).

`P f K L v n` is the canonical map H^n(X,K) → H^n(Y,L) on derived global sections
(def-weil-pbc-cohomology-pullback, derived clause), tied by `hP`: RΓ of the unit of
f^* ⊣ Rf_*, the Leray identification RΓ(X, Rf_* -) = RΓ(Y, -), then RΓ(v).

Proof:
1. Choose Cartan--Eilenberg resolutions I_K and J_L. Exactness of inverse image
   (prop-weil-pbc-inverse-image-exact) and the comparison lift
   (lem-weil-pbc-cartesian-eilenberg-functorial) give f⁻¹ I_K -> J_L over u.
   Apply Γ to the inverse-image unit termwise, then Γ to the lifted map. The
   resulting map of total complexes preserves the second-degree filtration.
   Apply thm-sp-spectral-object-yields and thm-sp-if-e1 to obtain the page maps.
2. Each row is an injective resolution and is K-injective
   (prop-weil-pbc-kinjective-resolutions-exist). Resolve its inverse image and
   factor the row lift through that resolution, up to homotopy
   (def-weil-pbc-kinjective-resolutions). The associated graded map therefore
   computes exactly H^p(u^q) after cohomology pullback
   (def-weil-pbc-cohomology-pullback, lem-weil-pbc-cohomology-pullback-functorial).
3. Functorial convergence in thm-sp-spectral-object-yields identifies the total
   cohomology map with the canonical map on derived global sections, preserves
   the finite abutment filtrations and identifies the stable-page maps with
   the maps on their graded pieces (def-weil-pbc-etale-cohomology).
4. Naturality of the unit and lem-weil-pbc-inverse-image-composition identify
   the composite total map with the map of the composite pair. Comparisons
   into K-injective totals are unique up to homotopy, so the abutment map is
   independent of lifts. The E₁ maps satisfy identity and composition by
   lem-weil-pbc-cohomology-pullback-functorial. Every later page is its predecessor's
   homology (def-sp-spectral-sequence), giving the same laws on all pages.
-/
theorem exists_etaleHypercohomology_pullback_functorial
    (P : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{uNatural + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{uNatural + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
    ∃ (D : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (R : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (n : ℤ),
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫ P f K.obj L.obj v n)
          (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{uNatural + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (D X K).sequence ∧
          ∀ n : ℤ, P (𝟙 X) K.obj K.obj
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{uNatural + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) n = 𝟙 _) ∧
      (∀ {X Y Z : Scheme.{uNatural}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{uNatural + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w ∧
          ∀ n : ℤ, P (g ≫ f) K.obj N.obj
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{uNatural + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{uNatural + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) n =
            P f K.obj L.obj v n ≫
              P g L.obj N.obj w n) := by
  sorry

end AlgebraicGeometry.Etale
