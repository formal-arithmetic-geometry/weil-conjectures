/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.Paper.EtaleTermwiseHypercohomology
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
/-! # Quantitative stabilization for functorial hypercohomology

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-hypercohomology-uniform-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Elaborate the dependent page and presentation families.
set_option linter.unusedVariables false in
/-- Functorial termwise presentations can be chosen with a quantitative stabilization bound.
Source: Stacks Project, Tags 015J, 015K and 0EZM.

Proof: Choose the Cartan--Eilenberg resolutions and comparison maps as in
`exists_etaleHypercohomology_pullback_functorial`. For a complex zero below a, choose
its resolution zero in these rows. On the first page the support is q >= a and the
resolution degree is nonnegative. In bidegree (q,n-q), an outgoing differential has
negative resolution degree once r > n-q+1; an incoming differential originates
below row a once r > q-a. Consequently both differentials vanish at and after
max 1 (max (q-a+2) (n-q+2)). The finite filtered total-complex construction identifies
this stationary term with its canonical abutment graded piece. Define R to be the
least stabilization threshold at least 1, and use the canonical stationary identifications.
The support estimate bounds R for every valid a. Filtered comparison maps commute
with all these identifications, giving the first-page, abutment, identity and
composition equations of the functorial presentation theorem unchanged.
(blueprint: lem-weil-pbc-hypercohomology-uniform-bound). -/
theorem exists_etaleHypercohomology_uniform_bound
    (P : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (_ : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      (cohomology AddCommGrpCat.{u + 1} X n).obj (DerivedCategory.Q.obj K) ⟶
        (cohomology AddCommGrpCat.{u + 1} Y n).obj (DerivedCategory.Q.obj L))
    (hP : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ L) (n : ℤ),
      P f K L v n = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} f).hom.app
              ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v))) :
    ∃ (D : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (R : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      (      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
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
        ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
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
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (D X K).sequence ∧
          ∀ n : ℤ, P (𝟙 X) K.obj K.obj
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) n = 𝟙 _) ∧
      (∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w ∧
          ∀ n : ℤ, P (g ≫ f) K.obj N.obj
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) n =
            P f K.obj L.obj v n ≫
              P g L.obj N.obj w n)) ∧
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (a q n : ℤ), (∀ s : ℤ, s < a → IsZero (K.obj.X s)) →
        R X K q n ≤ max 1 (max (q - a + 2) (n - q + 2))) := by sorry

end AlgebraicGeometry.Etale
