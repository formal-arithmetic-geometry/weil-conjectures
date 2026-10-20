/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion

/-!
# Closed-support amplitude

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-kummer/lem-exc-closed-amplitude.md,
node lem-exc-closed-amplitude, order 1911
(blueprint: lem-exc-closed-amplitude).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The closed exceptional inverse image sends [a,b] into [a,b+c+1], with the
same assertion for constructible cohomology under the extra direct-image finiteness
hypothesis. Ri^! is the right adjoint of the actual closed derived direct image,
whose existence is lem-exc-closed-ambient, not an assumed exceptional functor.
Source: blueprint smooth-purity, sk-prop-a1-kummer, node order 1911
(blueprint: lem-exc-closed-amplitude).

Proof:
1. Exact inverse image commutes with cohomology, so j^* preserves [a,b].
2. The source-library amplitude-by-devissage lemmas apply to Rj_*: its value on
   a sheaf in degree zero is nonnegative, and the dimension hypothesis bounds it
   above by c. Finite truncation induction therefore puts Rj_* j^* K in [a,b+c].
3. The closed-support triangle gives the exact segment
   H^(n-1)(Rj_* j^* K) → H^n(i_* Ri^! K) → H^n(K).
   The outside terms vanish when n<a or n>b+c+1; here c≥0 is used for H^n(K).
4. Closed pushforward is faithful and exact, so its derived cohomology comparison
   reflects these vanishings to Ri^! K.
5. Compare the finite-constant-value constructibility predicate with the source
   library's constructible-sheaf predicate. Exact pullback preserves it on cohomology.
6. Complexes with constructible cohomology form a triangulated subcategory by the
   kernel, cokernel and extension clauses of the constructible Serre theorem.
   Its inverse image under Rj_* is triangulated. The hypothesis on degree-zero
   sheaves and bounded devissage give constructible cohomology of Rj_* j^* K.
   The closed-support triangle then gives constructible cohomology of i_* Ri^! K.
7. The exact closed-pushforward cohomology comparison, constructibility under i^*,
   and the counit i^* i_* ≅ Id give constructible cohomology of Ri^! K.
This uses finite truncation induction instead of a hypercohomology spectral sequence. -/
theorem closedImmersion_rightAdjoint_amplitude
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) :
    (∀ K : DerivedCategoryModule A T,
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ∧
    ((∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf F →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) →
      ∀ K : DerivedCategoryModule A T,
        _root_.DerivedCategory.homologyConcentratedIn a b K →
        (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) →
        _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ∧
        ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))) := by
  classical
  let : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
  let P := upperStar (ModuleCat.{u + 1} A) j
  let G := lowerStar (ModuleCat.{u + 1} A) j
  let I := lowerStar (ModuleCat.{u + 1} A) i
  let E := (R(I)).rightAdjoint
  obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle A i j hij
  have hL (K : DerivedCategoryModule A T)
      (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
      _root_.DerivedCategory.homologyConcentratedIn a (b + c)
        ((R(G)).obj (P.mapDerivedCategory.obj K)) := by
    have hP := P.homologyConcentratedIn_mapDerivedCategory_obj hK
    have hb := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
      ⟨a, b, hP⟩
    have ha := hP.1
    have hh := hP.2
    constructor
    · simpa using _root_.DerivedCategory.isGE_obj_of_isGE (R(G)) 0
        (fun M ↦ G.isGE_rightDerivedFunctor_obj_singleFunctor M) _ hb a
    · exact _root_.DerivedCategory.isLE_obj_of_isLE (R(G)) c
        (fun M ↦ (_root_.DerivedCategory.isLE_iff _ c).2 (hcd M)) _ hb b
  have hbound (K : DerivedCategoryModule A T)
      (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
      _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1) (E.obj K) := by
    have hLK := hL K hK
    have hF : _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
        ((R(I)).obj (E.obj K)) := by
      have hz (n : ℤ) (hn : n < a ∨ b + c + 1 < n) :
          IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
            ((R(I)).obj (E.obj K))) := by
        have hzK : IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj K) := by
          rcases hn with hn | hn
          · exact (_root_.DerivedCategory.isGE_iff K a).1 hK.1 n hn
          · exact (_root_.DerivedCategory.isLE_iff K b).1 hK.2 n (by omega)
        have hzL : IsZero ((_root_.DerivedCategory.homologyFunctor _ (n - 1)).obj
            ((R(G)).obj (P.mapDerivedCategory.obj K))) := by
          rcases hn with hn | hn
          · exact (_root_.DerivedCategory.isGE_iff _ a).1 hLK.1 _ (by omega)
          · exact (_root_.DerivedCategory.isLE_iff _ (b + c)).1 hLK.2 _ (by omega)
        exact (_root_.DerivedCategory.HomologySequence.exact₁ _ (hδ K) (n - 1) n
          (by omega)).isZero_X₂ (hzL.eq_of_src _ _) (hzK.eq_of_tgt _ _)
      exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 (fun n hn ↦ hz n (.inl hn)),
        (_root_.DerivedCategory.isLE_iff _ (b + c + 1)).2
          (fun n hn ↦ hz n (.inr hn))⟩
    apply I.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    exact (_root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)).prop_of_iso
      (I.rightDerivedFunctorIsoMapDerivedCategory.app (E.obj K)) hF
  refine ⟨hbound, ?_⟩
  intro hcons K hK hcK
  refine ⟨hbound K hK, ?_⟩
  let CT := _root_.DerivedCategory.homologyProperty
    (constructibleSheaf (ModuleCat.{u + 1} A) T)
  have hcK' : CT K := fun q ↦
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hcK q)
  have hbK := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
    ⟨a, b, hK⟩
  have hcPK := DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar
    j (K := K) ⟨hbK, hcK'⟩
  have hcL : CT ((R(G)).obj (P.mapDerivedCategory.obj K)) := by
    apply _root_.DerivedCategory.prop_of_bounded (CT.inverseImage (R(G)))
      (constructibleSheaf (ModuleCat.{u + 1} A) U)
      (fun M hM ↦ ?_) _ hcPK.1 hcPK.2
    intro q
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hcons M q
        ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 hM))
  have hcF : CT ((R(I)).obj (E.obj K)) :=
    CT.ext_of_isTriangulatedClosed₁ _ (hδ K) hcK' hcL
  intro q
  have hI : Scheme.IsConstructibleSheaf
      (I.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj (E.obj K))) := by
    let : Scheme.IsConstructibleSheaf
        ((R(I) ⋙ _root_.DerivedCategory.homologyFunctor _ q).obj (E.obj K)) := hcF q
    exact Scheme.IsConstructibleSheaf.of_iso
      ((I.rightDerivedFunctorHomologyFunctorIso q).app (E.obj K)).symm
  have := hI
  have hP : Scheme.IsConstructibleSheaf
      ((upperStar (ModuleCat.{u + 1} A) i).obj
        (I.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj (E.obj K)))) :=
    Scheme.IsConstructibleSheaf.upperStar i _
  let : Scheme.IsConstructibleSheaf
      ((I ⋙ upperStar (ModuleCat.{u + 1} A) i).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj (E.obj K))) := hP
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  exact Scheme.IsConstructibleSheaf.of_iso
    (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
      ((_root_.DerivedCategory.homologyFunctor _ q).obj (E.obj K))))

end AlgebraicGeometry.Etale
