/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Common derived resolution models for transported fixed pairs

Source: `CategoryTheory/Endofunctor/IsoAlgebra.lean`, mapOfNatIsoCompForgetIso;
`CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean`,
rightDerivedFunctorMapOfNatIsoCompForgetIso; Stacks Tags 079P, 070K and 070Y.
(blueprint: lem-sf-fixed-pair-common-derived-resolution)

The two resolution isomorphisms below use the units of the recorded total right
derived functors. Their common target is the literal underlying complex L(U_F I).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' wC wD wB wE gC gD gB gE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {H : D ⥤ D} [H.Additive] [H.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ H ≅ F ⋙ L)
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [HasDerivedCategory.{wB} (IsoAlgebra F)] [HasDerivedCategory.{wE} (IsoAlgebra H)]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inverse derived unit on K-injective complexes, with the
quotient-to-derived comparisons included. -/
private theorem resolutionIso_naturality (G : C ⥤ D) [G.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (t : I ⟶ J) :
    (G.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map t) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J)).hom =
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 I)).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  have := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  have := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J
  simp only [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom,
    Functor.map_id, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [show (DerivedCategory.Q.map t ≫ ((DerivedCategory.quotientCompQhIso C).app J).inv) =
      ((DerivedCategory.quotientCompQhIso C).app I).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map t)
    from DerivedCategory.quotientCompQhIso_inv_naturality t]
  rw [Functor.map_comp, Category.assoc]
  congr 1
  simp only [asIso_inv, Iso.app_hom]
  have hu := NatTrans.naturality_inv (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit h)
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map t)
  dsimp only [Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  rw [Functor.mapHomotopyCategory_map, DerivedCategory.quotientCompQhIso_hom_naturality]

/-- The first canonical resolution isomorphism a_s: derive the transported functor,
forget, invert the derived unit on I, and use the exact-forgetful localization comparison.
Its target is the common underlying complex L(U_F I), by the transport formula.
Source: RightDerivedFunctor/IsoAlgebra.lean, comparison at lines 75-97; Stacks 070Y.
(blueprint: lem-sf-fixed-pair-common-derived-resolution) -/
noncomputable def fixedPairForgottenResolutionIso
    (hB : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {K I : CochainComplex (IsoAlgebra F) ℤ} [I.IsKInjective]
    (s : K ⟶ I) [QuasiIso s] :
    ((forget H).mapDerivedCategory).obj
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hB).obj
          (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
  (forget H).mapDerivedCategory.mapIso
      ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsObjIso hB s) ≪≫
    (forget H).mapDerivedCategoryFactors.app
      (((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- The second canonical resolution isomorphism b_s: identify D(U_F)(QK) with Q(U_F K),
apply RL, and invert its unit on U_F I. The same model L(U_F I) is the target.
Source: RightDerivedFunctor/IsoAlgebra.lean, comparison at lines 75-97; Stacks 070Y.
(blueprint: lem-sf-fixed-pair-common-derived-resolution) -/
noncomputable def fixedPairUnderlyingResolutionIso
    [(forget F).PreservesKInjectiveComplexes]
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {K I : CochainComplex (IsoAlgebra F) ℤ} [I.IsKInjective]
    (s : K ⟶ I) [QuasiIso s] :
    (L.rightDerivedFunctorOfQuasiIsoResolutions hC).obj
        ((forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
  (L.rightDerivedFunctorOfQuasiIsoResolutions hC).mapIso
      ((forget F).mapDerivedCategoryFactors.app K) ≪≫
    L.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hC
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map s)

/-- The comparison obtained by the identity of the common complex model: a_s followed
by the inverse of b_s. No choice of a map on the model is made.
Source: Stacks 070Y and RightDerivedFunctor/IsoAlgebra.lean, comparison at lines 75-97.
(blueprint: lem-sf-fixed-pair-common-derived-resolution) -/
noncomputable def fixedPairCommonModelComparison
    [(forget F).PreservesKInjectiveComplexes]
    (hB : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {K I : CochainComplex (IsoAlgebra F) ℤ} [I.IsKInjective]
    (s : K ⟶ I) [QuasiIso s] :
    (forget H).mapDerivedCategory.obj
        (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hB).obj
          (DerivedCategory.Q.obj K)) ≅
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC).obj
        ((forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
  fixedPairForgottenResolutionIso e hB s ≪≫ (fixedPairUnderlyingResolutionIso hC s).symm

set_option backward.isDefEq.respectTransparency false in
/-- Transport is additive and left exact, commutes with forgetting on objects, maps,
complexes and homotopies, and has the stated canonical common resolution models.
Source: Endofunctor/IsoAlgebra.lean, mapOfNatIsoCompForgetIso and
preservesFiniteLimits_mapOfNatIso; RightDerivedFunctor/IsoAlgebra.lean, lines 75-97;
Stacks 079P, 070K, 070Y and 015F.
(blueprint: lem-sf-fixed-pair-common-derived-resolution)

Proof plan:
1. The structure map is e_X followed by L(theta_X), with inverse L(theta_X inverse)
   followed by e_X inverse. Naturality of e and the fixed-pair morphism equation
   show L(a) commutes with the structure maps (def-weil-endofunctor-fixed-pair-category).
2. Underlying addition is addition in C and D, so the transport is additive. U_F creates
   finite limits, L preserves them, and U_H reflects their universal property: the
   mediating map commutes with structures after each jointly monic limit projection.
   This includes the empty diagram.
3. On complexes and chain maps both composites have terms L(U_F(-)); on homotopies
   their components are L(U_F(h)). Additivity preserves the shift signs and cone matrices
   (def-weil-abstract-derived-category).
4. Apply lem-weil-pbc-kinjective-functorial-existence in B and C. Exactness of U_F
   preserves quasi-isomorphisms (lem-weil-pbc-exact-functor-derived-factorization), and
   its assumed K-injective preservation makes every forgotten resolution K-injective.
   Apply lem-weil-pbc-kinjective-total-derived to obtain the total derived functors
   with units (def-sfb-right-derived-functor).
5. The definitions above give a_s = D(U_H)(R Ltilde(Qs) followed by inverse unit at I),
   followed by the localization comparison, and b_s = RL(Q(U_F s)) followed by inverse
   unit at U_F I, after identifying D(U_F)QK with Q(U_F K). Each factor is invertible;
   the common target is literally Q(L(U_F I)). Their composite a_s b_s inverse is the
   comparison induced by the identity of that model.
6. For t between K-injectives use identity resolutions. Naturality of both derived
   units, together with the exact-forgetful localization comparison, gives the two
   displayed conjugation equations with the identical map Q(L(U_F t)). -/
theorem fixedPair_commonDerivedResolution
    [IsGrothendieckAbelian.{gC} C] [IsGrothendieckAbelian.{gD} D]
    [IsGrothendieckAbelian.{gB} (IsoAlgebra F)]
    [IsGrothendieckAbelian.{gE} (IsoAlgebra H)]
    [CreatesFiniteLimits (forget F)] [CreatesFiniteLimits (forget H)]
    [PreservesFiniteLimits (forget F)] [PreservesFiniteColimits (forget F)]
    [PreservesFiniteLimits (forget H)] [PreservesFiniteColimits (forget H)]
    [(forget F).ReflectsIsomorphisms] [(forget H).ReflectsIsomorphisms]
    [(forget F).PreservesKInjectiveComplexes] [PreservesFiniteLimits L] :
    (mapOfNatIso e).Additive ∧ PreservesFiniteLimits (mapOfNatIso e) ∧
    (mapOfNatIso e ⋙ forget H = forget F ⋙ L) ∧
    (∀ X : IsoAlgebra F,
      ((mapOfNatIso e).obj X).str = e.app X.carrier ≪≫ L.mapIso X.str) ∧
    ((mapOfNatIso e).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (forget H).mapHomologicalComplex (ComplexShape.up ℤ) =
      (forget F).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        L.mapHomologicalComplex (ComplexShape.up ℤ)) ∧
    (∀ (K J : CochainComplex (IsoAlgebra F) ℤ) (f g : K ⟶ J)
        (h : Homotopy f g) (i j : ℤ),
      ((forget H).mapHomotopy ((mapOfNatIso e).mapHomotopy h)).hom i j =
        (L.mapHomotopy ((forget F).mapHomotopy h)).hom i j) ∧
    ∃ (hB : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I),
          I.IsKInjective ∧ QuasiIso s)
      (hC : ∀ K : CochainComplex C ℤ,
        ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s),
      (∀ (K I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I),
        I.IsKInjective → QuasiIso s →
          CochainComplex.IsKInjective
            (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ∧
          QuasiIso (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
      (∀ (I J : CochainComplex (IsoAlgebra F) ℤ) [I.IsKInjective] [J.IsKInjective]
          (t : I ⟶ J),
        (fixedPairForgottenResolutionIso e hB (𝟙 I)).inv ≫
            (forget H).mapDerivedCategory.map
              (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hB).map
                (DerivedCategory.Q.map t)) ≫
            (fixedPairForgottenResolutionIso e hB (𝟙 J)).hom =
          DerivedCategory.Q.map ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map t))) ∧
      (∀ (I J : CochainComplex (IsoAlgebra F) ℤ) [I.IsKInjective] [J.IsKInjective]
          (t : I ⟶ J),
        (fixedPairUnderlyingResolutionIso hC (𝟙 I)).inv ≫
            (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
              ((forget F).mapDerivedCategory.map (DerivedCategory.Q.map t)) ≫
            (fixedPairUnderlyingResolutionIso hC (𝟙 J)).hom =
          DerivedCategory.Q.map ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map t))) := by
  refine ⟨inferInstance, inferInstance, rfl, ?_, rfl, ?_, ?_⟩
  · exact mapOfNatIso_obj_str e
  · intro K J f g h i j
    rfl
  · have hB : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I),
          I.IsKInjective ∧ QuasiIso s := by
      intro K
      obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, s, hI, hs⟩
    have hC : ∀ K : CochainComplex C ℤ,
        ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s := by
      intro K
      obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, s, hI, hs⟩
    refine ⟨hB, hC, ?_, ?_, ?_⟩
    · intro K I s hI hs
      exact ⟨inferInstance, inferInstance⟩
    · intro I J _ _ t
      have hn :
          (forget H).mapDerivedCategory.map
              (((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hB).map
                (DerivedCategory.Q.map t)) ≫
            (fixedPairForgottenResolutionIso e hB (𝟙 J)).hom =
          (fixedPairForgottenResolutionIso e hB (𝟙 I)).hom ≫
            DerivedCategory.Q.map ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map t)) := by
        dsimp only [fixedPairForgottenResolutionIso, Iso.trans_hom, Functor.mapIso_hom]
        rw [← Functor.map_comp_assoc, resolutionIso_naturality, Functor.map_comp]
        simp only [Category.assoc, Iso.app_hom]
        rw [Functor.mapDerivedCategoryFactors_hom_naturality]
        rfl
      rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · intro I J _ _ t
      have hn :
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
              ((forget F).mapDerivedCategory.map (DerivedCategory.Q.map t)) ≫
            (fixedPairUnderlyingResolutionIso hC (𝟙 J)).hom =
          (fixedPairUnderlyingResolutionIso hC (𝟙 I)).hom ≫
            DerivedCategory.Q.map ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map t)) := by
        dsimp only [fixedPairUnderlyingResolutionIso, Iso.trans_hom, Functor.mapIso_hom]
        simp only [Functor.map_id, Iso.app_hom]
        rw [← Functor.map_comp_assoc, Functor.mapDerivedCategoryFactors_hom_naturality,
          Functor.map_comp, Category.assoc, resolutionIso_naturality]
        simp only [Category.assoc]
      rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.Endofunctor.IsoAlgebra
