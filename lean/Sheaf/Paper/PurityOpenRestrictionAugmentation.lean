/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.PuritySupportCommonInjectives
public import Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Open restriction of the comparison augmentation

Source: Stacks Project, sites.tex, Tag 03CF; proetale.tex, Tags 099V and 09B1
(blueprint: lem-pur-open-restriction-comparison-augmentation).

All functors act on ordinary fixed-ring module sheaves. The explicit source transport
only identifies restriction of a degree-zero complex with the degree-zero complex of
restriction; its other factor is the prescribed canonical comparison beta.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]

/-- The canonical transport of the degree-zero source along beta and open restriction.
Source: Stacks Project, Tag 03CF, and the canonical beta of
`lem-pur-comparison-pullback-open-unit`
(blueprint: lem-pur-open-restriction-comparison-augmentation). -/
noncomputable def supportComparisonOpenSourceIso
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapCochainComplexPlus.obj
      (supportComparisonSource V A
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F))).obj ≅
    ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
        (supportComparisonSource T A F))).obj :=
  ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapHomologicalComplex (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j) (.up ℤ) 0).app F).symm ≪≫
    (NatIso.mapHomologicalComplex (comparisonPullbackOpenUnitGamma A j) (.up ℤ)).app
      (supportComparisonSource T A F).obj

/-- The restricted resolution map is beta followed by restriction of h, with only the
canonical identification of the degree-zero source made explicit.
Source: Stacks Project, Tag 03CF
(blueprint: lem-pur-open-restriction-comparison-augmentation). -/
noncomputable def supportComparisonOpenResolutionMap
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapCochainComplexPlus.obj
      (supportComparisonSource V A
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F)) ⟶
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J :=
  ObjectProperty.homMk
    ((supportComparisonOpenSourceIso A j F).hom ≫
      ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).map
        h.hom)

attribute [local irreducible] openComparisonRestrictionIso supportComparisonOpenSourceIso


private lemma supportComparisonOpenUnitForward
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app G) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) V).unit.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj G) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) V).map
          ((comparisonPullbackOpenUnitGamma A j).hom.app G) := by
  let E := Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j
  let P := openImmersionRestriction (ModuleCat.{u + 1} A) j
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) V
  let z : E.obj G ⟶ R.obj
      (P.obj ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj G)) :=
    E.map ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app G)
  have hu := comparisonPullbackOpenUnit A j G
  change z ≫ 𝟙 _ ≫ R.map ((comparisonPullbackOpenUnitGamma A j).inv.app G) = _ at hu
  simp only [Category.id_comp] at hu
  change z = _
  calc
    z = (z ≫ R.map ((comparisonPullbackOpenUnitGamma A j).inv.app G)) ≫
        R.map ((comparisonPullbackOpenUnitGamma A j).hom.app G) := by
      rw [Category.assoc, ← R.map_comp, Iso.inv_hom_id_app]
      exact (Category.comp_id z).symm.trans
        (congrArg (fun q ↦ z ≫ q)
          (R.map_id (P.obj ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj G))).symm)
    _ = _ := congrArg (fun q ↦ q ≫
      R.map ((comparisonPullbackOpenUnitGamma A j).hom.app G)) hu


attribute [local irreducible] supportComparisonAugmentation
  supportComparisonDerivedResolutionMap supportComparisonOpenResolutionMap
  derivedComparisonAdjunctionPlus

set_option maxHeartbeats 800000 in
-- The dependent normalization and naturality clauses need additional elaboration heartbeats.
/-- Open restriction preserves the given augmented injective resolution, the actual
ordinary unit and augmentation equalities, section complexes and restriction arrows,
and their naturality in every compatible chain map. The computation isomorphisms
are fixed by their equations with the right-derived comparison alpha.

Source: Stacks Project, sites.tex, Tag 03CF; proetale.tex, Tags 099V and 09B1
(blueprint: lem-pur-open-restriction-comparison-augmentation).

Proof:
1. An open immersion is etale (`lem-weil-pbc-open-immersion-etale`). The canonical
restriction identification of `lem-pur-comparison-pullback-open-unit` and exactness
and injective preservation of `lem-weil-pbc-proetale-restriction-injectives` show
that the restricted complex has injective terms and the same lower bound.
`lem-weil-pbc-exact-functor-complex-cohomology` preserves the quasi-isomorphism;
precomposition by beta and the degree-zero source identification preserves it too.
2. In `lem-pur-comparison-pullback-open-unit`, a is beta inverse and c is the
identity on sections. Compose its unit equation with nu_*(beta) and cancel.
This is exactly the ordinary unit equality below, with the prescribed beta.
3. Direct image commutes literally with restriction. Expand the definition of h_V,
apply functoriality and step 2, to obtain the expanded augmentation and its equality
to restriction of a (transporting the degree-zero source by singleMapHomologicalComplex).
4. Apply `lem-pur-support-comparison-common-injectives` on V to this very h_V.
It gives the etale injective resolution and the canonical derived computation theta,
characterized by theta followed by R(Qh_V) = alpha, with Qa_V theta the derived unit.
Evaluation on W is literally J(W over T), including its differential; every restriction
arrow is the same arrow over T (`lem-pur-comparison-pullback-open-unit`).
5. Restrict t h = h' nu^*(f) and use naturality of beta to obtain the first chain-map
identity. Naturality of the ordinary unit gives nu_*(t_V) a_V = a'_V f_V.
6. The module-sheaf category is Grothendieck abelian
(`lem-weil-pbc-ring-sheaves-grothendieck`) and has enough injectives
(`lem-sp-grothendieck-enough-injectives`). For the canonical comparison alpha of
`lem-weil-pbc-right-derived-plus-injective`, alpha_J and alpha_J' are invertible.
Write theta = alpha_J followed by R(Qh_V) inverse, and similarly for theta'.
Naturality of alpha and the chain-map identity in step 5 imply
Q(nu_* t_V) theta' = theta R(nu^* f_V), the final square below. -/
theorem supportComparisonOpenRestrictionAugmentation
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J) :
    QuasiIso h.hom → (∀ n : ℤ, Injective (J.obj.X n)) →
    QuasiIso (supportComparisonOpenResolutionMap A j F J h).hom ∧
    (∀ n : ℤ, Injective (((openImmersionRestriction (ModuleCat.{u + 1} A)
      j).mapCochainComplexPlus.obj J).obj.X n)) ∧
    (comparisonLowerStar (ModuleCat.{u + 1} A) V).mapCochainComplexPlus.obj
      ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J) =
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J) ∧
    (∀ n : ℤ, Injective (((comparisonLowerStar (ModuleCat.{u + 1} A) V).mapCochainComplexPlus.obj
      ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J)).obj.X n)) ∧
    QuasiIso (supportComparisonAugmentation V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1}
      A) j).obj F) ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J)
      (supportComparisonOpenResolutionMap A j F J h)) ∧
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map ((comparisonAdjunction
      (ModuleCat.{u + 1} A) T).unit.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) V).unit.app ((Etale.openImmersionRestriction
        (ModuleCat.{u + 1} A) j).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) V).map ((comparisonPullbackOpenUnitGamma A
          j).hom.app F) ∧
    (supportComparisonAugmentation V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
      F) ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J)
      (supportComparisonOpenResolutionMap A j F J h)) =
      (NatTrans.mapHomologicalComplex (V.proEtaleSiteComparisonModules A).unit (.up ℤ)).app
        (supportComparisonSource V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
          F)).obj ≫
      ((comparisonLowerStar (ModuleCat.{u + 1} A) V).mapHomologicalComplex (.up ℤ)).map
        (supportComparisonOpenSourceIso A j F).hom ≫
      ((comparisonLowerStar (ModuleCat.{u + 1} A) V).mapHomologicalComplex (.up ℤ)).map
        (((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).map
          h.hom) ∧
    (supportComparisonAugmentation V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
      F) ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J)
      (supportComparisonOpenResolutionMap A j F J h)) =
      ((HomologicalComplex.singleMapHomologicalComplex (Etale.openImmersionRestriction (ModuleCat.{u
      + 1} A) j) (.up ℤ) 0).app F).inv ≫ ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A)
      j).mapHomologicalComplex (.up ℤ)).map (supportComparisonAugmentation T A F J h) ∧
    (∀ W : V.Etale,
      (((sheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (op W)).mapHomologicalComplex
        (.up ℤ)).obj (((Etale.openImmersionRestriction (ModuleCat.{u + 1} A)
          j).mapCochainComplexPlus.obj
          ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J)).obj) =
        (((sheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (op ((Scheme.toProEt T).obj
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj W)))).mapHomologicalComplex
          (.up ℤ)).obj J.obj ∧
      (((sheafSections (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)).obj
          (op ((Scheme.toProEt V).obj W))).mapHomologicalComplex (.up ℤ)).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J).obj =
        (((sheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (op ((Scheme.toProEt T).obj
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj W)))).mapHomologicalComplex
          (.up ℤ)).obj J.obj) ∧
    (∀ (W₁ W₂ : V.Etale) (b : W₁ ⟶ W₂) (n : ℤ),
      (((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J)).obj.X
        n).obj.map b.op =
        (J.obj.X n).obj.map
          ((Scheme.toProEt T).map
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map b)).op ∧
      (((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J).obj.X
        n).obj.map ((Scheme.toProEt V).map b).op =
        (J.obj.X n).obj.map
          ((Scheme.toProEt T).map
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map b)).op) ∧
    (∃ θ : DerivedCategory.Plus.Q.obj ((comparisonLowerStar (ModuleCat.{u + 1} A)
      V).mapCochainComplexPlus.obj ((openImmersionRestriction (ModuleCat.{u + 1} A)
      j).mapCochainComplexPlus.obj J)) ≅ (comparisonLowerStar (ModuleCat.{u + 1} A)
      V).rightDerivedFunctorPlus.obj ((comparisonUpperStar (ModuleCat.{u + 1} A)
      V).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj (supportComparisonSource V A
      ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F)))),
      θ.hom ≫ supportComparisonDerivedResolutionMap V A ((Etale.openImmersionRestriction
        (ModuleCat.{u + 1} A) j).obj F) ((openImmersionRestriction (ModuleCat.{u + 1} A)
        j).mapCochainComplexPlus.obj J) (supportComparisonOpenResolutionMap A j F J h) =
        (comparisonLowerStar (ModuleCat.{u + 1} A) V).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj ((openImmersionRestriction (ModuleCat.{u + 1} A)
        j).mapCochainComplexPlus.obj J)) ∧
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk (supportComparisonAugmentation V A
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) ((openImmersionRestriction
        (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J) (supportComparisonOpenResolutionMap A
        j F J h))) ≫ θ.hom = (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) V).unit.app
        (DerivedCategory.Plus.Q.obj (supportComparisonSource V A ((Etale.openImmersionRestriction
        (ModuleCat.{u + 1} A) j).obj F))) ∧
      ∀ (F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (J' : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
        (h' : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
          (supportComparisonSource T A F') ⟶ J')
        (f : F ⟶ F') (t : J ⟶ J'),
        QuasiIso h'.hom → (∀ n : ℤ, Injective (J'.obj.X n)) →
        h ≫ t = (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.map
          (ObjectProperty.homMk ((CochainComplex.singleFunctor _ 0).map f)) ≫ h' →
        (supportComparisonOpenResolutionMap A j F J h) ≫ ((openImmersionRestriction (ModuleCat.{u +
          1} A) j).mapCochainComplexPlus.map t) = (comparisonUpperStar (ModuleCat.{u + 1} A)
          V).mapCochainComplexPlus.map ((ObjectProperty.homMk ((CochainComplex.singleFunctor _
          0).map ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map f))) :
          supportComparisonSource V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
          F) ⟶ supportComparisonSource V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A)
          j).obj F')) ≫ (supportComparisonOpenResolutionMap A j F' J' h') ∧
        (supportComparisonAugmentation V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A)
          j).obj F) ((openImmersionRestriction (ModuleCat.{u + 1} A) j).mapCochainComplexPlus.obj J)
          (supportComparisonOpenResolutionMap A j F J h)) ≫ ((comparisonLowerStar (ModuleCat.{u + 1}
          A) V).mapHomologicalComplex (.up ℤ)).map ((openImmersionRestriction (ModuleCat.{u + 1} A)
          j).mapCochainComplexPlus.map t).hom =
          ((CochainComplex.singleFunctor _ 0).map ((Etale.openImmersionRestriction (ModuleCat.{u +
            1} A) j).map f)) ≫ (supportComparisonAugmentation V A ((Etale.openImmersionRestriction
            (ModuleCat.{u + 1} A) j).obj F') ((openImmersionRestriction (ModuleCat.{u + 1} A)
            j).mapCochainComplexPlus.obj J') (supportComparisonOpenResolutionMap A j F' J' h')) ∧
        ∃ θ' : DerivedCategory.Plus.Q.obj ((comparisonLowerStar (ModuleCat.{u + 1} A)
          V).mapCochainComplexPlus.obj ((openImmersionRestriction (ModuleCat.{u + 1} A)
          j).mapCochainComplexPlus.obj J')) ≅ (comparisonLowerStar (ModuleCat.{u + 1} A)
          V).rightDerivedFunctorPlus.obj ((comparisonUpperStar (ModuleCat.{u + 1} A)
          V).mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj (supportComparisonSource V A
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F')))),
          θ'.hom ≫ supportComparisonDerivedResolutionMap V A ((Etale.openImmersionRestriction
            (ModuleCat.{u + 1} A) j).obj F') ((openImmersionRestriction (ModuleCat.{u + 1} A)
            j).mapCochainComplexPlus.obj J') (supportComparisonOpenResolutionMap A j F' J' h') =
            (comparisonLowerStar (ModuleCat.{u + 1} A) V).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj ((openImmersionRestriction (ModuleCat.{u + 1} A)
            j).mapCochainComplexPlus.obj J')) ∧
          DerivedCategory.Plus.Q.map ((comparisonLowerStar (ModuleCat.{u + 1} A)
            V).mapCochainComplexPlus.map ((openImmersionRestriction (ModuleCat.{u + 1} A)
            j).mapCochainComplexPlus.map t)) ≫ θ'.hom =
            θ.hom ≫ (comparisonLowerStar (ModuleCat.{u + 1} A) V).rightDerivedFunctorPlus.map
              ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlus.map
                (DerivedCategory.Plus.Q.map ((ObjectProperty.homMk ((CochainComplex.singleFunctor _
                0).map ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map f))) :
                supportComparisonSource V A ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A)
                j).obj F) ⟶ supportComparisonSource V A ((Etale.openImmersionRestriction
                (ModuleCat.{u + 1} A) j).obj F'))))) := by
  intro hh hJ
  let E := Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j
  let P := openImmersionRestriction (ModuleCat.{u + 1} A) j
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) V
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) V
  let FV := E.obj F
  let JV := P.mapCochainComplexPlus.obj J
  let k := supportComparisonOpenResolutionMap A j F J h
  have hlim : PreservesFiniteLimits P := by
    unfold P openImmersionRestriction localizationRestriction
    infer_instance
  have hcolim : PreservesFiniteColimits P := by
    have := (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint
    exact inferInstance
  have hinj : ∀ n : ℤ, Injective (JV.obj.X n) := fun n ↦ by
    change Injective ((localizationRestriction (ModuleCat.{u + 1} A) j
      (inferInstance : WeaklyEtale j)).obj (J.obj.X n))
    exact Functor.PreservesInjectiveObjects.injective_obj (F :=
      localizationRestriction (ModuleCat.{u + 1} A) j inferInstance) (hJ n)
  have : QuasiIso h.hom := hh
  have hk : QuasiIso k.hom := by
    unfold k supportComparisonOpenResolutionMap
    change QuasiIso ((supportComparisonOpenSourceIso A j F).hom ≫
      (P.mapHomologicalComplex (.up ℤ)).map h.hom)
    infer_instance
  obtain ⟨hRI, ha, ⟨θ, hθ, hunit⟩, _⟩ :=
    (supportComparisonCommonInjectives V A FV).2 JV k hk hinj
  refine And.intro hk ?_
  refine And.intro hinj ?_
  refine And.intro rfl ?_
  refine And.intro hRI ?_
  refine And.intro ha ?_
  refine And.intro (supportComparisonOpenUnitForward A j F) ?_
  refine And.intro ?_ ?_
  · unfold supportComparisonAugmentation supportComparisonOpenResolutionMap
    change _ ≫ (R.mapHomologicalComplex (.up ℤ)).map
      ((supportComparisonOpenSourceIso A j F).hom ≫
        (P.mapHomologicalComplex (.up ℤ)).map h.hom) = _
    rw [Functor.map_comp]
  refine And.intro ?_ ?_
  · let δ : (supportComparisonSource V A FV).obj ⟶
        (E.mapHomologicalComplex (.up ℤ)).obj (supportComparisonSource T A F).obj :=
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app F).inv
    let γ := (NatIso.mapHomologicalComplex (comparisonPullbackOpenUnitGamma A j)
      (.up ℤ)).hom.app (supportComparisonSource T A F).obj
    let η := NatTrans.mapHomologicalComplex (V.proEtaleSiteComparisonModules A).unit (.up ℤ)
    unfold supportComparisonAugmentation supportComparisonOpenResolutionMap
    unfold supportComparisonOpenSourceIso
    apply HomologicalComplex.hom_ext
    intro n
    let d := δ.f n
    let g := ((comparisonPullbackOpenUnitGamma A j).hom.app
      ((supportComparisonSource T A F).obj.X n))
    let e := (comparisonAdjunction (ModuleCat.{u + 1} A) V).unit
    have hn := e.naturality d
    have hu := supportComparisonOpenUnitForward A j ((supportComparisonSource T A F).obj.X n)
    change e.app _ ≫ R.map (L.map d ≫ g ≫ P.map (h.hom.f n)) =
      d ≫ E.map ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        ((supportComparisonSource T A F).obj.X n) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} A) T).map (h.hom.f n))
    change d ≫ e.app _ = e.app _ ≫ R.map (L.map d) at hn
    simp only [Functor.map_comp, ← Category.assoc]
    erw [← hn]
    simp only [Category.assoc]
    erw [← Category.assoc (e.app _) (R.map g), ← hu]
    rfl
  refine And.intro (fun W ↦ ⟨rfl, rfl⟩) ?_
  refine And.intro (fun W₁ W₂ b n ↦ ⟨rfl, rfl⟩) ?_
  refine ⟨θ, hθ, hunit, ?_⟩
  intro F' J' h' f t hh' hJ' ht
  let FV' := E.obj F'
  let JV' := P.mapCochainComplexPlus.obj J'
  let k' := supportComparisonOpenResolutionMap A j F' J' h'
  have hinj' : ∀ n : ℤ, Injective (JV'.obj.X n) := fun n ↦ by
    change Injective ((localizationRestriction (ModuleCat.{u + 1} A) j
      (inferInstance : WeaklyEtale j)).obj (J'.obj.X n))
    exact Functor.PreservesInjectiveObjects.injective_obj (F :=
      localizationRestriction (ModuleCat.{u + 1} A) j inferInstance) (hJ' n)
  have : QuasiIso h'.hom := hh'
  have hk' : QuasiIso k'.hom := by
    unfold k' supportComparisonOpenResolutionMap
    change QuasiIso ((supportComparisonOpenSourceIso A j F').hom ≫
      (P.mapHomologicalComplex (.up ℤ)).map h'.hom)
    infer_instance
  let fV : supportComparisonSource V A FV ⟶ supportComparisonSource V A FV' :=
    ObjectProperty.homMk ((HomologicalComplex.single _ (.up ℤ) 0).map (E.map f))
  let tV := P.mapCochainComplexPlus.map t
  have hs : (supportComparisonOpenSourceIso A j F).hom ≫
      (P.mapHomologicalComplex (.up ℤ)).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
          (.up ℤ) |>.map ((HomologicalComplex.single _ (.up ℤ) 0).map f)) =
      (L.mapCochainComplexPlus.map fV).hom ≫
        (supportComparisonOpenSourceIso A j F').hom := by
    unfold supportComparisonOpenSourceIso
    let δ := (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).inv
    let γ := (NatIso.mapHomologicalComplex (comparisonPullbackOpenUnitGamma A j)
      (.up ℤ)).hom
    apply HomologicalComplex.hom_ext
    intro n
    let sf := (HomologicalComplex.single _ (.up ℤ) 0).map f
    let g := (comparisonPullbackOpenUnitGamma A j).hom
    have hn := g.naturality (sf.f n)
    have hd := congrArg (fun z ↦ L.map (z.f n)) (δ.naturality f)
    change (L.map ((δ.app F).f n) ≫ g.app _) ≫
        P.map ((comparisonUpperStar (ModuleCat.{u + 1} A) T).map (sf.f n)) =
      L.map (((HomologicalComplex.single _ (.up ℤ) 0).map (E.map f)).f n) ≫
        (L.map ((δ.app F').f n) ≫ g.app _)
    change L.map (((HomologicalComplex.single _ (.up ℤ) 0).map (E.map f)).f n ≫
        (δ.app F').f n) = L.map ((δ.app F).f n ≫ E.map (sf.f n)) at hd
    change L.map (E.map (sf.f n)) ≫ g.app _ =
      g.app _ ≫ P.map ((comparisonUpperStar (ModuleCat.{u + 1} A) T).map (sf.f n)) at hn
    erw [Category.assoc, ← hn, ← Category.assoc, ← L.map_comp, ← hd,
      L.map_comp, Category.assoc]
  have hkt : k ≫ tV = L.mapCochainComplexPlus.map fV ≫ k' := by
    apply ObjectProperty.hom_ext
    unfold k k' supportComparisonOpenResolutionMap
    have ht' := congrArg (fun z ↦ (P.mapHomologicalComplex (.up ℤ)).map z.hom) ht
    change (P.mapHomologicalComplex (.up ℤ)).map (h.hom ≫ t.hom) =
      (P.mapHomologicalComplex (.up ℤ)).map
        (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
          (.up ℤ)).map ((HomologicalComplex.single _ (.up ℤ) 0).map f) ≫ h'.hom) at ht'
    change (supportComparisonOpenSourceIso A j F).hom ≫
      (P.mapHomologicalComplex (.up ℤ)).map h.hom ≫
        (P.mapHomologicalComplex (.up ℤ)).map t.hom = _
    erw [← Functor.map_comp, ht', Functor.map_comp,
      ← Category.assoc, hs, Category.assoc]
    rfl
  have hat : supportComparisonAugmentation V A FV JV k ≫
      (R.mapHomologicalComplex (.up ℤ)).map tV.hom =
      fV.hom ≫ supportComparisonAugmentation V A FV' JV' k' := by
    have hn := (NatTrans.mapHomologicalComplex
      (V.proEtaleSiteComparisonModules A).unit (.up ℤ)).naturality fV.hom
    change fV.hom ≫ _ = _ ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((L.mapHomologicalComplex (.up ℤ)).map fV.hom) at hn
    have ht' := congrArg (fun z ↦ (R.mapHomologicalComplex (.up ℤ)).map z.hom) hkt
    change (R.mapHomologicalComplex (.up ℤ)).map (k.hom ≫ tV.hom) =
      (R.mapHomologicalComplex (.up ℤ)).map
        ((L.mapHomologicalComplex (.up ℤ)).map fV.hom ≫ k'.hom) at ht'
    unfold supportComparisonAugmentation
    change _ ≫ (R.mapHomologicalComplex (.up ℤ)).map k.hom ≫
      (R.mapHomologicalComplex (.up ℤ)).map tV.hom = _
    erw [← Functor.map_comp, ht', Functor.map_comp, ← Category.assoc,
      ← hn, Category.assoc]
  obtain ⟨_, _, ⟨θ', hθ', hunit'⟩, _⟩ :=
    (supportComparisonCommonInjectives V A FV').2 JV' k' hk' hinj'
  refine ⟨hkt, hat, θ', hθ', ?_⟩
  let a : supportComparisonSource V A FV ⟶ R.mapCochainComplexPlus.obj JV :=
    ObjectProperty.homMk (supportComparisonAugmentation V A FV JV k)
  have : QuasiIso a.hom := ha
  have hqa : IsIso (DerivedCategory.Plus.Q.map a) := by
    change IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map a))
    apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ha
  apply (cancel_epi (DerivedCategory.Plus.Q.map a)).1
  have hat' : a ≫ R.mapCochainComplexPlus.map tV =
      fV ≫ ObjectProperty.homMk (supportComparisonAugmentation V A FV' JV' k') := by
    apply ObjectProperty.hom_ext
    exact hat
  rw [← Category.assoc, ← Functor.map_comp, hat', Functor.map_comp, Category.assoc,
    hunit', ← Category.assoc, hunit]
  exact (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) V).unit.naturality
    (DerivedCategory.Plus.Q.map fV)
end AlgebraicGeometry.ProEtale
