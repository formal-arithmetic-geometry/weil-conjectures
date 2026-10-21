/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact inverse image and local derived restriction

Source: Stacks Project, derived.tex, Tag 015F; sites-modules.tex, Tags 03D2, 03DA,
04IX; Bhatt--Scholze, Proposition 6.8.11(3).
(blueprint: lem-weil-pbc-local-derived-restriction-comparisons).

## Main declarations

* `inverseImage_exact`: exactness over the actual inverse-image ring.
* `comparison`: the prescribed localization-representative comparison.
* `comparisons`: its functorial cohomology and shifted-single normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wT wS wU

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEtaleLocalRestriction

/-- Underlying ring sheaf of the specified commutative coefficient sheaf.
This is only a transparent notation for sheafCompose with forget₂, not a new ring.
Source: Stacks, Tag 03DA (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
abbrev ring {T : Scheme.{u}} (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- The actual inverse-image coefficient ring, with commutativity forgotten.
Source: Stacks, Tag 03D2 (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
abbrev inverseRing {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  ring ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)

/-- Module restriction to the slice, with its actual restricted coefficient ring.
Source: Stacks, Tag 04IX (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
abbrev restriction {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :=
  SheafOfModules.overFunctor.{u + 1} (inverseRing g R) U

/-- Actual-ring inverse image is additive and exact for every scheme morphism.
Source: Stacks, Tags 03D2, 03DA and 010N
(blueprint: lem-weil-pbc-local-derived-restriction-comparisons).
Proof: the module inverse-image comparison identifies its underlying abelian sheaf
with abelian inverse image, preserving the scalar action. Site inverse image is exact.
The faithful exact module forgetful functors reflect zero homology: a module with zero
underlying sheaf has zero identity by faithfulness. They therefore reflect short exact
sequences and addition of maps. Apply the abelian exact-functor criterion. This uses
only the actual inverse-image ring, without extension to another coefficient ring.
DAG inputs: lem-weil-pbc-proetale-module-inverse-image-comparison,
lem-weil-pbc-left-exact-site-inverse-image-tensor,
lem-weil-pbc-module-sheaves-colimits-forgetful, and
lem-sp-exact-functor-preserves-homology. -/
theorem inverseImage_exact {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive ∧
      PreservesFiniteLimits (proEtaleModuleInverseImage g R) ∧
      PreservesFiniteColimits (proEtaleModuleInverseImage g R) := by
  let F := proEtaleModuleInverseImage g R
  let V := SheafOfModules.toSheaf.{u + 1} (inverseRing g R)
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} (ring R)) :=
    (moduleSheaves_colimits_forgetful (ring R)).2.2.1
  let : PreservesFiniteColimits V :=
    (moduleSheaves_colimits_forgetful (inverseRing g R)).2.2.1
  let : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).Additive := ⟨by
    intros
    ext W
    rfl⟩
  let : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).Additive :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).left_adjoint_additive
  let : RepresentablyFlat (proEtaleBaseChange g) := flat_of_preservesFiniteLimits _
  let : PreservesFiniteLimits (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) :=
    inferInstance
  let : PreservesColimitsOfSize.{0, 0}
      (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
  obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison g R).1
  let : (F ⋙ V).Additive := Functor.additive_of_iso e.symm
  let : F.Additive := Functor.additive_of_comp_faithful F V
  let : ReflectsFiniteLimits V := reflectsFiniteLimits_of_reflectsIsomorphisms V
  let : PreservesFiniteLimits (F ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F V
  let : ReflectsFiniteColimits V :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  let : PreservesFiniteColimits (F ⋙ V) := preservesFiniteColimits_of_natIso e.symm
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F V
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity supplied by the actual-ring exactness assertion.
Source: Stacks, Tag 03DA (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance inverseImage_additive {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g R).Additive :=
  (inverseImage_exact g R).1

/-- Preservation of finite limits supplied by actual-ring exactness.
Source: Stacks, Tag 03DA (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance inverseImage_preservesFiniteLimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleModuleInverseImage g R) :=
  (inverseImage_exact g R).2.1

/-- Preservation of finite colimits supplied by actual-ring exactness.
Source: Stacks, Tag 03DA (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance inverseImage_preservesFiniteColimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleModuleInverseImage g R) :=
  (inverseImage_exact g R).2.2

/-- Additivity of the existing slice restriction, without a site-size identification.
Source: Stacks, Tag 04IX (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance restriction_additive {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    (restriction g R U).Additive :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).1

/-- Left exactness of existing slice restriction.
Source: Stacks, Tag 04IX (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance restriction_preservesFiniteLimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteLimits (restriction g R U) :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).2.1

/-- Right exactness of existing slice restriction.
Source: Stacks, Tag 04IX (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
instance restriction_preservesFiniteColimits {S T : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt) :
    PreservesFiniteColimits (restriction g R U) :=
  (ringedOverFunctor_exactGeneral (inverseRing g R) U).2.2

variable {S T : Scheme.{u}} (g : S ⟶ T)
  (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
  [HasDerivedCategory.{wT} (SheafOfModules.{u + 1} (ring R))]
  [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (inverseRing g R))]
  [HasDerivedCategory.{wU} (SheafOfModules.{u + 1} ((inverseRing g R).over U))]

/-- The specified representative-normalized comparison: first apply derived restriction
of the inverse representative isomorphism, then the exact localization factor.
Source: Stacks, Tag 015F (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
def comparison (K : DerivedCategory (SheafOfModules.{u + 1} (ring R))) :
    (restriction g R U).mapDerivedCategory.obj
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) ≅
      ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) :=
  (restriction g R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K)).symm ≪≫
    (restriction g R U).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K))

/-- Functorial local restriction with normalized cohomology and shifted-single comparisons.
Source: Stacks, Tag 015F; Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-local-derived-restriction-comparisons).
Proof:
1. Actual-ring module inverse image is exact by the abelian comparison and faithful
   exact forgetful functors (inverseImage_exact). Slice restriction preserves finite
   limits and colimits; its universe-independent interface applies to this small site.
2. Apply exact-functor localization separately to F and G. It gives DF, DG and their
   factorization isomorphisms, commuting with every integer shift, without boundedness.
3. For X = DF(K), use the chosen representative C and epsilon : Q(C) ≅ X. The comparison
   is DG(epsilon.symm) followed by the localization factor at C, exactly comparison.
4. Define L on objects by the recorded representative restriction, and on maps by
   alpha.inv followed by DG(DF(a)) followed by alpha.hom. Cancellation proves the functor
   laws and naturality, and transports inverses. For any other representative B, replace
   epsilon by Q(B) ≅ X; naturality of the localization factor identifies the comparisons
   on chain maps and inverted quasi-isomorphisms, hence on all derived morphisms.
5. Exact functors commute with complex cohomology by the kernel/image comparison. Descend
   that comparison through localization. Compose G(h_F), h_G and H(alpha); their naturality
   gives the displayed natural cohomology isomorphism and its compatibility with alpha.
6. On degree-zero complexes use the exact-functor single comparison twice. On a shift r,
   use the two derived shift comparisons and shift the single comparison. Compose with
   alpha.inv to obtain the specified natural shifted-single comparison.
7. On the representative M[0][r] these comparisons use the same kernels and images:
   identity on GFM in degree -r and zero in the other degrees. The termwise shifts have
   differential (-1)^r GF(d), for either sign of r. Transport by step 4 identifies these
   comparisons with the chosen representative convention.
DAG inputs: def-weil-proetale-inverse-image, def-pur-localized-ringed-site,
lem-weil-pbc-finite-type-restriction-exact,
lem-weil-pbc-exact-functor-derived-factorization,
def-weil-pbc-ringed-site-derived-restriction, def-weil-abstract-derived-category, and
lem-weil-pbc-exact-functor-complex-cohomology. -/
theorem comparisons :
    ∃ (L : DerivedCategory (SheafOfModules.{u + 1} (ring R)) ⥤
        DerivedCategory (SheafOfModules.{u + 1} ((inverseRing g R).over U)))
      (hobj : ∀ K, L.obj K =
        ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
          ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K))
      (α : (proEtaleModuleInverseImage g R).mapDerivedCategory ⋙
        (restriction g R U).mapDerivedCategory ≅ L),
      (∀ K, α.app K ≪≫ eqToIso (hobj K) = comparison g R U K) ∧
      (∀ {K K'} (a : K ⟶ K'), L.map a =
        α.inv.app K ≫ (restriction g R U).mapDerivedCategory.map
          ((proEtaleModuleInverseImage g R).mapDerivedCategory.map a) ≫ α.hom.app K') ∧
      (∀ q : ℤ, ∃ c :
        DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} (ring R)) q ⋙
            proEtaleModuleInverseImage g R ⋙ restriction g R U ≅
          L ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q,
        ∀ K, c.hom.app K =
          (restriction g R U).map
              (((proEtaleModuleInverseImage g R).mapDerivedCategoryHomologyFunctorIso q).hom.app
                K) ≫
            ((restriction g R U).mapDerivedCategoryHomologyFunctorIso q).hom.app
              ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) ≫
            (DerivedCategory.homologyFunctor
              (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q).map (α.hom.app K)) ∧
      (∀ r : ℤ, ∃ s :
        DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (ring R)) 0 ⋙
            shiftFunctor _ r ⋙ L ≅
          proEtaleModuleInverseImage g R ⋙ restriction g R U ⋙
            DerivedCategory.singleFunctor
              (SheafOfModules.{u + 1} ((inverseRing g R).over U)) 0 ⋙ shiftFunctor _ r,
        ∀ M, s.hom.app M =
          α.inv.app ((DerivedCategory.singleFunctor _ 0).obj M⟦r⟧) ≫
            (restriction g R U).mapDerivedCategory.map
              (((proEtaleModuleInverseImage g R).mapDerivedCategory.commShiftIso r).hom.app
                ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
            ((restriction g R U).mapDerivedCategory.commShiftIso r).hom.app
              ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
            (shiftFunctor _ r).map
              ((restriction g R U).mapDerivedCategory.map
                  (((proEtaleModuleInverseImage g R).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
                ((restriction g R U).mapDerivedCategorySingleFunctor 0).hom.app
                  ((proEtaleModuleInverseImage g R).obj M))) := by
  let F := proEtaleModuleInverseImage g R
  let G := restriction g R U
  let D := F.mapDerivedCategory ⋙ G.mapDerivedCategory
  let obj := fun K ↦ ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
    (F.mapDerivedCategory.obj K)
  let L := D.copyObj obj (comparison g R U)
  let α := D.isoCopyObj obj (comparison g R U)
  refine ⟨L, (fun _ ↦ rfl), α, ?_, ?_, ?_, ?_⟩
  · intro K
    simp [α, Functor.isoCopyObj]
  · intro K K' a
    rfl
  · intro q
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q
    refine ⟨Functor.isoWhiskerRight (F.mapDerivedCategoryHomologyFunctorIso q) G ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso q) ≪≫
      Functor.isoWhiskerRight α H, ?_⟩
    intro K
    rfl
  · intro r
    let single := DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (ring R)) 0
    let sF := F.mapDerivedCategorySingleFunctor 0
    let sG := G.mapDerivedCategorySingleFunctor 0
    refine ⟨Functor.isoWhiskerLeft (single ⋙ shiftFunctor _ r) α.symm ≪≫
      Functor.isoWhiskerLeft single
        (Functor.isoWhiskerRight (F.mapDerivedCategory.commShiftIso r) G.mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft F.mapDerivedCategory (G.mapDerivedCategory.commShiftIso r)) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight sF G.mapDerivedCategory ≪≫ Functor.isoWhiskerLeft F sG)
        (shiftFunctor _ r), ?_⟩
    intro M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.comp_obj, Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.Scheme.ProEtaleLocalRestriction
