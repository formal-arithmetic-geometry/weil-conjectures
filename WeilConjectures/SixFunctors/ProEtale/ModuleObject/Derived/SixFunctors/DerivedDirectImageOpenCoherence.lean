/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageAssociativity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionMixed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-! Assembly of the four independent coherence arguments. -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] lowerStar upperStar lowerStarComp upperStarComp
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem derived_comp_evaluation
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D] [HasDerivedCategory.{v} E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((F ⋙ G).rightDerivedFunctorObjQIso I).hom := by
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj I
  have hm : ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K) =
      𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K), Iso.hom_inv_id_app]
    simp [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  have hc : (F ⋙ G).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
        G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
          G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
    simp only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso, Functor.rightDerivedNatTrans_app,
      Functor.whiskerRight_app, NatTrans.id_app, DerivedCategory.Qh.map_id,
      Category.id_comp, Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, hm, Category.comp_id, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    erw [Category.id_comp]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_inv, Functor.map_comp, Category.assoc]
  have hn := (Functor.rightDerivedFunctorCompIso F G).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).inv.app I)
  dsimp only [Functor.comp_map] at hn
  have hd : (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (DerivedCategory.quotientCompQhIso D).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) = 𝟙 _ := Iso.hom_inv_id_app _ _
  simp only [← G.rightDerivedFunctor.map_comp_assoc, hd]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  congr 1
  rw [← cancel_epi ((F ⋙ G).rightDerivedFunctorUnit.app K),
    IsIso.hom_inv_id_assoc, reassoc_of% hc]
  dsimp only [K]
  erw [← G.rightDerivedFunctor.map_comp_assoc, IsIso.hom_inv_id]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  change G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
    inv (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I))) = 𝟙 _
  exact IsIso.hom_inv_id _

private theorem composition_normalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DirectImageCompositionNormalized Λ f g := by
  intro I hI
  dsimp only [directImageComposition, Iso.trans_hom, NatTrans.comp_app,
    Functor.rightDerivedFunctorNatIso, Iso.symm_hom]
  rw [Category.assoc, derived_comp_evaluation]
  exact Functor.rightDerivedFunctorNatTrans_app_Q_obj (lowerStarComp Λ f g).inv I


private theorem coherence_all (k : Type u) [Field k] : DirectImageOpenCoherence Λ k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros X Y Z T _ _ _ _ _ _ _ _ _ _ _ _ f g h
    exact ⟨composition_normalized Λ f.left g.left,
      derivedDirectImageAssociativity Λ f.left g.left h.left⟩
  · intros X Y X' Y' _ _ _ _ _ _ _ _ _ _ _ _ f j f' i _ _ _ sq
    exact derivedOpenRestrictionNormalization Λ sq
  · intros X Y X' Y' X'' Y'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      f j f' i j' f'' i' _ _ _ _ _ _ sq sq'
    exact derivedOpenRestrictionSuccessive Λ sq sq'
  · intros X Y Z X' Y' Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      f g f' g' i j a _ _ _ _ sqf sqg
    exact derivedOpenRestrictionMixed Λ sqf sqg

/-- Derived direct-image comparisons are associative and compatible with open restriction,
for E and for the finite-subextension-valued condensed algebraic closure.
The representative normalizations include identity scheme maps and identity open immersions:
under the canonical site identifications their section maps are identities.

Source: blueprint main-20261015, sk-thm-sf-comp-composition, Composition isomorphism and
Canonicity and associativity; Stacks Tags 08BJ, 070I, 070Y and 0D6E
(blueprint: lem-sfb-derived-direct-image-open-coherence).

Proof plan (the seven steps of the DAG node):
1. Identify internal modules with sheaves of modules over the section-ring sheaf using
   def-weil-pbc-internal-abelian-sheaf-module-equivalence. This preserves sections and
   actions. Exact pullback and its adjunction from sk-def-sfb-module-pushforward-pullback
   and sk-prop-sfb-cartesian-coefficients make every direct image preserve K-injectives
   by lem-weil-pbc-right-adjoint-preserves-kinjective. Exact open extension by zero from
   sk-def-sfb-module-lower-shriek makes open restriction preserve K-injectives as well.
   Resolutions exist by prop-pur-kinjective-resolutions-exist. Work on a single initial I.
2. In lem-weil-pbc-ringed-topoi-derived-pushforward-composition use the identity resolution
   of f_*I. Thus kappa is the class of the inverse underived lowerStarComp. This is the
   universal, unit-preserving derived comparison used in directImageComposition.
   The representative and transition formulas of lem-sf-kinjective-derived-map-computation
   make this computation natural and independent of I, including arbitrary resolutions.
3. For three direct images evaluate both bracketings in degree n at V over the target.
   Both identify the iterated fibre product with V times X. Their projections to V and X
   agree, hence the arrows agree by the fibre-product universal property. Applying the
   contravariant sections functor gives equal chain maps. The coefficient actions agree
   by lem-sfb-eta-comp; the module lifts of def-sfb-finite-lower-star-comp are faithful.
   Localization gives DirectImageCompositionAssociative with its canonical associator.
4. Apply lem-sfb-proetale-open-restriction-counit to the actual pulled-back ring sheaf.
   Transport coefficients through sk-prop-sfb-cartesian-coefficients, using alpha inverse.
   Its counit characterization identifies beta with directImageOpenRestriction, the mate
   of the canonical pullback square. The site object coprojections are bijections. On V,
   beta sends a section along openCoherenceSectionArrow, which fixes V and the source
   projection; this is the identity on I(V times X) under the fibre-product identification.
5. Open restriction of I is K-injective by step 1. Therefore both sides of rho are computed
   by the degreewise beta, which is invertible and commutes with differentials. This gives
   DirectImageRestrictionNormalized and identifies the derived mate with that class.
   Naturality for chain maps and independence under homotopy equivalences follow from
   lem-sf-kinjective-derived-map-computation, so no boundedness hypothesis is needed.
6. For successive opens evaluate both maps in degree n at a test object V. Both are the
   identity on I(V times X) under the displayed coprojections. Iterated coefficient
   restriction is restriction of the same ring sheaf, and both fibre-product maps have
   the same projections. Thus they agree degreewise and after localization. For an
   identity open or identity scheme map the same section computation is the identity.
7. In the composition/restriction square, f_*I and every restricted image remain
   K-injective by step 1. The left path splits the direct image, restricts g, then f;
   the right path first restricts the composite and then splits it. On V each sends a
   section over V times X to that same section on the iterated fibre product. The
   projections to V and X agree, so the maps coincide. Localize and use the transition
   formulas from step 2. This proves DirectImageRestrictionComposition with all the
   specified coefficient actions and canonical fibre-product identifications.
-/
theorem derivedDirectImageOpenCoherence
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    DirectImageOpenCoherence (Profinite.continuousMapRingObj E.1) k ∧
      DirectImageOpenCoherence (Profinite.padicAlgClRingObj ℓ) k := by
  exact ⟨coherence_all _ k, coherence_all _ k⟩

end AlgebraicGeometry.ProEtale.CondensedRing
