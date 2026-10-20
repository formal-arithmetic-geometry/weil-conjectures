/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Paper.UnboundedProperOpenInterchange
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.Paper.ProEtaleProperOpenComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen

/-! # Coefficient and site naturality of proper/open interchange

Source: Stacks Project, Tags 0F7B and 0GL6; blueprint main-20261015,
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
existence, uniqueness and naturality
(blueprint: lem-sp-proper-open-coefficient-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable {U V W Z : Scheme.{u}}
  [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
  {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
  [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]

/-- The proper/open isomorphism from the recorded theorem, whose representative and
open adjunct determine it uniquely. Source: Stacks 0F7B
(blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (unboundedProperOpenInterchange A).choose_spec.choose k r p i sq.toCommSq

/-- The restriction isomorphism selected by its specified exchange and open-unit formula.
The hom component, rather than just its endpoints, is fixed by the recorded theorem.
Source: Stacks 0F7B (blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i) :
    D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
        D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]) :=
  (Functor.isoWhiskerLeft R((r)_*[ModuleCat.{u + 1} A])
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i).unit) ≪≫
    Functor.isoWhiskerRight (properOpenCoefficientInterchange A sq)
      D((i)^*[ModuleCat.{u + 1} A])).symm

/-- Canonical inclusion comparison for the target of proper/open interchange.
Source: Stacks 0F7B, exact extension and K-injective direct image
(blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientTargetPlus (A : Type (u + 1)) [CommRing A]
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
      ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E)).obj ≅
      R((p)_*[ModuleCat.{u + 1} A]).obj (D((k)_!open[ModuleCat.{u + 1} A]).obj E.obj) :=
  ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app
      ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E) ≪≫
    R((p)_*[ModuleCat.{u + 1} A]).mapIso
      (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app E)

/-- The specified etale interchange, expressed in the full bounded-below subcategories.
Full faithfulness of the inclusion transports the actual morphism, not just its objects.
Source: Stacks 0F7B (blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientInterchangePlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (i)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj
        ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≅
      (p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
        ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E) :=
  (DerivedCategory.Plus.ι (C := Sheaf Z.smallEtaleTopology
    (ModuleCat.{u + 1} A))).preimageIso
    (((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app
        ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≪≫
      D((i)_!open[ModuleCat.{u + 1} A]).mapIso
        (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app E) ≪≫
      (properOpenCoefficientInterchange A sq).app E.obj ≪≫
      (properOpenCoefficientTargetPlus (p := p) (k := k) A E).symm)

private def properOpenCoefficientInterchangePlusIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i) :
    (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus ⋙
        (i)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus ≅
      (k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus ⋙
        (p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus
        ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility
        D((i)_!open[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (properOpenCoefficientInterchange A sq) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.symm
        R((p)_*[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus
        ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm)

private lemma properOpenCoefficientInterchangePlusIso_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properOpenCoefficientInterchangePlusIso A sq).hom.app E =
      (properOpenCoefficientInterchangePlus A sq E).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp [properOpenCoefficientInterchangePlusIso, properOpenCoefficientInterchangePlus,
    properOpenCoefficientTargetPlus, Functor.preimageIso, Category.assoc]

/-- The exact same restriction exchange in bounded-below coordinates.
Source: Stacks 0F7B (blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientRestrictionPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj
        ((p)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj
          ((k)_!open[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.obj E)) ≅
      (r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E :=
  (DerivedCategory.Plus.ι (C := Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} A))).preimageIso
    (((i)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryPlusCompatibility.app _ ≪≫
      D((i)^*[ModuleCat.{u + 1} A]).mapIso
        (properOpenCoefficientTargetPlus (p := p) (k := k) A E) ≪≫
      (properOpenCoefficientRestriction A sq).app E.obj ≪≫
      (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.app E).symm)

private lemma properOpenCoefficientRestrictionPlus_inv
    (A : Type (u + 1)) [CommRing A] [Finite A] (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properOpenCoefficientRestrictionPlus A sq E).inv =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} A) i).unit.app
          ((r)_*[ModuleCat.{u + 1} A].rightDerivedFunctorPlus.obj E) ≫
        (i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.map
          (properOpenCoefficientInterchangePlus A sq E).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  rw [properOpenCoefficientRestrictionPlus, Functor.preimageIso_inv, Functor.map_preimage]
  rw [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
    Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  have hmap : DerivedCategory.Plus.ι.map
      ((i)^*[ModuleCat.{u + 1} A].mapDerivedCategoryPlus.map
        (properOpenCoefficientInterchangePlus A sq E).hom) =
      D((i)^*[ModuleCat.{u + 1} A]).map
        (DerivedCategory.Plus.ι.map (properOpenCoefficientInterchangePlus A sq E).hom) := rfl
  rw [hmap]
  rw [properOpenCoefficientInterchangePlus, Functor.preimageIso_hom, Functor.map_preimage]
  simp only [properOpenCoefficientRestriction, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  simp only [Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  erw [← reassoc_of% (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i).unit.naturality
      (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorPlusCompatibility.hom.app E)]
  rfl



/-- The coefficient-square composite through the B proper/open map.
The two scalar comparisons are the recorded summandwise maps, and the proper
coefficient arrow is the uniquely specified B-linear counit transpose.
Source: Stacks 0GL6 and 0F7B (blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenCoefficientComposite
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    (scalarExtension φ Z).obj
        (D((i)_!open[ModuleCat.{u + 1} A]).obj (R((r)_*[ModuleCat.{u + 1} A]).obj E)) ⟶
      R((p)_*[ModuleCat.{u + 1} B]).obj
        (D((k)_!open[ModuleCat.{u + 1} B]).obj ((scalarExtension φ U).obj E)) :=
  (openScalarExtension φ i).hom.app (R((r)_*[ModuleCat.{u + 1} A]).obj E) ≫
    D((i)_!open[ModuleCat.{u + 1} B]).map (finiteCoefficientDirectImageMap φ r E) ≫
    (properOpenCoefficientInterchange B sq).hom.app ((scalarExtension φ U).obj E)

/-- The transpose identity for the coefficient square.  This is the counit calculation
that remains after applying the proper direct-image adjunction; it is strictly weaker than
the coefficient-square equality and is the mate-pasting step of the blueprint.
Source: Stacks 0F7B and 0GL6; blueprint lem-sp-proper-open-coefficient-mate, proof Step 1.
(blueprint: lem-sp-proper-open-coefficient-mate-transposed).
Proof in words: expand the coefficient direct-image map as the adjoint transpose of
the scalar-extended counit, and expand the coefficient composite.  The tensor and
open-extension comparison maps reassociate the two paths to the same inverse-image
composite.  The proper/open interchange normalization and the mate-pasting identity
then identify their inverse proper-adjunction transposes. -/
theorem properOpen_coefficient_mate_transposed
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    (_hE : ∃ n : ℤ, E.IsGE n)
    (_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n) :
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p
    ((adj.homEquiv _ _).symm)
      ((scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
        finiteCoefficientDirectImageMap φ p
          (D((k)_!open[ModuleCat.{u + 1} A]).obj E) ≫
        R((p)_*[ModuleCat.{u + 1} B]).map
          ((openScalarExtension φ k).hom.app E)) =
    ((adj.homEquiv _ _).symm)
      (properOpenCoefficientComposite φ sq E) := by
  sorry


/-- The coefficient square, as equality of actual B-linear arrows in the unbounded
category. Source: Stacks 0F7B/0GL6; blueprint exceptional coefficient comparison,
existence, uniqueness and naturality (blueprint: lem-sp-proper-open-coefficient-mate).
Proof: write the tensor/pullback comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The definition of
finiteCoefficientDirectImageMap is the B-adjoint transpose of tensor of the A-counit.
The open comparisons are the summandwise tensor comparisons of lem-coef-etale-open-tensor.
The normalization in lem-amb-unbounded-proper-open-interchange identifies Gamma as
adjunct of inverse open exchange of def-kun-unbounded-exchange followed by inverse
open unit. Apply lem-weil-pbc-mate-pasting to the rectangle of the two proper
adjunctions, the two open adjunctions and scalar extension. Both displayed paths
transpose to the same inverse-image composite. Injectivity of the adjunction Hom
bijections gives the equation. This requires no flatness and no preservation of
bounded-below objects by scalar extension: the two lower bounds are separate. -/
theorem properOpen_coefficient_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    (_hE : ∃ n : ℤ, E.IsGE n)
    (_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n) :
    (scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
        finiteCoefficientDirectImageMap φ p (D((k)_!open[ModuleCat.{u + 1} A]).obj E) ≫
        R((p)_*[ModuleCat.{u + 1} B]).map ((openScalarExtension φ k).hom.app E) =
      properOpenCoefficientComposite φ sq E := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p
  have h := properOpen_coefficient_mate_transposed φ sq E _hE _hEB
  dsimp only at h
  exact (adj.homEquiv _ _).symm.injective h


/-- Naturality of both paths of the coefficient square in the input complex.
Source: Stacks 0F7B/0GL6 and blueprint exceptional coefficient comparison, naturality
(blueprint: lem-sp-proper-open-coefficient-mate).
Proof: finiteCoefficientDirectImageMap_naturality is naturality of the counit transpose.
The open tensor comparison and proper/open isomorphism are natural transformations.
Compose these three naturality identities to obtain the displayed identity for the
right-hand path. The coefficient-square equation identifies the left-hand path with
it at each endpoint. This is Step 3 of the node's proof, using
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
lem-amb-unbounded-proper-open-interchange. No flatness is used. -/
theorem properOpen_coefficient_mate_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) {E F : DerivedCategoryModule A U}
    (_hE : ∃ n : ℤ, E.IsGE n) (_hF : ∃ n : ℤ, F.IsGE n)
    (_hEB : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n)
    (_hFB : ∃ n : ℤ, ((scalarExtension φ U).obj F).IsGE n) (f : E ⟶ F) :
    (scalarExtension φ Z).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map (R((r)_*[ModuleCat.{u + 1} A]).map f)) ≫
        properOpenCoefficientComposite φ sq F =
      properOpenCoefficientComposite φ sq E ≫
        R((p)_*[ModuleCat.{u + 1} B]).map
          (D((k)_!open[ModuleCat.{u + 1} B]).map ((scalarExtension φ U).map f)) := by
  dsimp [properOpenCoefficientComposite]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  have hq := (openScalarExtension φ i).hom.naturality (R((r)_*[ModuleCat.{u + 1} A]).map f)
  have hmap : (scalarExtension φ Z).map
      (D((i)_!open[ModuleCat.{u + 1} A]).map (R((r)_*[ModuleCat.{u + 1} A]).map f)) =
      (derivedExtension i ⋙ scalarExtension φ Z).map (R((r)_*[ModuleCat.{u + 1} A]).map f) := rfl
  rw [hmap, hq]
  have hmap2 : (scalarExtension φ W ⋙ derivedExtension i).map
      (R((r)_*[ModuleCat.{u + 1} A]).map f) =
      D((i)_!open[ModuleCat.{u + 1} B]).map
        ((scalarExtension φ W).map (R((r)_*[ModuleCat.{u + 1} A]).map f)) := rfl
  rw [hmap2]
  simp only [Category.assoc]
  nth_rewrite 2 [← Category.assoc]
  rw [← D((i)_!open[ModuleCat.{u + 1} B]).map_comp]
  rw [finiteCoefficientDirectImageMap_naturality]
  rw [D((i)_!open[ModuleCat.{u + 1} B]).map_comp]
  have hmap3 : D((i)_!open[ModuleCat.{u + 1} B]).map
        (R((r)_*[ModuleCat.{u + 1} B]).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
            U.smallEtaleTopology φ).map f)) =
      (R((r)_*[ModuleCat.{u + 1} B]) ⋙ D((i)_!open[ModuleCat.{u + 1} B])).map
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
          U.smallEtaleTopology φ).map f) := rfl
  have hi := (properOpenCoefficientInterchange B sq).hom.naturality
    ((scalarExtension φ U).map f)
  rw [hmap3]
  simp only [Category.assoc]
  rw [hi]
  rfl


end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private lemma transportOpenAdjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (N : D ⥤ D') (M : C ⥤ C')
    (e : L ⋙ N ≅ M ⋙ L') (t : R ⋙ M ≅ N ⋙ R')
    (hc : ∀ Y : D, N.map (a.counit.app Y) =
      e.hom.app (R.obj Y) ≫ L'.map (t.hom.app Y) ≫ b.counit.app (N.obj Y))
    (X : C) (Y : D) (l : X ⟶ R.obj Y)
    (P : C') (d : M.obj X ≅ P) (Z : D') (c : N.obj Y ⟶ Z) :
    N.map ((a.homEquiv X Y).symm l) ≫ c = e.hom.app X ≫ L'.map d.hom ≫
      (b.homEquiv P Z).symm
        (d.inv ≫ M.map l ≫ t.hom.app Y ≫ R'.map c) := by
  dsimp only [Functor.comp_obj] at *
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [← L'.map_comp_assoc, d.hom_inv_id]
  rw [hc Y]
  have hn := e.hom.naturality l
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [b.counit_naturality]
  simp only [L'.map_id, Category.id_comp]


variable {U V W Z : Scheme.{u}}
  [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
  {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
  [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]

/-- Inverse of the transported open-restriction exchange followed by the inverse
open unit. The factors are the named counit mates, exact pullback comparison and
open-extension comparison. It does not use the site square to define Gamma.
Source: Stacks 0F7B and blueprint exceptional coefficient comparison,
existence, uniqueness and naturality (blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenSiteRestrictionInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E) ≅
      (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E))) :=
  ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A r)
      (isIso_fixedComparisonDirectImageMatePlus A r)).app E).symm ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus.mapIso
      (Etale.properOpenCoefficientRestrictionPlus A sq E).symm ≪≫
    (fixedComparisonPullbackPlus A i).app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E)) ≪≫
    (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.mapIso
      ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A p)
          (isIso_fixedComparisonDirectImageMatePlus A p)).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≪≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.mapIso
          ((properOpenSiteExtensionIso A k).app E))

private lemma openComparisonPlus_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j]
    (B : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j).counit.app B) =
      (properOpenSiteExtensionIso A j).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj B) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A j).hom.app B) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.obj B) := by
  let c := Compactification.ofIsOpenImmersion j
  have : IsNoetherian c.Z := by
    change IsNoetherian Y
    infer_instance
  exact (compactSupportSiteComparison_open_counits A c).2 B

/-- Gamma on bounded-below etale-origin complexes, defined by the open adjunct of
inverse transported restriction and open unit, with the retained origin E.
Source: Stacks 0F7B; blueprint exceptional comparison, existence and naturality
(blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenSiteInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj E)) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i).homEquiv _ _ |>.symm
      (properOpenSiteRestrictionInverse A sq E).hom

/-- The path through the etale proper/open comparison, the specified proper counit
mate and the open comparison. Source: Stacks 0F7B and blueprint exceptional comparison
(blueprint: lem-sp-proper-open-coefficient-mate). -/
def properOpenSiteComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
      (Etale.properOpenCoefficientInterchangePlus A sq E).hom ≫
    (fixedComparisonDirectImageMatePlus A p).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
      ((properOpenSiteExtensionIso A k).hom.app E)

/-- Site naturality square for the specified open adjunct, as an equation in the
unbounded category via the fully faithful bounded-below inclusion.
Source: Stacks 0F7B and blueprint exceptional coefficient comparison, existence,
uniqueness and naturality (blueprint: lem-sp-proper-open-coefficient-mate).
Proof: use lem-weil-pbc-comparison-pullback for exact inverse-image compatibility.
The proper edges are exactly the counit mates of
lem-weil-pbc-comparison-direct-image-canonical-mate, with its counit normalization.
The open edges are the natural comparison of lem-cbc-proetale-extension-zero-comparison.
Transport the coefficient mate rectangle across exact comparison. The inverse exchange
and inverse open unit give properOpenSiteRestrictionInverse; its open adjunct is
properOpenSiteInterchange. Mate pasting (lem-weil-pbc-mate-pasting) identifies the two
paths, because their open transposes are the same transported inverse-image composite.
The fully faithful inclusion of D+ places this equation in D without changing maps. -/
theorem properOpen_site_mate (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map (properOpenSiteComposite A sq E) =
      DerivedCategory.Plus.ι.map
        ((properOpenSiteExtensionIso A i).hom.app
            ((Etale.lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.obj E) ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.map
            ((fixedComparisonDirectImageMatePlus A r).app E) ≫
          properOpenSiteInterchange A sq E) := by
  apply congrArg DerivedCategory.Plus.ι.map
  let a := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} A) i
  have hγ : (a.homEquiv _ _).symm
      (Etale.properOpenCoefficientRestrictionPlus A sq E).inv =
        (Etale.properOpenCoefficientInterchangePlus A sq E).hom := by
    rw [Etale.properOpenCoefficientRestrictionPlus_inv]
    change (a.homEquiv _ _).symm
      ((a.homEquiv _ _) (Etale.properOpenCoefficientInterchangePlus A sq E).hom) = _
    exact (a.homEquiv _ _).symm_apply_apply _
  have h := transportOpenAdjunct a b
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus
    (properOpenSiteExtensionIso A i) (fixedComparisonPullbackPlus A i)
    (openComparisonPlus_counit A i) _ _
    (Etale.properOpenCoefficientRestrictionPlus A sq E).inv _
    ((@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A r)
      (isIso_fixedComparisonDirectImageMatePlus A r)).app E) _
    ((fixedComparisonDirectImageMatePlus A p).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.obj E) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
        ((properOpenSiteExtensionIso A k).hom.app E))
  rw [hγ] at h
  dsimp only [Functor.comp_obj] at h
  simpa only [properOpenSiteComposite, properOpenSiteInterchange,
    properOpenSiteRestrictionInverse, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, asIso_hom, Category.assoc, b] using h


/-- Both site-square composites are natural in every bounded-below etale-origin input.
Source: Stacks 0F7B and blueprint exceptional coefficient comparison, naturality
(blueprint: lem-sp-proper-open-coefficient-mate).
Proof: all three constituents of properOpenSiteComposite are natural: the specified
proper/open map, the counit mate and the exact open comparison. Their naturality
identities compose, with the canonical D+ inclusion comparisons. The site-square
identity then gives the same naturality for the path through the pro-etale open
adjunct. This is Step 3 of the node, using
lem-amb-unbounded-proper-open-interchange,
lem-weil-pbc-comparison-direct-image-canonical-mate and
lem-cbc-proetale-extension-zero-comparison. -/
theorem properOpen_site_mate_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    (sq : IsPullback k r p i)
    {E F : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (f : E ⟶ F) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.map
          ((Etale.lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.map f)) ≫
        properOpenSiteComposite A sq F =
      properOpenSiteComposite A sq E ≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.map
            ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.map f)) := by
  let γ := Etale.properOpenCoefficientInterchangePlusIso A sq
  let η :=
    Functor.whiskerRight γ.hom
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus
        (fixedComparisonDirectImageMatePlus A p) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (properOpenSiteExtensionIso A k).hom
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus
  simpa only [η, γ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Etale.properOpenCoefficientInterchangePlusIso_app, properOpenSiteComposite] using
    η.naturality f

end AlgebraicGeometry.ProEtale
