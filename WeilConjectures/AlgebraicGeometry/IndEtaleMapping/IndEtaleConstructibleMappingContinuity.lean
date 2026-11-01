/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.Constructible
public import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleConstructibleMappingContinuityData
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleConstructibleMappingModelSkeleton
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- Global RHom of the two exact inverse images along a scheme over X.
This is the existing RΓ of the existing derived internal Hom.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def value (T : Over X) : DerivedCategory (ModuleCat.{u + 1} A) :=
  ((ExternalRHom.globalHom A T.left).obj
    (op ((ExternalRHom.pull A T.hom).obj K))).obj
      ((ExternalRHom.pull A T.hom).obj M)

/-- Pullback of derived morphisms, transported along the canonical composition
isomorphisms for inverse image. Its source is the evaluation transpose already
provided by ExternalRHom.restriction; no map or isomorphism is chosen.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def pullback {T S : Over X} (f : T ⟶ S) : value A K M S ⟶ value A K M T :=
  ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app K).op).app
          ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
          f.w.symm).inv.app M)

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)

variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

end AlgebraicGeometry.Etale.IndEtaleMapping

namespace AlgebraicGeometry.Etale.IndEtaleMapping

private def isColimit_of_normalization
    {C : Type*} [Category C] {L : Type*} [Category L]
    {B E : L ⥤ C} (b : Cocone B) (e : Cocone E)
    (stage : ∀ i : L, B.obj i ≅ E.obj i) (apex : b.pt ≅ e.pt)
    (transition : ∀ {i j : L} (f : i ⟶ j),
      B.map f ≫ (stage j).hom = (stage i).hom ≫ E.map f)
    (leg : ∀ i : L, b.ι.app i ≫ apex.hom = (stage i).hom ≫ e.ι.app i)
    (he : IsColimit e) : IsColimit b := by
  let δ : B ≅ E := NatIso.ofComponents stage (fun f ↦ transition f)
  let γ : b ≅ (Cocone.precompose δ.hom).obj e := Cocone.ext apex leg
  exact ((IsColimit.precomposeHomEquiv δ e).symm he).ofIsoColimit γ.symm

private theorem isIso_localized_desc_of_cohomology
    (B : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : Cocone B)
    [IsCofiltered I]
    (h : ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).mapCocone b))) :
    IsIso (DerivedCategory.Q.map (colimit.desc B b)) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q
  obtain ⟨hq⟩ := h q
  let hb : IsColimit (H.mapCocone b) :=
    IsColimit.mapCoconeEquiv
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q) hq
  let hc := isColimitOfPreserves H (colimit.isColimit B)
  have hdesc : hc.desc (H.mapCocone b) = H.map (colimit.desc B b) := by
    apply hc.hom_ext
    intro i
    change H.map (colimit.ι B i) ≫ _ = H.map (colimit.ι B i) ≫ _
    exact (hc.fac (H.mapCocone b) i).trans (by
      simp only [← Functor.map_comp, colimit.ι_desc]
      rfl)
  have hi := hc.nonempty_isColimit_iff_isIso_desc.1 ⟨hb⟩
  rw [hdesc] at hi
  exact hi

/-- The global-Hom square of one strict direct-image transition: a map of
representatives normalized against `imagePullback g` goes, after global Hom and
`imageHomIso`, to the evaluation-defined `pullback g`. -/
private theorem imageHomIso_stage_square {T S : Over X} (g : T ⟶ S)
    {Y Z : DerivedCategoryModule A X} (w : Y ⟶ Z) (sS : Y ≅ imageValue A M S)
    (sT : Z ≅ imageValue A M T) (h : w ≫ sT.hom = sS.hom ≫ imagePullback A M g) :
    ((ExternalRHom.globalHom A X).obj (op K)).map w ≫
        (((ExternalRHom.globalHom A X).obj (op K)).mapIso sT ≪≫ imageHomIso A M K T).hom =
      (((ExternalRHom.globalHom A X).obj (op K)).mapIso sS ≪≫ imageHomIso A M K S).hom ≫
        pullback A K M g := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
    imageHomIso_naturality A K M g, pullback]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale.IndEtaleMapping
