/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.PreservesKFlatComplexesCriterion
public import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract

/-!
# K-flat resolutions whose image under a functor is K-flat

Let `F : C ⥤ D` be an additive functor between Grothendieck abelian braided closed monoidal
categories which commutes with colimits. Suppose that `C` has a flat separator `G` such that
`F G` is flat as well. Then every complex `K` of `C` receives a quasi-isomorphism `Q ⟶ K` from
a K-flat complex `Q` such that `F Q` is K-flat
(`CategoryTheory.Functor.exists_quasiIso_kFlat_mapHomologicalComplex_kFlat`). This holds even
if `F` does not preserve flat objects in general.

Indeed, the objects `X` such that both `X` and `F X` are flat
(`CategoryTheory.Functor.flatAndMapFlat`) are closed under coproducts, so the functorial
covers `∐_{g : G ⟶ X} G ⟶ X` give a left resolution by such objects
(`CategoryTheory.Functor.flatAndMapFlatLeftResolution`). The associated resolutions of
complexes are `ℤ`-indexed colimits of bounded above complexes of objects in this class; they
are K-flat, and so are their images by `F`
(`CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_of_colimitsOfShape_of_le`).

-/

@[expose] public section

universe v u u'

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
  [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
  [Abelian D] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [BraidedCategory D] [MonoidalClosed D]
  (F : C ⥤ D) [F.Additive]

/-- The objects `X` such that both `X` and `F X` are flat. -/
def flatAndMapFlat : ObjectProperty C :=
  fun X ↦ ObjectProperty.flat X ∧ ObjectProperty.flat (F.obj X)

instance : (flatAndMapFlat F).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨ObjectProperty.prop_of_iso _ e h.1, ObjectProperty.prop_of_iso _ (F.mapIso e) h.2⟩

instance : (flatAndMapFlat F).ContainsZero where
  exists_zero := ⟨0, isZero_zero C,
    ObjectProperty.prop_of_isZero _ (isZero_zero C),
    ObjectProperty.prop_of_isZero _ (F.map_isZero (isZero_zero C))⟩

instance : (flatAndMapFlat F).IsStableUnderRetracts where
  of_retract e h := ⟨ObjectProperty.prop_of_retract _ e h.1,
    ObjectProperty.prop_of_retract _ (e.map F) h.2⟩

instance (J : Type) [Finite J] :
    (flatAndMapFlat F).IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine ⟨ObjectProperty.prop_of_isLimit _ p.isLimit (fun j ↦ (p.prop_diag_obj j).1),
      ObjectProperty.prop_of_isLimit _ (isLimitOfPreserves F p.isLimit)
        (fun j ↦ (p.prop_diag_obj j).2)⟩

instance : HasFiniteProducts (flatAndMapFlat F).FullSubcategory where
  out _ := by
    apply hasLimitsOfShape_of_closedUnderLimits

instance : HasFiniteBiproducts (flatAndMapFlat F).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteProducts

omit [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C] in
/-- A functor commuting with `ℤ`-indexed colimits sends `ℤ`-indexed colimits of bounded above
complexes of objects in a class `P` to K-flat complexes, as soon as it sends the objects of `P`
to flat objects. -/
lemma kFlat_mapHomologicalComplex_obj_of_colimitsOfShape_of_le
    [PreservesColimitsOfShape ℤ F] (P : ObjectProperty C)
    (hP : ∀ X, P X → ObjectProperty.flat (F.obj X)) {K : CochainComplex C ℤ}
    (hK : P.cochainComplexMinus.colimitsOfShape ℤ K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨p⟩ := hK
  refine ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) p.isColimit) (fun j ↦ ?_)
  obtain ⟨hj, n, hn⟩ := p.prop_diag_obj j
  exact CochainComplex.cochainComplexMinus_flat_le_kFlat D _
    ⟨fun i ↦ hP _ (hj i), n, (CochainComplex.isStrictlyLE_iff _ n).2
      fun i hi ↦ F.map_isZero (CochainComplex.isZero_of_isStrictlyLE _ n i hi)⟩

variable [PreservesColimitsOfSize.{v, v} F]

/-- The functorial cover `∐_{g : G ⟶ X} G ⟶ X` attached to a flat separator `G` with `F G`
flat is a left resolution by objects `X` with `X` and `F X` flat. -/
noncomputable def flatAndMapFlatLeftResolution {G : C} (hG : IsSeparator G)
    (hG' : ObjectProperty.flat G) (hFG : ObjectProperty.flat (F.obj G)) :
    Abelian.LeftResolution (flatAndMapFlat F).ι where
  F := ObjectProperty.lift _ (coyoneda.obj (Opposite.op G) ⋙ sigmaConst.obj G) (fun X ↦
    ⟨ObjectProperty.flat_coproduct _ (fun _ ↦ hG'),
      ObjectProperty.prop_of_iso _
        (PreservesCoproduct.iso F (fun _ : (G ⟶ X) ↦ G)).symm
        (ObjectProperty.flat_coproduct _ (fun _ ↦ hFG))⟩)
  π := (sigmaConstAdj G).counit
  epi_π_app X := (isSeparator_iff_epi G).1 hG X

/-- If `C` has a flat separator `G` with `F G` flat, every complex `K` of `C` receives a
quasi-isomorphism from a K-flat complex `Q` with `F Q` K-flat. -/
theorem exists_quasiIso_kFlat_mapHomologicalComplex_kFlat [PreservesColimitsOfShape ℤ F]
    {G : C} (hG : IsSeparator G) (hG' : ObjectProperty.flat G)
    (hFG : ObjectProperty.flat (F.obj G)) (K : CochainComplex C ℤ) :
    ∃ (Q : CochainComplex C ℤ) (π : Q ⟶ K), QuasiIso π ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
  let Λ := (flatAndMapFlatLeftResolution F hG hG' hFG).reduced
  have hι : (flatAndMapFlat F).ι.essImage ≤ flatAndMapFlat F := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  exact ⟨Λ.resolutionFunctor.obj K, Λ.resolutionNatTrans.app K, inferInstance,
    Λ.kFlat_resolutionFunctor_obj (hι.trans fun _ h ↦ h.1) K,
    F.kFlat_mapHomologicalComplex_obj_of_colimitsOfShape_of_le _ (fun _ h ↦ (hι _ h).2)
      (Λ.colimitOfShapeResolutionFunctorObj K).colimitsOfShape⟩

end CategoryTheory.Functor
