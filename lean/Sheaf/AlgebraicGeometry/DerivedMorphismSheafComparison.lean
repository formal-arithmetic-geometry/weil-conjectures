/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.CategoryTheory.DerivedMorphismPresheaf
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
/-!
# Canonical comparison and evaluation of derived morphism sheaves

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- The actual inverse-image functor on set sheaves for the etale/pro-etale comparison.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSetUpperStar :=
  Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)

/-- The existing comparison inverse image preserves finite limits.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
instance comparisonSetUpperStar_preservesFiniteLimits :
    PreservesFiniteLimits (comparisonSetUpperStar X) :=
  preservesFiniteLimits_proEtaleSiteComparison X

/-- The exact module-sheaf comparison inverse image, applied to the actual derived category.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparison :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory

/-- The etale-to-pro-etale inclusion induces a continuous functor on localized sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: An etale cover on the slice is a jointly surjective etale covering of its domain. Its
image in the pro-etale slice is a covering family. Covering sieves are stable under the base
changes that define the localized topologies. The continuity criterion on covering families
therefore applies to the postcomposition functor. -/
theorem comparisonSlice_continuous (V : X.Etale) :
    (Over.post (toProEt X)).IsContinuous (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V)) := by
  have : RepresentablyFlat (Over.post (X := V) (toProEt X)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((CoverPreserving.of_isContinuous (toProEt X) _ _).overPost V)

attribute [instance] comparisonSlice_continuous

/-- The constructed comparison inverse image on the localized etale and pro-etale sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSliceUpperStar (V : X.Etale) :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.post (toProEt X))
    (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

/-- The constructed pullback/pushforward adjunction on the localized sites.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev comparisonSliceAdjunction (V : X.Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.post (toProEt X))
    (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

/-- The localized comparison direct image is additive, section by section.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
instance comparisonSliceLowerStar_additive (V : X.Etale) :
    ((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} B)
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))).Additive where
  map_add := by intros; rfl

/-- The localized comparison inverse image is additive by its adjunction.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable instance comparisonSliceUpperStar_additive (V : X.Etale) :
    (comparisonSliceUpperStar X B V).Additive :=
  (comparisonSliceAdjunction X B V).left_adjoint_additive

/-- The localized comparison inverse image preserves finite colimits as a left adjoint.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
instance comparisonSliceUpperStar_preservesFiniteColimits (V : X.Etale) :
    PreservesFiniteColimits (comparisonSliceUpperStar X B V) :=
  letI := (comparisonSliceAdjunction X B V).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The localized comparison inverse image is left exact.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: The inclusion on slices preserves finite limits: the underlying inclusion does so, and
slice finite limits are computed in the original categories. Together with continuity, the
constructed sheaf inverse image is the inverse image of a geometric morphism and preserves
finite limits. The same calculation applies to module-valued sheaves since the finite-limit
comparison is computed on their underlying sheaves. -/
theorem comparisonSliceUpperStar_preservesFiniteLimits (V : X.Etale) :
    PreservesFiniteLimits (comparisonSliceUpperStar X B V) := by
  have : RepresentablyFlat (Over.post (X := V) (toProEt X)) :=
    flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (Over.post (toProEt X)) (ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V))

attribute [instance] comparisonSliceUpperStar_preservesFiniteLimits

/-- The canonical slice base-change map, defined by restricting the unit of the global comparison
adjunction and transposing under the slice adjunction.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonSliceBaseMap (V : X.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonSliceUpperStar X B V).obj (M.over V) ⟶
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M).over
        ((toProEt X).obj V) :=
  ((comparisonSliceAdjunction X B V).homEquiv _ _).symm
    ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M))

private noncomputable def comparisonStarIso (V : X.Etale) :
    Over.star V ⋙ Over.post (toProEt X) ≅
      toProEt X ⋙ Over.star ((toProEt X).obj V) :=
  NatIso.ofComponents (fun W ↦ Over.isoMk (asIso (prodComparison (toProEt X) V W))
    (by simp [Over.post, Over.star_obj_hom])) (by
      intro W Z f
      ext
      simpa using prodComparison_natural (toProEt X) (𝟙 V) f)

/-- The specified canonical slice base-change map is invertible and natural in the module sheaf.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Both composites are inverse image for the same geometric morphism from the localized
pro-etale topos to the etale topos. The comparison obtained by transposing the restricted unit
is their canonical localization comparison, and is invertible: on a sheafified presheaf it is
the restriction/sheafification comparison on the slice. Sheafification and restriction commute
by the covering-sieve description of a localized topology. Naturality follows by restricting
naturality of the adjunction unit and transposing through the slice adjunction. -/
theorem comparisonSliceBaseMap_properties (V : X.Etale) :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
      IsIso (comparisonSliceBaseMap X B V M)) ∧
    (∀ (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (f : M ⟶ N),
      (comparisonSliceUpperStar X B V).map
          ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V).map f) ≫
        comparisonSliceBaseMap X B V N =
      comparisonSliceBaseMap X B V M ≫
        ((ProEt.topology X).overPullback (ModuleCat.{u + 1} B)
          ((toProEt X).obj V)).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map f)) := by
  let rV := (Over.forgetAdjStar V).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B) (X.smallEtaleTopology.over V) X.smallEtaleTopology
  let rU := (Over.forgetAdjStar ((toProEt X).obj V)).sheafPushforwardContinuous
    (E := ModuleCat.{u + 1} B)
    ((ProEt.topology X).over ((toProEt X).obj V)) (ProEt.topology X)
  have : (toProEt X ⋙ Over.star ((toProEt X).obj V)).IsContinuous
      X.smallEtaleTopology ((ProEt.topology X).over ((toProEt X).obj V)) :=
    Functor.isContinuous_comp _ _ _ (ProEt.topology X) _
  let eR :=
    Functor.sheafPushforwardContinuousComp' (comparisonStarIso X V)
      (ModuleCat.{u + 1} B) X.smallEtaleTopology
      (X.smallEtaleTopology.over V)
      ((ProEt.topology X).over ((toProEt X).obj V)) ≪≫
    (Functor.sheafPushforwardContinuousComp (toProEt X)
      (Over.star ((toProEt X).obj V)) (ModuleCat.{u + 1} B)
      X.smallEtaleTopology (ProEt.topology X)
      ((ProEt.topology X).over ((toProEt X).obj V))).symm
  let adj₁ := (rV.comp (comparisonSliceAdjunction X B V)).ofNatIsoRight eR
  let adj₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).comp rU
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      e.hom.app M = comparisonSliceBaseMap X B V M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      ((rV.comp (comparisonSliceAdjunction X B V)).ofNatIsoRight eR).homEquiv _ _
        (comparisonSliceBaseMap X B V M)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change adj₂.unit.app M =
      rV.homEquiv _ _
        ((comparisonSliceAdjunction X B V).homEquiv _ _
          (comparisonSliceBaseMap X B V M)) ≫ eR.hom.app _
    rw [comparisonSliceBaseMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    ext W : 3
    let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M
    let N := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M
    change η.hom.app W ≫ N.obj.map (prod.snd :
        (toProEt X).obj V ⨯ (toProEt X).obj W.unop ⟶ _).op =
      (M.obj.map (prod.snd : V ⨯ W.unop ⟶ _).op ≫
        η.hom.app (op (V ⨯ W.unop))) ≫
          N.obj.map (inv (prodComparison (toProEt X) V W.unop)).op
    have hn : M.obj.map (prod.snd : V ⨯ W.unop ⟶ W.unop).op ≫
        η.hom.app (op (V ⨯ W.unop)) =
      η.hom.app W ≫ N.obj.map ((toProEt X).map prod.snd).op :=
        η.hom.naturality (prod.snd : V ⨯ W.unop ⟶ W.unop).op
    rw [hn]
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [inv_prodComparison_map_snd]
  constructor
  · intro M
    rw [← he M]
    infer_instance
  · intro M N f
    simpa only [he, Functor.comp_map] using e.hom.naturality f

/-- The natural isomorphism formed from the specified invertible slice base-change map.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonSliceBaseIso (V : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) V ⋙
      comparisonSliceUpperStar X B V ≅
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ⋙
      (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) ((toProEt X).obj V) :=
  NatIso.ofComponents (fun M ↦
    @asIso _ _ _ _ (comparisonSliceBaseMap X B V M)
      ((comparisonSliceBaseMap_properties X B V).1 M))
    ((comparisonSliceBaseMap_properties X B V).2 _ _)

/-- The induced canonical commutation of comparison inverse image and restriction on derived
categories.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonSliceIso (V : X.Etale) :
    derivedSliceRestriction X.smallEtaleTopology B V ⋙
      (comparisonSliceUpperStar X B V).mapDerivedCategory ≅
    derivedComparison X B ⋙
      derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonSliceBaseIso X B V) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

variable (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))

/-- Pullback of an actual etale-local derived morphism under the localized comparison functor.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonLocalHom (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj A) ⟶
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj D) :=
  (derivedComparisonSliceIso X B V).inv.app A ≫
    (comparisonSliceUpperStar X B V).mapDerivedCategory.map f ≫
      (derivedComparisonSliceIso X B V).hom.app D

/-- Pullback of an actual etale-local derived isomorphism under that same functor.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonLocalIso (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj A) ≅
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).obj
        ((derivedComparison X B).obj D) :=
  ((derivedComparisonSliceIso X B V).app A).symm ≪≫
    (comparisonSliceUpperStar X B V).mapDerivedCategory.mapIso f ≪≫
      (derivedComparisonSliceIso X B V).app D

/-- The pro-etale sheafification of local derived Hom between the pulled-back objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparisonHomTarget :=
  derivedLocalHomSheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)

/-- The pro-etale sheafification of local derived Isom between the pulled-back objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev derivedComparisonIsoTarget :=
  derivedLocalIsoSheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)

/-- Pull back a local derived morphism and apply the pro-etale sheafification unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonHomUnit (V : X.Etale)
    (f : (derivedLocalHomPresheaf X.smallEtaleTopology B A D).obj (op V)) :
    (derivedComparisonHomTarget X B A D).obj.obj (op ((toProEt X).obj V)) :=
  (toSheafify (ProEt.topology X)
    (derivedLocalHomPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app
        (op ((toProEt X).obj V)) (derivedComparisonLocalHom X B A D V f)

/-- Pull back a local derived isomorphism and apply the pro-etale sheafification unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonIsoUnit (V : X.Etale)
    (f : (derivedLocalIsoPresheaf X.smallEtaleTopology B A D).obj (op V)) :
    (derivedComparisonIsoTarget X B A D).obj.obj (op ((toProEt X).obj V)) :=
  (toSheafify (ProEt.topology X)
    (derivedLocalIsoPresheaf (ProEt.topology X) B
      ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app
        (op ((toProEt X).obj V)) (derivedComparisonLocalIso X B A D V f)

/-- Local derived pullback followed by sheafification commutes with restriction on the etale site.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: The canonical slice comparison is defined by adjunction units, so satisfies the
localization cocycle. Derive that cocycle. Expand the local pullback and restriction
conjugations; the cocycle and functoriality identify the two resulting derived morphisms. Apply
naturality of the pro-etale sheafification unit. For isomorphisms use the same argument on hom
components and then isomorphism extensionality. -/
theorem derivedComparisonUnits_natural :
    (∀ (V W : X.Etale) (g : W ⟶ V)
      (f : (derivedLocalHomPresheaf X.smallEtaleTopology B A D).obj (op V)),
      derivedComparisonHomUnit X B A D W
          (derivedLocalHomRestriction X.smallEtaleTopology B A D g f) =
        (derivedComparisonHomTarget X B A D).obj.map ((toProEt X).map g).op
          (derivedComparisonHomUnit X B A D V f)) ∧
    (∀ (V W : X.Etale) (g : W ⟶ V)
      (f : (derivedLocalIsoPresheaf X.smallEtaleTopology B A D).obj (op V)),
      derivedComparisonIsoUnit X B A D W
          (derivedLocalIsoRestriction X.smallEtaleTopology B A D g f) =
        (derivedComparisonIsoTarget X B A D).obj.map ((toProEt X).map g).op
          (derivedComparisonIsoUnit X B A D V f)) := by
  sorry

/-- The presheaf map formed from the specified local derived Hom pullbacks.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonHomPresheafMap :
    derivedLocalHomPresheaf X.smallEtaleTopology B A D ⟶
      ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonHomTarget X B A D) |>.obj where
  app V := ↾(derivedComparisonHomUnit X B A D V.unop)
  naturality := by
    intro V W f
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedComparisonUnits_natural X B A D).1 _ _ f.unop a

/-- The presheaf map formed from the specified local derived Isom pullbacks.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedComparisonIsoPresheafMap :
    derivedLocalIsoPresheaf X.smallEtaleTopology B A D ⟶
      ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonIsoTarget X B A D) |>.obj where
  app V := ↾(derivedComparisonIsoUnit X B A D V.unop)
  naturality := by
    intro V W f
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedComparisonUnits_natural X B A D).2 _ _ f.unop a

/-- The canonical comparison map on derived Hom sheaves: first transpose along sheafification, then
along the comparison adjunction. Its data comes from actual local derived pullback.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedHomSheafComparison :
    (comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D) ⟶
        derivedComparisonHomTarget X B A D :=
  ((proEtaleSiteComparison X).homEquiv _ _).symm
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonHomPresheafMap X B A D))

/-- The analogous canonical comparison map on derived Isom sheaves, using actual isomorphisms.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedIsoSheafComparison :
    (comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D) ⟶
        derivedComparisonIsoTarget X B A D :=
  ((proEtaleSiteComparison X).homEquiv _ _).symm
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonIsoPresheafMap X B A D))

/-- The pro-etale sheafification unit on the local derived Hom presheaf at the specified object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev proEtaleDerivedHomUnit (U : X.ProEt) :=
  (toSheafify (ProEt.topology X) (derivedLocalHomPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app (op U)

/-- The pro-etale sheafification unit on the local derived Isom presheaf at the specified object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable abbrev proEtaleDerivedIsoUnit (U : X.ProEt) :=
  (toSheafify (ProEt.topology X) (derivedLocalIsoPresheaf (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D))).app (op U)

/-- The pro-etale sheafification units for these two presheaves are bijective on affine weakly
contractible objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Restriction identifies module sheaves on a finite disjoint union of site objects with the
product of the module-sheaf categories of its components. This is an exact equivalence, and
hence gives the corresponding equivalence of derived categories. Thus both actual local derived
Hom and Isom presheaves send finite disjoint unions to products, including the empty union,
whose localized category is the zero category. Stacks Tag 0F63 now says their sheafification
units are bijective on an affine weakly contractible object. The hypothesis here is the
topos-theoretic weak contractibility used in that tag, not merely a property of the underlying
topological space. -/
theorem proEtaleDerivedUnits_bijective (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    Function.Bijective (proEtaleDerivedHomUnit X B A D U) ∧
      Function.Bijective (proEtaleDerivedIsoUnit X B A D U) := by
  sorry

/-- The canonical evaluation map: the comparison map followed by the unique inverse of the bijective
pro-etale sheafification unit. Only the proof of bijectivity is postponed.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedHomEvaluation (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj A) ⟶
      (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj D) :=
  (Equiv.ofBijective (proEtaleDerivedHomUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).1).symm
      ((derivedHomSheafComparison X B A D).hom.app (op U) s)

/-- The same canonical evaluation construction on actual derived isomorphisms.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def derivedIsoEvaluation (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj A) ≅
      (derivedSliceRestriction (ProEt.topology X) B U).obj ((derivedComparison X B).obj D) :=
  (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).2).symm
      ((derivedIsoSheafComparison X B A D).hom.app (op U) s)

/-- Composition of pulled-back Hom-sheaf sections, through the inverse-image binary-product
comparison.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackDerivedHomComp
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U))
    (t : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B D G)).obj.obj (op U)) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A G)).obj.obj (op U) :=
  ((comparisonSetUpperStar X).map
      (derivedLocalHomSheafComp X.smallEtaleTopology B A D G)).hom.app (op U)
    ((inv (prodComparison (comparisonSetUpperStar X)
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)
      (derivedLocalHomSheaf X.smallEtaleTopology B D G))).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t))

/-- Composition of pulled-back Isom-sheaf sections through the same product comparison.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackDerivedIsoComp
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U))
    (t : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B D G)).obj.obj (op U)) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A G)).obj.obj (op U) :=
  ((comparisonSetUpperStar X).map
      (derivedLocalIsoSheafComp X.smallEtaleTopology B A D G)).hom.app (op U)
    ((inv (prodComparison (comparisonSetUpperStar X)
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)
      (derivedLocalIsoSheaf X.smallEtaleTopology B D G))).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t))

/-- The section of the pulled-back Hom sheaf represented by an actual etale-local morphism and a map
from the pro-etale object to its domain.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackEtaleLocalHom (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D)
    (U : X.ProEt) (g : U ⟶ (toProEt X).obj V) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U) :=
  ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.map g.op
    (((proEtaleSiteComparison X).unit.app
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f))

/-- The corresponding section represented by an actual etale-local isomorphism.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackEtaleLocalIso (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D)
    (U : X.ProEt) (g : U ⟶ (toProEt X).obj V) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U) :=
  ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.map g.op
    (((proEtaleSiteComparison X).unit.app
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f))

/-- The identity section, pulled back from the terminal etale object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackDerivedIdentity (U : X.ProEt) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A A)).obj.obj (op U) :=
  pulledbackEtaleLocalHom X B A A (Scheme.Etale.mk (𝟙 X)) (𝟙 _) U
    (MorphismProperty.Over.homMk U.hom (by
      change U.hom ≫ 𝟙 X = U.hom
      simp))

/-- The identity isomorphism section, pulled back from the terminal etale object.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def pulledbackDerivedIsoIdentity (U : X.ProEt) :
    ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A A)).obj.obj (op U) :=
  pulledbackEtaleLocalIso X B A A (Scheme.Etale.mk (𝟙 X)) (Iso.refl _) U
    (MorphismProperty.Over.homMk U.hom (by
      change U.hom ≫ 𝟙 X = U.hom
      simp))

variable {B' : Type (u + 1)} [CommRing B']

/-- The canonical map commuting scalar restriction with comparison inverse image, obtained by
transposing the restriction of the comparison adjunction unit.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsMap (φ : B →+* B')
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ⟶
      (Sheaf.restrictScalars (ProEt.topology X) φ).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X).obj M) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _).symm
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).unit.app M))

/-- The specified scalar-restriction comparison is invertible and natural.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison)

Proof: Restriction of scalars is computed on the same underlying sheaf with its scalar action
forgotten along the given ring map. Comparison inverse image is the inverse image on the
underlying sheaves with its induced scalar action. These operations commute. On sheafified
presheaves their canonical comparison is the identity before sheafification and is therefore
invertible; transposing the restricted adjunction unit gives exactly this comparison. Naturality
follows from naturality of that unit and naturality of the adjunction hom equivalence. -/
theorem comparisonRestrictScalarsMap_properties (φ : B →+* B') :
    (∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'),
      IsIso (comparisonRestrictScalarsMap X B φ M)) ∧
    (∀ (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) (f : M ⟶ N),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).map f) ≫
        comparisonRestrictScalarsMap X B φ N =
      comparisonRestrictScalarsMap X B φ M ≫
        (Sheaf.restrictScalars (ProEt.topology X) φ).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X).map f)) := by
  let adj₁ := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)
  let adj₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).comp
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ)
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')) :
      e.hom.app M = comparisonRestrictScalarsMap X B φ M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).homEquiv _ _
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _
          (comparisonRestrictScalarsMap X B φ M))
    rw [comparisonRestrictScalarsMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    exact (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.naturality
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B') X).unit.app M)
  constructor
  · intro M
    rw [← he M]
    infer_instance
  · intro M N f
    simpa only [he, Functor.comp_map] using e.hom.naturality f

/-- The canonical scalar-restriction comparison isomorphism on module sheaves.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsSheafIso (φ : B →+* B') :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X ≅
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B') X ⋙
      Sheaf.restrictScalars (ProEt.topology X) φ :=
  NatIso.ofComponents (fun M ↦
    @asIso _ _ _ _ (comparisonRestrictScalarsMap X B φ M)
      ((comparisonRestrictScalarsMap_properties X B φ).1 M))
    ((comparisonRestrictScalarsMap_properties X B φ).2 _ _)

/-- The canonical scalar-restriction comparison induced on derived categories.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; localization and inverse-image
adjunctions. (blueprint: def-weil-pbc-derived-morphism-sheaf-comparison) -/
noncomputable def comparisonRestrictScalarsIso (φ : B →+* B') :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ derivedComparison X B ≅
      derivedComparison X B' ⋙ Sheaf.derivedRestrictScalars (ProEt.topology X) φ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonRestrictScalarsSheafIso X B φ) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

end AlgebraicGeometry.Scheme
