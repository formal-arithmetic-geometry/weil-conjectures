/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent
import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent

/-! # Object compatibility for a composite overlap pullback

Source: Stacks Project, Tags 08DW and 0D5S, the restriction and composition
comparisons used in the first paragraph of the proof of Tag 09RE.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory

attribute [local instance_reducible] TopologicalSpace.Opens.map
attribute [local instance_reducible] OrderHomClass.toOrderHom
attribute [local instance_reducible] TopCat.Hom.frameHom
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

private theorem object_pin_pasting
    {C : Type*} [Category* C] {A B D H : C}
    {ψ : A ⟶ B} {ρ : B ⟶ D} {χ : D ⟶ H}
    {t : A ⟶ D} {z : A ⟶ H}
    (hs : ψ ≫ ρ = t) (hp : t ≫ χ = z) : ψ ≫ ρ ≫ χ = z := by
  rw [← Category.assoc, hs, hp]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]


set_option maxHeartbeats 1000000 in
-- Comparing dependent derived functor types requires additional elaboration steps.
/-- Canonical restriction transport satisfies the cartesian object comparison.
Source: Stacks Project, Tags 08DW and 0D5S, the comparison of restricted
pullbacks in Tag 09RE.

Proof: Treat each Boolean branch with its selected open L (U or V). Lift the
object on L to the global derived category using essential surjectivity of
open restriction. Naturality transports gamma to that lift, where the defining
coherence square for comparisonFromRestrictions expresses gamma inverse in
terms of beta, tau, betaW and alpha. Substitute theta = kappa followed by the
inverse-site image of phi followed by site. The triangle identity for
openSiteReturnIso and openSiteOverlapIso cancels site against tau. Substitute
the component equation for perfectOverlapRestrictionBeta: its return-site
inverse cancels the site counit in eta. Naturality moves phi across the
restriction and cartesian pullback comparisons. The remaining two composites
are the two reassociations of pullback along the same three scheme maps.
The associativity law of the fixed counit-pinned perfectHomComposition makes
them equal; hmap identifies the composite cartesian maps and baseChangeMap_fst
identifies the final first projection. Mapping back the localization lift iso
and cancelling its inverse gives the desired identity for the original object.
Finally substitute the equalities specifying σ', ρ', η' and χ'. These parameters
provide an equation interface to the fixed constructors without unfolding them
in clients. The argument uses only restriction equivalences and natural isomorphisms; it
also applies to empty, equal and total opens, zero objects and unbounded E.
(blueprint: lem-pc-perfect-overlap-composite-object-pin).
-/
theorem perfect_overlap_composite_object_pin
    {X Y K C T S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (l : Over.mk b ⟶ Over.mk q)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let s := W.ι ≫ pY
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let m := baseChangeMap s l
  let eY := ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f W).paste_vert hf).isoPullback
  ∀ hmap : eY.inv ≫ r = m ≫ eK.inv,
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U))).mapDerivedCategory
  let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V))).mapDerivedCategory
  let τU := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ U))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))
  let τV := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ V))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))
  let ψ : ∀ a, data.d.toDiagram.HW.obj (F a) ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E := fun a ↦
    Bool.casesOn a
      (data.d.toDiagram.γU.symm.app ((derivedPullback (f ∣_ U)).obj A) ≪≫
        SP.mapIso data.θU ≪≫ τU.app E)
      (data.d.toDiagram.γV.symm.app ((derivedPullback (f ∣_ V)).obj B) ≪≫
        SQ.mapIso data.θV ≪≫ τV.app E)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let η := perfectOverlapNaturalComparisonOfSquare g f pX pK pY b q hg hf U V r m hmap
  let σ : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      ((perfectOverlapStageObjectIso f pK pY q hf U V U inf_le_left).app A)
      ((perfectOverlapStageObjectIso f pK pY q hf U V V inf_le_right).app B)
  let ρ : ∀ a : Bool, apex.functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
        (derivedPullback (pullback.fst s b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φU)
      (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φV)
  ∀ (σ' : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A))
    (ρ' : ∀ a : Bool, apex.functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
        (derivedPullback (pullback.fst s b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A))
    (η' : data.d.toDiagram.HW ⋙ apex.functor ≅
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙ derivedPullback m)
    (χ' : derivedPullback (pullback.fst s b) ≅
      derivedPullback (pullback.fst s q) ⋙ derivedPullback m),
    σ' = σ → ρ' = ρ → η' = η → χ' = perfectHomComparison s l →
  ∀ a : Bool,
    apex.functor.map (ψ a).hom ≫ (ρ' a).hom ≫
        χ'.hom.app
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) =
      η'.hom.app (F a) ≫ (derivedPullback m).map (σ' a).hom := by
  intro W s r m eY eK hmap data F SP SQ τU τV ψ apex η σ ρ
    σ' ρ' η' χ' hσ hρ hη hχ a
  rw [hρ]
  have hs := perfectOverlapCompositeSiteComponent
    f gk g hgf pX pY b hg U V A B E φU φV
  have hp := perfectOverlapProjectionCompositionComponent
    f gk g hgf pX pK pY b q hg hf l U V A B E φU φV
    hmap σ' η' χ' hσ hη hχ
  cases a
  · exact object_pin_pasting hs.1 (hp false)
  · exact object_pin_pasting hs.2 (hp true)

end AlgebraicGeometry
