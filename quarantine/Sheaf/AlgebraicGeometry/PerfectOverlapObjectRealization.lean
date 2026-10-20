/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData

/-! # Object comparisons for the geometric overlap model

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- Object-level realization in the fixed geometric base-change system.
This contains no Hom equivalences, identity/composition laws or perfectness assertions.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization). -/
structure PerfectHomObjectRealization
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i)) (objects : Bool → schemeDerivedCategory Y)
    where
  stageEquiv : ∀ k : Set.Ici i, C k ≌
    schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property))))
  apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))
  stageObj : ∀ k b, (stageEquiv k).functor.obj (F k b) ≅
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).obj
      (objects b)
  apexObj : ∀ b, apexEquiv.functor.obj (O b) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj (objects b)
  hom_pin : ∀ (k : Set.Ici i) (a b : Bool) (f : F k a ⟶ F k b),
    (Iso.homCongr (apexObj a) (apexObj b))
        (apexEquiv.functor.map ((ψ k a).inv ≫ (G k).map f ≫ (ψ k b).hom)) =
      perfectLimitMap R c s k.property
        ((Iso.homCongr (stageObj k a) (stageObj k b))
          ((stageEquiv k).functor.map f))

private theorem pinned_conjugation
    {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]
    (S₀ : C₀ ⥤ D₀) (K₀ : C₀ ⥤ E₀) (H₀ : D₀ ⥤ E₀)
    (η : K₀ ≅ S₀ ⋙ H₀) {a b : C₀} {p q : D₀} {z z' : E₀}
    (σa : S₀.obj a ≅ p) (σb : S₀.obj b ≅ q)
    (ρa : K₀.obj a ≅ z) (ρb : K₀.obj b ≅ z')
    (χa : z ≅ H₀.obj p) (χb : z' ≅ H₀.obj q)
    (ha : ρa.hom ≫ χa.hom = η.hom.app a ≫ H₀.map σa.hom)
    (hb : ρb.hom ≫ χb.hom = η.hom.app b ≫ H₀.map σb.hom) (f : a ⟶ b) :
    ρa.inv ≫ K₀.map f ≫ ρb.hom =
      χa.hom ≫ H₀.map (σa.inv ≫ S₀.map f ≫ σb.hom) ≫ χb.inv := by
  have hsource : ρa.inv ≫ η.hom.app a = χa.hom ≫ H₀.map σa.inv := by
    apply (cancel_epi ρa.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ha, Category.assoc, ← H₀.map_comp]
    simp
  apply (cancel_mono χb.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  rw [hb]
  rw [← Category.assoc (K₀.map f), η.hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Category.assoc ρa.inv, hsource]
  simp only [Category.assoc]

/-- Pinned object comparisons and a natural functor comparison determine the Hom pin.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization).

Proof: Multiply the target equation by the hom component of the target composition
comparison. Substitute object_pin at the target. Naturality of comparison moves the
stage morphism through that component. The inverse form of object_pin at the source
then leaves exactly the fixed conjugation defining perfectLimitMap. Cancel the target
comparison, which is an isomorphism. -/
private theorem perfect_overlap_object_realization_hom_pin
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    (objects : Bool → schemeDerivedCategory Y)
    (stageEquiv : ∀ k : Set.Ici i, C k ≌
      schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))))
    (apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (r : PerfectHomObjectRealizationCore R c i C F D O G ψ Y s objects stageEquiv apexEquiv) :
    ∀ (k : Set.Ici i) (a b : Bool) (f : F k a ⟶ F k b),
    (Iso.homCongr (r.apexObj a) (r.apexObj b))
        (apexEquiv.functor.map ((ψ k a).inv ≫ (G k).map f ≫ (ψ k b).hom)) =
      perfectLimitMap R c s k.property
        ((Iso.homCongr (r.stageObj k a) (r.stageObj k b))
          ((stageEquiv k).functor.map f)) := by
  intro k a b f
  have h := pinned_conjugation (stageEquiv k).functor
    (G k ⋙ apexEquiv.functor)
    (r.transition k)
    (r.comparison k) (r.stageObj k a) (r.stageObj k b)
    (apexEquiv.functor.mapIso (ψ k a) ≪≫ r.apexObj a)
    (apexEquiv.functor.mapIso (ψ k b) ≪≫ r.apexObj b)
    ((r.baseComparison k).app (objects a))
    ((r.baseComparison k).app (objects b))
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.app_hom] using r.object_pin k a)
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.app_hom] using r.object_pin k b) f
  rw [r.transition_pin]
  simpa only [Iso.homCongr_apply, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp,
    Category.assoc, Iso.app_inv, Iso.app_hom] using h


private def completePerfectHomObjectRealization
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (C : Set.Ici i → Type v) [∀ k, Category.{h} (C k)]
    (F : ∀ k, Bool → C k) (D : Type v') [Category.{h'} D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i)) (objects : Bool → schemeDerivedCategory Y)
    (stageEquiv : ∀ k : Set.Ici i, C k ≌
      schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE k.property)))))
    (apexEquiv : D ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (r : PerfectHomObjectRealizationCore R c i C F D O G ψ Y s objects stageEquiv apexEquiv) :
    PerfectHomObjectRealization R c i C F D O G ψ Y s objects where
  stageEquiv := stageEquiv
  apexEquiv := apexEquiv
  stageObj := r.stageObj
  apexObj := r.apexObj
  hom_pin := perfect_overlap_object_realization_hom_pin R c i C F D O G ψ Y s objects
    stageEquiv apexEquiv r

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent overlap expression needs the shared exact-restriction instances.
set_option maxHeartbeats 1600000 in
-- Elaborating the pinned stage and limit comparisons requires this budget.
/-- The object-comparison proposition for the fixed overlap scheme and pullback objects.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization). -/
noncomputable def perfectOverlapObjectRealizationStatement
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : Prop :=
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    Nonempty (
      Σ data : (k : I) → (hjk : j ≤ k) →
        perfectOverlapComparisonDataType R c hc i Z t j hij hstage
          U V hcover hU hV A B hA hB E φU φV k hjk,
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      PerfectHomObjectRealization R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A))

set_option synthInstance.maxHeartbeats 400000 in
-- Shared derived-category comparisons require the exact-restriction instances.
set_option maxHeartbeats 1600000 in
-- Elaborating the cached proposition includes every stage and limit comparison.
/-- The canonical overlap model has compatible object and functor comparisons.
No geometric finiteness, perfectness, or Hom equivalence is supplied by this lemma.
Source: Stacks Project, Tag 09RE, first paragraph of the proof, and the restriction
and composition constructions in Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization).

Proof: For each stage, base change of (U intersection V).toScheme is isomorphic to
(f inverse U intersection f inverse V).toScheme. Construct the isomorphism by the
pullback universal property using the open inclusions; its inverse is the restriction
of the stage projection. Both inverse equations follow by the monomorphism of the
open inclusion and the pullback projection equations. Pullback along this isomorphism
gives stageEquiv. At the limit use the analogous cartesian isomorphism and the derived
inverse of the open-site equivalence to obtain apexEquiv. Restriction of A and B is
derived pullback along the corresponding open inclusion; composition with the
cartesian isomorphisms identifies F with the pullbacks of these fixed objects and
gives stageObj. Restrict the supplied phiU and phiV to the intersection, transport
through the limit cartesian isomorphism, and invert these comparisons to give apexObj.
Construct each diagram's HU, HV and HW as pullback along the restricted limit map
followed by the inverse open-site equivalence. Restriction and composition comparisons
give beta and gamma, with their coherence checked on a K-flat representative where
both paths are termwise tensor pullback followed by restriction. Composition along
X to Yk to Yj gives kappa. The open-site unit and counit give site; set theta equal
to kappa followed by the image of phi followed by site, proving htheta by reflexivity.
The cartesian composition comparison gives comparison, naturally in every overlap
object. Expanding psi, substituting the theta equations and cancelling the site
unit/counit gives the object-comparison equation: restriction coherence cancels gamma
and tau, and associativity of the counit-pinned pullback comparison leaves the
comparison for the fixed overlap structural map. Apply inverse of that equation at
the source and the equation at the target;
expand the image of psi inverse, G(f), psi, use naturality of comparison, and cancel
comparison inverse followed by comparison. The remaining conjugation is exactly
perfectLimitMap by its definition, giving hom_pin. No Hom continuity is used. Empty
opens, coincident opens, zero objects and arbitrary E use the same cartesian and
restriction constructions without a nonemptiness assumption. -/
theorem perfect_overlap_object_realization
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapObjectRealizationStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapObjectRealizationStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  have hcore := perfect_overlap_object_realization_core_data R c hc i Z t j hij hstage
  rw [perfectOverlapObjectRealizationCoreStatement] at hcore
  have hdata := hcore U V hcover hU hV A B hA hB E φU φV
  obtain ⟨⟨data, core⟩⟩ := hdata
  exact ⟨⟨data, completePerfectHomObjectRealization _ _ _ _ _ _ _ _ _ _ _ _ _ _ core⟩⟩

end AlgebraicGeometry
