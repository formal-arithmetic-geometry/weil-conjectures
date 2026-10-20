/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectHomPresentation
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization

/-! # Geometric Hom presentation on a compact two-open overlap

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-hom-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- Assemble the geometric finiteness and perfectness with object comparisons. -/
private noncomputable def homPresentationOfObjects
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (C : Set.Ici i → Type*) [∀ k, Category* (C k)]
    (F : ∀ k, Bool → C k) (D : Type*) [Category* D]
    (O : Bool → D) (G : ∀ k, C k ⥤ D)
    (ψ : ∀ k b, (G k).obj (F k b) ≅ O b)
    (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    (objects : Bool → schemeDerivedCategory Y)
    (lfp : LocallyOfFinitePresentation s) (qc : QuasiCompact s) (qs : QuasiSeparated s)
    (perfect : ∀ b, Y.IsPerfect (objects b))
    (r : PerfectHomObjectRealization R c i C F D O G ψ Y s objects) :
    PerfectHomPresentation R c i C F D O G ψ where
  Y := Y
  s := s
  lfp := lfp
  qc := qc
  qs := qs
  P := objects
  perfect := perfect
  stage k a b := (r.stageEquiv k).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (r.stageObj k a) (r.stageObj k b))
  apex a b := r.apexEquiv.fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (r.apexObj a) (r.apexObj b))
  stage_id k a := by
    simp
  stage_comp k a b d f g := by
    simp
  pin k a b f := by
    exact r.hom_pin k a b f

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent overlap expression needs the shared exact-restriction instances.
set_option maxHeartbeats 1600000 in
-- Elaborating the pinned stage and limit comparisons requires this budget.
/-- The geometric presentation proposition, with its dependent expressions cached.
This is the exact proposition of `perfect_overlap_hom_presentation`.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-hom-presentation). -/
noncomputable def perfectOverlapHomPresentationStatement
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
      PerfectHomPresentation R c j C F _ (fun _ ↦ RW.obj E) G ψ)

set_option synthInstance.maxHeartbeats 400000 in
-- The cached statement exposes the shared exact-restriction instances.
set_option maxHeartbeats 1600000 in
-- The reduction unfolds the cached stage categories and their realization data.
/-- The exact overlap Hom sets admit a pinned geometric presentation.
No morphism lifting, eventual equality, or stage transport is asserted here.
Source: Stacks Project, Tag 09RE, restriction to quasi-compact opens in the proof
of lemma-descend-homomorphisms; Tags 08DW and 0D5S for the comparisons.
(blueprint: lem-pc-perfect-overlap-hom-presentation).

Proof: Put W = (U intersection V).toScheme over Spec(R_j). Quasi-separatedness
of Y_j makes U intersection V compact. Thus W has a quasi-compact open immersion
into Y_j, and its structural map is locally finitely presented, quasi-compact and
quasi-separated. Restrict A and B along the two open immersions into U and V;
these restrictions are derived pullbacks and are perfect by pullback preservation.
Use these as P(false) and P(true). At each k, the pullback of W over R_k is
canonically isomorphic to the intersection of the inverse-image opens in Y_k,
by the universal properties of open immersions and the cartesian base-change
squares. The same identification holds over the colimit ring.
Construct HU, HV and HW as derived pullback on the corresponding open subschemes
followed by the inverse open-site equivalences. Composition of derived pullback
and its restriction comparison give beta and gamma; their coherence follows by
computing both paths on a K-flat representative, where both are the same
restriction of termwise tensor pullback. The composition comparison along
X -> Y_k -> Y_j supplies kappa. The unit and counit of each open-site equivalence
supply siteU and siteV. Define theta by kappa followed by the image of the supplied
phi and then site, giving both required theta equations.
Conjugation by the cartesian object identifications gives the stage Hom
equivalences. Identify the limit objects with RW(E) by restricting phiU and phiV
and applying the same cartesian and open-site equivalences. Conjugation by those
isomorphisms and the fully faithful site equivalence gives the apex Hom
equivalences. Functoriality and cancellation of an isomorphism with its inverse
prove stage_id and stage_comp. For pin, expand psi as gamma inverse followed
by the image of theta and tau. Substitute the defining theta equations; the
restriction-composition coherence cancels the site comparisons, and associativity
of the counit-pinned pullback composition comparisons leaves precisely
perfectLimitMap. This constructs only comparisons and perfect objects, without
using the Hom-colimit theorem. Empty and coincident opens obey the same cartesian
identifications, and no nonemptiness of the overlap is needed. -/
theorem perfect_overlap_hom_presentation
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
    : perfectOverlapHomPresentationStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapHomPresentationStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  let W := U ⊓ V
  let s : W.toScheme ⟶ Spec (R.obj j) :=
    W.ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij)))
  have : QuasiSeparatedSpace Yj :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd t (Spec.map (R.map (homOfLE hij))))
  have hW : IsCompact (W : Set Yj) :=
    hU.inter_of_isOpen hV U.isOpen V.isOpen
  have : CompactSpace W.toScheme :=
    (isCompact_iff_compactSpace).mp hW
  have hsfp : LocallyOfFinitePresentation s := by dsimp [s]; infer_instance
  have hsqc : QuasiCompact s := by infer_instance
  have hsqs : QuasiSeparated s := by dsimp [s]; infer_instance
  let objects : Bool → schemeDerivedCategory W.toScheme := fun b ↦
    if b then (derivedPullback (Yj.homOfLE (inf_le_right : W ≤ V))).obj B
    else (derivedPullback (Yj.homOfLE (inf_le_left : W ≤ U))).obj A
  have hobjects : ∀ b, W.toScheme.IsPerfect (objects b) := by
    intro b
    cases b
    · exact derivedPullback_preserve_perfect _ A hA
    · exact derivedPullback_preserve_perfect _ B hB
  have hr := perfect_overlap_object_realization R c hc i Z t j hij hstage
  unfold perfectOverlapObjectRealizationStatement at hr
  have hr' := hr U V hcover hU hV A B hA hB E φU φV
  obtain ⟨pair⟩ := hr'
  let data := pair.1
  have realization := pair.2
  refine ⟨⟨data, ?_⟩⟩
  intro K C F G ψ
  exact homPresentationOfObjects R c j C F _ (fun _ ↦ RW.obj E) G ψ W.toScheme s objects
    hsfp hsqc hsqs hobjects realization

end AlgebraicGeometry
