/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.SplitLocalClopenFinite
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finiteness of quasi-compact clopen pieces of strictly locally split étale schemes

Source: the finite-sheet and limit-descent argument in
`lem-sf-normal-strict-local-split-components`, steps 6--9; Stacks Project, Tags 01ZO and 02LA
(blueprint: lem-sf-strict-local-split-clopen-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

private theorem finite_neighbourhood_of_strictLocal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    [IsFinite (pullback.snd f (Scheme.strictHenselizationStructuralMap s))] :
    ∃ (V : Scheme.{u}) (g : V ⟶ X), Etale g ∧
      IsFinite (pullback.snd f g) ∧ Set.range s ⊆ Set.range g := by
  classical
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let D := (Scheme.strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec
  let c := Scheme.strictHenselizationCone s
  let J := (SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))ᵒᵖᵒᵖ
  have := (Scheme.strictHenselization_properties s).2.1
  have : IsCofiltered J := inferInstance
  have hlim : IsLimit c := (Scheme.strictHenselization_properties s).2.2.some
  let b (i : J) : D.obj i ⟶ X :=
    Spec.map (ΓSpecIso (N.obj i.unop.unop).1.left.unop).inv ≫
      ((Scheme.AffineEtale.Spec X).obj (N.obj i.unop.unop).1).hom
  have hb (i : J) : Etale (b i) := by dsimp [b]; infer_instance
  have hc (i : J) : c.π.app i ≫ b i =
      Scheme.strictHenselizationStructuralMap s := by
    exact Classical.choose_spec (Scheme.exists_strictHenselizationStructuralMap s)
      i.unop.unop
  have hnat {i j : J} (u : i ⟶ j) : D.map u ≫ b j = b i := by
    let v := (N.map u.unop.unop).1.left.unop
    have hv := congrArg Spec.map (ΓSpecIso_inv_naturality v)
    simp only [Spec.map_comp] at hv
    have hw : Spec.map v ≫
        ((Scheme.AffineEtale.Spec X).obj (N.obj j.unop.unop).1).hom =
        ((Scheme.AffineEtale.Spec X).obj (N.obj i.unop.unop).1).hom :=
      (N.map u.unop.unop).1.w
    change Spec.map (Spec.map v).appTop ≫
      Spec.map (ΓSpecIso (N.obj j.unop.unop).1.left.unop).inv ≫ _ = _
    rw [← Category.assoc, ← hv, Category.assoc, hw]
  have (i : J) : IsAffine (D.obj i) := inferInstanceAs (IsAffine (Spec _))
  have {i j : J} (u : i ⟶ j) : IsAffineHom (D.map u) := isAffineHom_of_isAffine _
  have (i : J) : CompactSpace (D.obj i) := inferInstance
  have (i : J) : QuasiSeparatedSpace (D.obj i) := inferInstance
  let i : J := Classical.choice (IsCofiltered.nonempty (C := J))
  let p := pullback.snd f (b i)
  have : IsFinite (pullback.snd p (c.π.app i)) := by
    rw [← isFinite_pullback_snd_comp_iff, hc]
    infer_instance
  obtain ⟨j, u, hu⟩ := Scheme.exists_isFinite_pullback_snd_of_isLimit hlim p
  have hj : IsFinite (pullback.snd f (b j)) := by
    rw [← isFinite_pullback_snd_comp_iff, hnat] at hu
    exact hu
  refine ⟨D.obj j, b j, hb j, hj, ?_⟩
  rintro _ ⟨z, rfl⟩
  let lift : Spec (.of Ω) ⟶ D.obj j :=
    (N.obj j.unop.unop).2.left ≫ Spec.map (ΓSpecIso
      (N.obj j.unop.unop).1.left.unop).hom
  refine ⟨lift z, ?_⟩
  have hl : lift ≫ b j = s := by
    change ((N.obj j.unop.unop).2.left ≫
      Spec.map (ΓSpecIso (N.obj j.unop.unop).1.left.unop).hom) ≫
      (Spec.map (ΓSpecIso (N.obj j.unop.unop).1.left.unop).inv ≫
        ((AffineEtale.Spec X).obj (N.obj j.unop.unop).1).hom) = s
    rw [Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
    exact Over.w (N.obj j.unop.unop).2
  exact congrArg (fun h : Spec (.of Ω) ⟶ X ↦ h z) hl

private theorem isFinite_of_strictLocal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsFinite (pullback.snd f (Scheme.strictHenselizationStructuralMap s))) :
    IsFinite f := by
  classical
  have he (x : X) : ∃ (V : Scheme.{u}) (g : V ⟶ X), Etale g ∧
      IsFinite (pullback.snd f g) ∧ x ∈ Set.range g := by
    let Ω := AlgebraicClosure (X.residueField x)
    let s : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫
        X.fromSpecResidueField x
    have := h Ω s
    obtain ⟨V, g, hg, hf, hs⟩ := finite_neighbourhood_of_strictLocal f s
    refine ⟨V, g, hg, hf, hs ?_⟩
    refine ⟨IsLocalRing.closedPoint Ω, ?_⟩
    change (X.fromSpecResidueField x) _ = x
    exact X.fromSpecResidueField_apply x _
  choose V g hg hf hx using he
  have hg' : Presieve.ofArrows V g ∈ Scheme.fppfPrecoverage X := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨x, hx x⟩, fun x ↦ ?_⟩
    have := hg x
    exact ⟨inferInstance, inferInstance⟩
  exact isFinite_of_fpqc_cover f V g
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage X hg') hf

/-- A quasi-compact clopen part of a separated étale scheme that is split over every
strict localization is finite over the Noetherian base. No connectedness or normality
hypothesis is needed here.

Source: Stacks Project, Tags 01ZO, 081D and 02LA; the strict-local finite-sheet argument
in `lem-sf-normal-strict-local-split-components`, steps 6--9
(blueprint: lem-sf-strict-local-split-clopen-finite).

Proof:
1. Fix a geometric point s. The strict henselization is the spectrum of a nonzero local
   ring, hence connected. Pullback of the clopen part is clopen in the given coproduct
   of copies of this spectrum. Its intersection with each connected sheet is either
   empty or the whole sheet. Quasi-compactness of its map and affineness of the strict
   localization imply only finitely many sheets occur. A finite coproduct of copies
   of Spec R is Spec of a finite product of R, hence finite over Spec R.
2. Express the strict localization as an inverse limit of pointed affine étale
   neighbourhoods with affine transitions, using `strictHenselization_properties`.
   Each stage is affine, hence quasi-compact and quasi-separated. The component map
   is quasi-compact, separated and locally of finite type, as are its base changes.
3. Apply the source library's `Scheme.exists_isFinite_pullback_snd_of_isLimit`
   directly to this cofiltered category. This gives a pointed affine étale
   neighbourhood on which the map is finite; no directed reindexing is required.
4. Such neighbourhoods cover the base, by choosing geometric points over all base
   points. They form an fppf family, hence an fpqc family. Apply
   `isFinite_of_fpqc_cover`. The empty clopen piece is included.
-/
theorem isFinite_clopen_of_strictLocal_split
    {X T : Scheme.{u}} [IsNoetherian X]
    (q : T ⟶ X) [IsSeparated q] [Etale q]
    (hsplit : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ (I : Type u)
        (ι : I → (Scheme.strictHenselizationScheme s ⟶
          pullback q (Scheme.strictHenselizationStructuralMap s))),
        (∀ i : I, ι i ≫ pullback.snd q (Scheme.strictHenselizationStructuralMap s) =
          𝟙 (Scheme.strictHenselizationScheme s)) ∧
        Nonempty (IsColimit (Cofan.mk
          (pullback q (Scheme.strictHenselizationStructuralMap s)) ι)))
    (U : T.Opens) (hclosed : IsClosed (U : Set T))
    [QuasiCompact (U.ι ≫ q)] : IsFinite (U.ι ≫ q) := by
  classical
  apply isFinite_of_strictLocal (U.ι ≫ q)
  intro Ω _ _ s
  let ρ := Scheme.strictHenselizationStructuralMap s
  let V := pullback.fst q ρ ⁻¹ᵁ U
  have hsq := (isPullback_morphismRestrict (pullback.fst q ρ) U).paste_vert
    (IsPullback.of_hasPullback q ρ)
  have : QuasiCompact (V.ι ≫ pullback.snd q ρ) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  obtain ⟨hlocal, _⟩ := strictHenselizationLocalStructure s
  let := hlocal
  obtain ⟨I, ι, hι, hc⟩ := hsplit Ω s
  have : IsFinite (V.ι ≫ pullback.snd q ρ) :=
    isFinite_clopen_of_coproduct_sections (Scheme.strictHenselizationRing s)
      (pullback.snd q ρ) ι hι hc V
      (hclosed.preimage (pullback.fst q ρ).continuous)
  rw [← hsq.isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry
