/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalSectionRestriction
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Properties of module-valued strict-local restriction

Source: Stacks Project, Tags 03Q9 and 03QO; blueprint:
`lem-pur-module-strict-local-restriction-properties`.
-/

@[expose] public section

universe u
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The module geometric stalk is left exact, sections on the strict-local model are
right exact, and the germ restrictions determine a unique natural comparison.
Source: Stacks Project, Tags 03Q9 and 03QO.
(blueprint: lem-pur-module-strict-local-restriction-properties).

The final conjunct quantifies the representative affine pointed neighbourhoods in
the chosen small model.  Its displayed equality is the germ equation: the canonical
germ into the module stalk followed by the comparison equals the restriction map
defined by `moduleStrictLocalSectionRestriction`.

Proof (blueprint node, five steps):
1. Finite limits (prop-weil-pbc-geometric-stalks-exact, def-weil-pbc-geometric-stalks):
   the geometric stalk is a filtered colimit over the `u`-small pointed neighbourhoods;
   `ModuleCat A` satisfies AB5 (shrunk from universe `u + 1` to `u`), sheaf limits are
   sectionwise, so the generic `sheafFiber` instance gives left exactness, also for the
   empty diagram and the zero ring.
2. Finite colimits (lem-weil-pbc-strict-henselization-local-structure,
   lem-sbc-strict-henselian-etale-neighbourhood-section): `R = strictHenselizationRing s`
   is strictly henselian local, so an epimorphism of module sheaves on `S = Spec R` is
   surjective on sections over the terminal etale object.  Transported along
   `Sheaf.ΓNatIsoSheafSections`, global sections preserve epimorphisms; being additive
   and a right adjoint they preserve kernels, hence homology and finite colimits.
3. Descent (def-weil-pbc-small-strict-local-section-cone,
   def-weil-pbc-strict-henselization-limit, lem-weil-pbc-colimit-initial-full-subcategory(1)):
   the chosen affine representatives form an initial full subcategory of the pointed
   neighbourhoods, so their germs form a colimit cocone.  With `H = g⁻¹F`, unit `η`, and
   compatible sections `σ_i` (`(t ×_B S) σ_i = σ_j`), the restrictions
   `d_i = H(σ_i) η_{V_i}` satisfy `d_i F(t) = H((t ×_B S) σ_i) η_{V_j} = d_j`; the
   terminal-object comparison preserves this, so a unique linear `r_F` has `r_F ι_i = d_i`.
4. Naturality: for `α : F ⟶ F'`, `Γ(S, g⁻¹α) d_{i,F} = d_{i,F'} α_{V_i}`, so
   `Γ(S, g⁻¹α) r_F` and `r_{F'} α_s` agree on every germ and are equal by colimit
   uniqueness.
5. Uniqueness: any other transformation with the germ equations has each component equal
   to `r_F` by the uniqueness of step 3, hence equals `r` by `NatTrans.ext`.
-/
theorem moduleStrictLocalRestriction_properties
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteLimits
        ((Scheme.pointSmallEtale s).sheafFiber
          (A := ModuleCat.{u + 1} A)) ∧
      PreservesFiniteColimits
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A)) ∧
      ∃! r :
          (Scheme.pointSmallEtale s).sheafFiber
              (A := ModuleCat.{u + 1} A) ⟶
            upperStar (ModuleCat.{u + 1} A)
                (Scheme.strictHenselizationStructuralMap s) ⋙
              Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
                (ModuleCat.{u + 1} A),
        ∀ (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
          (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)),
          (Scheme.pointSmallEtale s).toPresheafFiber
              ((Scheme.AffineEtale.Spec B).obj
                ((equivSmallModel.{u}
                  (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
              ((equivSmallModel.{u}
                (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 F.obj ≫
            r.app F =
          moduleStrictLocalSectionRestriction A s F j := by
  classical
  have h_exists : ∀ (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃! r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A)).obj
          ((upperStar (ModuleCat.{u + 1} A)
            (Scheme.strictHenselizationStructuralMap s)).obj F),
        ∀ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)),
          (Scheme.pointSmallEtale s).toPresheafFiber
              ((Scheme.AffineEtale.Spec B).obj
                ((equivSmallModel.{u}
                  (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
              ((equivSmallModel.{u}
                (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 F.obj ≫
            r = moduleStrictLocalSectionRestriction A s F j := by
    intro F
    let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    have : N.Initial := (Scheme.strictHenselization_properties s).1
    let k := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
    let hk : IsColimit k :=
      (Functor.Final.isColimitWhiskerEquiv N.op _).symm
        ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
    let d : Cocone (N.op ⋙ (CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).op ⋙
        F.obj) :=
      { pt := (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A)).obj
          ((upperStar (ModuleCat.{u + 1} A)
            (Scheme.strictHenselizationStructuralMap s)).obj F)
        ι := { app i := moduleStrictLocalSectionRestriction A s F i.unop
               naturality := by
                 intro i j a
                 dsimp
                 simp only [Category.comp_id, moduleStrictLocalSectionRestriction]
                 let t := (CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).map
                   (N.map a.unop)
                 rw [← Category.assoc, ← Category.assoc]
                 erw [((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                   (Scheme.strictHenselizationStructuralMap s)).unit.app F).hom.naturality t.op]
                 simp only [Category.assoc]
                 let H := (upperStar (ModuleCat.{u + 1} A)
                   (Scheme.strictHenselizationStructuralMap s)).obj F
                 change _ ≫
                   H.obj.map ((Scheme.strictHenselizationStructuralMap s).Etale.map t).op ≫
                   H.obj.map (strictLocalNeighbourhoodSection s j.unop).op ≫ _ = _
                 have hnat := (strictLocalSectionCone s).naturality a.unop
                 change strictLocalNeighbourhoodSection s j.unop ≫
                   (Scheme.strictHenselizationStructuralMap s).Etale.map t =
                     strictLocalNeighbourhoodSection s i.unop at hnat
                 rw [← H.obj.map_comp_assoc, ← op_comp, hnat]
                 rfl } }
    refine ⟨hk.desc d, ?_, ?_⟩
    · intro j
      exact hk.fac d (op j)
    · intro r hr
      apply hk.hom_ext
      intro j
      exact (hr j.unop).trans (hk.fac d j).symm
  let r : (Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A)
          (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          (ModuleCat.{u + 1} A) := {
    app := fun F ↦ (h_exists F).choose
    naturality := by
      intro F G a
      let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
        Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
      have : N.Initial := (Scheme.strictHenselization_properties s).1
      let k := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
      let hk : IsColimit k :=
        (Functor.Final.isColimitWhiskerEquiv N.op _).symm
          ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
      apply hk.hom_ext
      intro j
      have hF := (Classical.choose_spec (h_exists F)).1
      have hG := (Classical.choose_spec (h_exists G)).1
      change (Scheme.pointSmallEtale s).toPresheafFiber
          ((Scheme.AffineEtale.Spec B).obj
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              j.unop).1)
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j.unop).2 F.obj ≫ _ = _
      erw [← Category.assoc,
        (Scheme.pointSmallEtale s).toPresheafFiber_naturality a.hom, Category.assoc]
      erw [hG j.unop]
      have hF' : k.ι.app j ≫ Classical.choose (h_exists F) =
          moduleStrictLocalSectionRestriction A s F j.unop := hF j.unop
      conv_rhs => rw [← Category.assoc, hF']
      dsimp [moduleStrictLocalSectionRestriction]
      simp only [Category.assoc]
      let g := Scheme.strictHenselizationStructuralMap s
      let W := (Scheme.AffineEtale.Spec B).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
          j.unop).1
      let V := Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))
      have hu := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.naturality a
      have he := congrArg (fun b ↦ b.hom.app (Opposite.op W)) hu
      dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
        at he
      rw [← Category.assoc, ← Category.assoc]
      erw [he]
      simp only [Category.assoc]
      have hn := ((upperStar (ModuleCat.{u + 1} A) g).map a).hom.naturality
        (strictLocalNeighbourhoodSection s j.unop).op
      erw [← reassoc_of% hn]
      have ht := ((Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
            (Scheme.strictHenselizationScheme s)) V Over.mkIdTerminal)).inv).naturality
        ((upperStar (ModuleCat.{u + 1} A) g).map a)
      change ((upperStar (ModuleCat.{u + 1} A) g).map a).hom.app (Opposite.op V) ≫ _ = _ at ht
      erw [ht] }
  have hcolim : PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)) := by
    obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure s
    let := hlocal
    let := hstrict
    let E := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      (ModuleCat.{u + 1} A)
    have hE : ((sheafSections (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)).obj
          (op (Scheme.etaleTerminal (Scheme.strictHenselizationRing s)))).PreservesEpimorphisms :=
      ⟨fun f _ ↦ (ModuleCat.epi_iff_surjective _).2
        (Scheme.surjective_app_of_epi_of_isStrictlyHenselianLocalRing
          (Scheme.strictHenselizationRing s) f)⟩
    have : E.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} A)
        (Scheme.isTerminalEtaleTerminal (Scheme.strictHenselizationRing s))).symm
    have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
    exact E.preservesFiniteColimits_of_preservesHomology
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} A) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  refine ⟨inferInstance, hcolim, ?_⟩
  refine ⟨r, ?_, ?_⟩
  · intro F j
    exact (Classical.choose_spec (h_exists F)).1 j
  · intro r' hr'
    apply NatTrans.ext
    funext F
    apply (Classical.choose_spec (h_exists F)).2
    intro j
    exact hr' F j

end AlgebraicGeometry.Etale
