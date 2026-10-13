/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # The canonical closed-immersion comparison for units is bijective

Source: Stacks Project, Cohomology, Lemma 02UV, and Varieties, Lemma 09NY
(blueprint: lem-sc-closed-immersion-units-cohomology-comparison-bijective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

private theorem epi_pushforward_closedEmbedding
    {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} Z} (g : F ⟶ G) [Epi g] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map g) := by
  classical
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
  apply (TopCat.Presheaf.isLocallySurjective_iff _).2
  intro U t x hx
  have hg := (TopCat.Presheaf.isLocallySurjective_iff g.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi g).2 inferInstance)
  by_cases hxim : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hxim
    obtain ⟨V, hVU, ⟨s, hs⟩, hz⟩ := hg ((Opens.map i).obj U) t z hx
    let W : Opens X := ⟨U ∩ (i '' (V : Set Z)ᶜ)ᶜ,
      U.isOpen.inter (hi.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
    have hWU : W ≤ U := fun y hy ↦ hy.1
    have hWV : (Opens.map i).obj W ≤ V := by
      intro y hy
      by_contra hyV
      exact hy.2 ⟨y, hyV, rfl⟩
    refine ⟨W, hWU, ⟨F.obj.map (homOfLE hWV).op s, ?_⟩, ?_⟩
    · change g.hom.app (Opposite.op ((Opens.map i).obj W))
        (F.obj.map (homOfLE hWV).op s) =
          G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t
      rw [← ConcreteCategory.comp_apply, g.hom.naturality, ConcreteCategory.comp_apply, hs]
      change G.obj.map (homOfLE hWV).op (G.obj.map (homOfLE hVU).op t) = _
      rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
      rfl
    · exact ⟨hx, fun ⟨y, hy, he⟩ ↦ hy (hi.isEmbedding.injective he ▸ hz)⟩
  · let W : Opens X := ⟨U ∩ (Set.range i)ᶜ, U.isOpen.inter hi.isClosed_range.isOpen_compl⟩
    have hWU : W ≤ U := fun y hy ↦ hy.1
    have he : (Opens.map i).obj W = ⊥ := by
      ext z
      change (i z ∈ U ∧ i z ∉ Set.range i) ↔ False
      exact ⟨fun hz ↦ hz.2 ⟨z, rfl⟩, False.elim⟩
    refine ⟨W, hWU, ⟨0, ?_⟩, hx, hxim⟩
    have ht := G.isTerminalOfEqEmpty he
    have hzero := ConcreteCategory.congr_hom (ht.hom_ext (𝟙 _) 0)
      (G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t)
    change g.hom.app (Opposite.op ((Opens.map i).obj W)) 0 =
      G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t
    rw [map_zero]
    exact hzero.symm


namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 400000 in
-- Comparing the two concrete Ext maps unfolds the sheaf-adjunction construction.
/-- The canonical comparison from cohomology of the direct image of units to cohomology
of units is bijective in every degree.
Source: Stacks Project, Cohomology, Lemma 02UV, and Varieties, Lemma 09NY, the sentence
invoking Lemma 02UV
(blueprint: lem-sc-closed-immersion-units-cohomology-comparison-bijective).

Proof: A closed embedding has exact direct image on abelian sheaves. Direct image also
preserves injectives, since its left adjoint, inverse image, is exact. An injective
resolution of O_Zˣ therefore pushes forward to an injective resolution of i_* O_Zˣ.
Their complexes of global sections are canonically identical, so the induced comparison
is an isomorphism in every degree, as in Lemma 02UV. The map defined by exact inverse
image on Ext, the constant-sheaf identification, and the counit is this comparison:
in degree zero the adjunction triangle identifies it with the identity on sections;
naturality with the connecting maps identifies it in all degrees by dimension shifting
through injective resolutions. Thus the particular unitsPushforwardCohomologyComparison,
not merely some abstract isomorphism, is bijective. This includes degree zero and the
empty closed subscheme, where both sides are zero. -/
theorem bijective_unitsPushforwardCohomologyComparison_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : ℕ) :
    Function.Bijective (unitsPushforwardCohomologyComparison i p) := by
  let g := Opens.map i.base
  let L := g.sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let R := g.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let adj := g.sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) g
  let : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  let := adj.leftAdjoint_preservesColimits
  let := preservesBinaryBiproducts_of_preservesBinaryProducts L
  let := Functor.additive_of_preservesBinaryBiproducts L
  let : (R ⋙ sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).Additive :=
    Functor.additive_of_iso
      (F := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj g.op)
      (Iso.refl _)
  let : R.Additive := Functor.additive_of_comp_faithful R
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let : R.PreservesEpimorphisms :=
    ⟨fun f _ ↦ epi_pushforward_closedEmbedding
      (Scheme.forgetToTop.map i) i.isClosedEmbedding f⟩
  let : PreservesFiniteLimits R := inferInstance
  let : R.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels R
  let : PreservesFiniteColimits R :=
    Functor.preservesFiniteColimits_of_preservesHomology R
  let e := (g.constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
    isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))
  have hb := adj.mapExtCounit_bijective
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) Z.unitsSheaf p
  have hc := (CategoryTheory.Abelian.Ext.precompAddEquiv e Z.unitsSheaf p).bijective.comp hb
  convert hc using 1
  ext x
  change (Sheaf.H.map (adj.counit.app Z.unitsSheaf) p)
    ((Sheaf.H.mapFunctor L e (R.obj Z.unitsSheaf) p) x) =
      (CategoryTheory.Abelian.Ext.precompAddEquiv e Z.unitsSheaf p)
        (adj.mapExtCounit _ Z.unitsSheaf p x)
  rw [Sheaf.H.map_apply, Sheaf.H.mapFunctor_apply,
    Adjunction.mapExtCounit_apply, CategoryTheory.Abelian.Ext.precompAddEquiv_apply]
  exact CategoryTheory.Abelian.Ext.comp_assoc _ _ _
    (zero_add p) (add_zero p) (by omega)

end AlgebraicGeometry.Scheme
