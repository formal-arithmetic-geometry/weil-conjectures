/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Noetherian
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen
import Sheaf.AlgebraicGeometry.NormalOpenLisseImage

/-!
# Constructibility of degree-zero open direct images over a field

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/thm-fin-open-degree-zero.md`,
statement and proof paragraphs 1–4 (blueprint: thm-fin-open-degree-zero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem integral_image {S T : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ T) [QuasiCompact f] : IsIntegral f.image := by
  have : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def _).mpr
    have h := (IrreducibleSpace.isIrreducible_univ S).image f.toImage.base
      f.toImage.continuous.continuousOn
    rw [Set.image_univ] at h
    simpa [f.toImage.denseRange.closure_eq] using h.closure
  have : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  exact isIntegral_of_irreducibleSpace_of_isReduced _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_constructible_stalk_test
    {k : Type u} [Field k] {X U : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (x : U) :
    ∃ (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (φ : F ⟶ G),
      Mono ((pointSmallEtale (U.algClosurePoint x)).sheafFiber.map φ) ∧
        IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj G) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have : TopologicalSpace.NoetherianSpace U := j.isEmbedding.noetherianSpace
  have : IsNoetherian U := {}
  let I := IdealSheafData.vanishingIdeal
    (⟨closure {x}, isClosed_closure⟩ : TopologicalSpace.Closeds U)
  let i := I.subschemeι
  have hi : Set.range i = closure {x} := by
    simp [i, I, IdealSheafData.range_subschemeι]
  have : IrreducibleSpace I.subscheme := by
    have : IrreducibleSpace (Set.range i) :=
      Subtype.irreducibleSpace (hi.symm ▸ isIrreducible_singleton.closure)
    exact i.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F) :=
    IsConstructibleSheaf.upperStar i F
  obtain ⟨D, hd, hD⟩ := IsConstructibleSheaf.exists_dense_open
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)
  have : Nonempty D := hd.nonempty.to_subtype
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  have : TopologicalSpace.NoetherianSpace I.subscheme := i.isEmbedding.noetherianSpace
  have : IsNoetherian I.subscheme := {}
  have : IsLocallyNoetherian D.toScheme := inferInstance
  have : CompactSpace D.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (D : Set I.subscheme))
  have : IsNoetherian D.toScheme := {}
  let f : D.toScheme ⟶ Spec (.of k) := D.ι ≫ i ≫ j ≫ X ↘ Spec (.of k)
  have : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  have : QuasiCompact f := inferInstance
  obtain ⟨V, hV, hnV⟩ := exists_nonempty_normal_open f
  have : Nonempty V := hV
  have hnormal : IsNormalScheme V := by
    refine ⟨inferInstance, fun v ↦ ⟨inferInstance, ?_⟩⟩
    exact IsIntegrallyClosed.of_equiv
      (V.stalkIso v).commRingCatIsoToRingEquiv.symm (h := hnV v.1 v.2)
  let h : V.toScheme ⟶ U := V.ι ≫ D.ι ≫ i
  let a : V.toScheme ⟶ X := h ≫ j
  have : QuasiCompact a := inferInstance
  have : IsIntegral a.image := integral_image a
  let L := (Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj F
  have : IsFiniteLocallyConstantSheaf L := by
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) D.ι).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) := hD
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.ι ≫ i)).obj F) :=
      IsFiniteLocallyConstantSheaf.of_iso
        (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) D.ι).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F))
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) D.ι i).app F).symm
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.ι ≫ i)).obj F)) :=
      IsFiniteLocallyConstantSheaf.upperStar V.ι _
    exact IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.ι ≫ i)).obj F))
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) V.ι (D.ι ≫ i)).app F).symm
  let : a.image.Over (Spec (.of k)) := ⟨a.imageι ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (a.image ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (a.imageι ≫ X ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (a.image ↘ Spec (.of k)) := by
    change QuasiCompact (a.imageι ≫ X ↘ Spec (.of k))
    infer_instance
  have hL := isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open (K := k) a.toImage hnormal L
  have : IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) a.toImage).obj L) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hL
  have hc := IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact a.imageι
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) a.toImage).obj L)
  have hpush : IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj L)) := by
    have := hc
    exact IsConstructibleSheaf.of_iso
      (F := (Etale.lowerStar (ModuleCat.{u + 1} Λ) a.imageι).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) a.toImage).obj L))
      ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) a.toImage a.imageι a
          a.toImage_imageι.symm).app L ≪≫
        ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h j).app L).symm)
  have hx : x ∈ Set.range h := by
    obtain ⟨z, hz⟩ : x ∈ Set.range i := hi.symm ▸ subset_closure rfl
    obtain ⟨v⟩ := hV
    have hs : z ⤳ D.ι (V.ι v) := by
      rw [← i.isEmbedding.isInducing.specializes_iff, hz, specializes_iff_mem_closure]
      exact hi ▸ Set.mem_range_self _
    have hzD : z ∈ D := hs.mem_open D.isOpen (V.ι v).2
    have hzV : (⟨z, hzD⟩ : D.toScheme) ∈ V := by
      have hs' : (⟨z, hzD⟩ : D.toScheme) ⤳ V.ι v := by
        rw [← D.ι.isEmbedding.isInducing.specializes_iff]
        exact hs
      exact hs'.mem_open V.isOpen v.2
    exact ⟨⟨⟨z, hzD⟩, hzV⟩, hz⟩
  obtain ⟨s, hs⟩ := exists_comp_eq_of_mem_range h (U.algClosurePoint x) (by
    simpa only [algClosurePoint_base] using hx)
  refine ⟨_, (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F,
    ?_, hpush⟩
  rw [← hs]
  let e := Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) h s
  have he := e.inv.naturality
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F)
  rw [Functor.comp_map] at he
  have hfac : (pointSmallEtale (s ≫ h)).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F) ≫
      e.inv.app _ ≫ (pointSmallEtale s).sheafFiber.map
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app L) =
      e.inv.app F := by
    dsimp only [Functor.comp_obj, Functor.id_obj] at he ⊢
    calc
      _ = ((pointSmallEtale (s ≫ h)).sheafFiber.map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F) ≫
          e.inv.app _) ≫ (pointSmallEtale s).sheafFiber.map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app L) :=
        (Category.assoc _ _ _).symm
      _ = (e.inv.app F ≫ (pointSmallEtale s).sheafFiber.map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F))) ≫
          (pointSmallEtale s).sheafFiber.map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app L) :=
        congrArg (fun t ↦ t ≫ (pointSmallEtale s).sheafFiber.map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app L)) he
      _ = _ := by
        rw [Category.assoc, ← Functor.map_comp]
        change e.inv.app F ≫ (pointSmallEtale s).sheafFiber.map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app F) ≫
            (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj F)) = _
        rw [Adjunction.left_triangle_components, CategoryTheory.Functor.map_id]
        exact Category.comp_id (e.inv.app F)
  have : Mono (e.inv.app F) := mono_of_mono_fac (e.inv_hom_id_app F)
  exact mono_of_mono_fac hfac

/-- The direct image of a constructible etale module sheaf under an open immersion into
 a scheme of finite type over a field is constructible, for every finite commutative
 coefficient ring.

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/thm-fin-open-degree-zero.md`,
statement and proof paragraphs 1–4 (blueprint: thm-fin-open-degree-zero).

Proof:
For each point of `U`, take a nonempty normal lisse open in its reduced closure.
Its unit map into the direct image of the restricted sheaf is injective at that point's
geometric stalk. The direct image of this restricted sheaf on `X` is constructible:
factor its immersion into `X` through its integral scheme-theoretic image, apply
`lem-fin-normal-open-lisse-image`, then push along the closed immersion.
Noetherian finite selection produces an injection from `F` into a finite product of
these sheaves. The functor `j_*` preserves this injection and the finite product.
Constructibility of finite products and subsheaves on Noetherian schemes finishes
the proof. No exactness beyond left exactness of the direct image is required. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_openImmersion_over_field
    {k : Type u} [Field k] {X U : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F) := by
  classical
  let := Abelian.hasFiniteBiproducts
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have : TopologicalSpace.NoetherianSpace U := j.isEmbedding.noetherianSpace
  have : IsNoetherian U := {}
  have : IsConstructibleSheaf F :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  choose G φ hmono hpush using exists_constructible_stalk_test (k := k) j F
  obtain ⟨S, hS⟩ := Etale.exists_finset_mono_pi_lift F G φ (by
    intro x v hv
    refine ⟨x, ?_⟩
    have := hmono x
    exact fun h ↦ hv ((ModuleCat.mono_iff_injective _).mp (hmono x)
      (by simpa using h)))
  have := hS
  have (x : S) : IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G x)) := hpush x
  have hprod : IsConstructibleSheaf
      (∏ᶜ fun x : S ↦ (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G x)) := by
    let e := S.equivFin.symm
    have : IsConstructibleSheaf (⨁ fun n : Fin S.card ↦
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G (e n))) :=
      IsConstructibleSheaf.biproduct _
    have : IsConstructibleSheaf (∏ᶜ fun n : Fin S.card ↦
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G (e n))) :=
      IsConstructibleSheaf.of_iso (Limits.biproduct.isoProduct _)
    exact IsConstructibleSheaf.of_iso (Limits.Pi.whiskerEquiv
      (f := fun n : Fin S.card ↦ (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G (e n)))
      (g := fun x : S ↦ (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (G x)) e
      (fun _ ↦ Iso.refl _))
  have : IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj (∏ᶜ fun x : S ↦ G x)) :=
    IsConstructibleSheaf.of_iso
      (Limits.PreservesProduct.iso (Etale.lowerStar (ModuleCat.{u + 1} Λ) j)
        (fun x : S ↦ G x)).symm
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (IsConstructibleSheaf.of_mono
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).map (Limits.Pi.lift fun x : S ↦ φ x)))

end AlgebraicGeometry.Scheme
