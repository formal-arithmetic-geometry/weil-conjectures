/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.CompactificationCategory
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Constructibility for compact support on a relative affine line

Source: Stacks Project, Tag 0GKZ, lemma-constructible-shriek-rel-dim-1
(blueprint: lem-weil-pbc-etale-affine-line-shriek-sheaf-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Descent to a finite-type integer base, using connected limits and affine-space base change. -/
private theorem affineLine_constructible_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R)
      (g : Y ⟶ Spec (.of R))
      (F₀ : Sheaf (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)),
      Scheme.IsConstructibleEtaleModuleSheaf F₀ ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F₀ ≅ F) := open CategoryTheory.Limits in by
  classical
  let A := Γ(Y, ⊤)
  have : IsFiltered (Finset A) := inferInstance
  have : IsConnected (Finset A)ᵒᵖ := IsCofiltered.isConnected _
  let D := (finsetSubringDiagram A).op ⋙ Scheme.Spec
  let c₀ := Scheme.Spec.mapCone (finsetSubringCocone A).op
  have hc₀ : IsLimit c₀ :=
    isLimitOfPreserves Scheme.Spec (isColimitFinsetSubringCocone A).op
  let c : Cone D :=
    { pt := Y
      π := { app := fun j ↦ Y.isoSpec.hom ≫ c₀.π.app j
             naturality := by
               intro j k f
               simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                 Category.assoc] using congrArg (Y.isoSpec.hom ≫ ·) (c₀.w f).symm } }
  have hc : IsLimit c := IsLimit.ofIsoLimit hc₀
    (Cone.ext Y.isoSpec (by intro j; rfl)).symm
  let L := AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin 1)))
  let a : D ⋙ L ⟶ D :=
    { app := fun j ↦ AffineSpace (ULift.{u} (Fin 1)) (D.obj j) ↘ D.obj j
      naturality := by intros; exact AffineSpace.map_over _ }
  let cL := L.mapCone c
  have hcL : IsLimit cL := isLimitOfIsPullbackOfIsConnected a cL c
    { hom := AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y
      w := by intro j; exact (AffineSpace.map_over _).symm }
    (fun j ↦ AffineSpace.isPullback_map _) hc
  have htrans : ∀ {j k : (Finset A)ᵒᵖ} (f : j ⟶ k),
      IsAffineHom ((D ⋙ L).map f) := fun f ↦
    by
      change IsAffineHom (AffineSpace.map (ULift.{u} (Fin 1)) (D.map f))
      have : ∀ j, IsAffine (D.obj j) := fun j ↦ inferInstanceAs (IsAffine (Spec _))
      exact isAffineHom_of_isAffine _
  have hcompact : ∀ j, CompactSpace ((D ⋙ L).obj j) := fun j ↦
    inferInstanceAs (CompactSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec _)))
  have hqs : ∀ j, QuasiSeparatedSpace ((D ⋙ L).obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec _)))
  obtain ⟨j, F₀, hF₀, he⟩ :=
    Scheme.exists_constructible_etaleModuleSheaf_descent (D ⋙ L) cL hcL Λ F hF
  let R := Algebra.adjoin ℤ (j : Set A)
  have : Algebra.FiniteType ℤ R :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset j)
  exact ⟨R, inferInstance, inferInstance, c.π.app (Opposite.op j), F₀, hF₀, he⟩

/-- Exact inverse image and compact-support exchange, at a single cohomology sheaf. -/
private theorem compactSupport_homology_baseChange_iso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (c' : Compactification f')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Nonempty
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
      (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c').obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F)))) := by
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  exact ⟨((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    H.mapIso ((asIso
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)).app K) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback sq)).mapIso
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlusSingleFunctor
          0).app F)) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso Λ
      (c.ofIsPullback sq) c').app _)⟩

/-- Noetherian induction, keeping arbitrary closed scheme structures on the subsets. -/
private theorem constructible_of_generic_closed_restrictions
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
      ∃ U : Z.Opens, Dense (U : Set Z) ∧
        Scheme.IsConstructibleEtaleModuleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G))) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr
  suffices h : ∀ C : TopologicalSpace.Closeds Y, ∀ (Z : Scheme.{u}) (i : Z ⟶ Y)
      [IsClosedImmersion i], Set.range i.base ⊆ C →
      Scheme.IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G) by
    have := h ⊤ Y (𝟙 Y) (Set.subset_univ _)
    exact Scheme.IsConstructibleSheaf.of_iso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) Y).app G)
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).obj G)
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hZC
  have : TopologicalSpace.NoetherianSpace Z :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      i.isClosedEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  by_cases hZ : IsEmpty Z
  · exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  rw [not_isEmpty_iff] at hZ
  obtain ⟨U, hUd, hU⟩ := hG Z i
  let i' := Scheme.Opens.closedComplement U
  have hij : Set.range i'.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set Z))
  rw [Scheme.isConstructibleSheaf_iff_upperStar U.ι i' hij]
  refine ⟨(Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hU, ?_⟩
  let C' : TopologicalSpace.Closeds Y :=
    ⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain ⟨z, rfl⟩ := hx
      exact hZC ⟨_, rfl⟩
    · obtain ⟨z, hz⟩ := hUd.nonempty
      have hx : i.base z ∈ (C : Set Y) := hZC ⟨z, rfl⟩
      rw [← h] at hx
      obtain ⟨w, hw⟩ := hx
      rw [Scheme.Hom.comp_apply] at hw
      have hw' : z ∈ Set.range i'.base := ⟨w, i.isClosedEmbedding.injective hw⟩
      rw [hij] at hw'
      exact hw' ⟨⟨z, hz⟩, rfl⟩
  have := ih C' hC' _ (i' ≫ i) subset_rfl
  exact Scheme.IsConstructibleSheaf.of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i' i).app G)

/-- The finite-type case follows by Noetherian induction from its dense-open case. -/
private theorem affineLine_shriek_constructible_of_finiteType
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have : IsNoetherianRing Γ(Y, ⊤) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : TopologicalSpace.NoetherianSpace Y := noetherianSpace_of_isAffine
  apply constructible_of_generic_closed_restrictions Λ Y _
  intro Z i hi
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : Algebra.FiniteType ℤ Γ(Z, ⊤) := by
    let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
    have : Algebra.FiniteType Γ(Y, ⊤) Γ(Z, ⊤) :=
      (RingHom.finiteType_algebraMap).mp
        (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) i inferInstance)
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ Γ(Y, ⊤))
      (inferInstance : Algebra.FiniteType Γ(Y, ⊤) Γ(Z, ⊤))
  let g' := AffineSpace.map (ULift.{u} (Fin 1)) i
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj F
  have hF' : Scheme.IsConstructibleEtaleModuleSheaf F' := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F').mpr
      (Scheme.IsConstructibleSheaf.upperStar g' F)
  let c' := c.ofIsPullback (AffineSpace.isPullback_map i)
  obtain ⟨U, hUd, hU⟩ := exists_dense_open_affineLine_shriek_constructible Λ Z F' hF' c' q
  obtain ⟨e⟩ := compactSupport_homology_baseChange_iso Λ (AffineSpace.isPullback_map i)
    c c' F q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hU
  exact ⟨U, hUd, (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (Scheme.IsConstructibleSheaf.of_iso
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).mapIso e).symm)⟩

/-- Compactly supported cohomology of a constructible module sheaf on the relative affine
line is constructible, for every degree and every compactification.
Source: Stacks Project, Tag 0GKZ (finite commutative coefficient ring specialization).
(blueprint: lem-weil-pbc-etale-affine-line-shriek-sheaf-constructible)

Proof: Express the coordinate ring as the filtered union of the integer subalgebras
generated by finite subsets. The affine-space cartesian squares show that the relative
line is the connected inverse limit of the corresponding lines. Constructible-module
limit descent gives a finite-type integer model of the input. Choose a compactification
of its projection. Exact inverse image, the compact-support exchange isomorphism, the
single-functor comparison and compactification independence identify the original output
with the pullback of the model's output.

For a finite-type integer affine base, use well-founded induction on closed subsets.
Closed subschemes are affine and still have finite-type integer coordinate rings. For
every closed restriction, the dense-open theorem supplies constructibility on a dense
open. Its complement is a strictly smaller closed subset, to which the induction
hypothesis applies. The exact inverse-image and compact-support comparisons identify
these restrictions with the corresponding compact-support outputs. Constructibility
glues along the open and closed parts. Empty schemes have zero sheaves. This proves
constructibility for the finite-type model, and constructible pullback finishes the
arbitrary-base case. The dense-open theorem is proved in the imported module from the
lisse-open-relative-line theorem, quasi-finite shriek constructibility, and the relative
open-closed triangle; its geometric shrinking step is also proved in this delivery.
-/
theorem isConstructibleEtaleModuleSheaf_affineLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  obtain ⟨R, hR, hft, g, F₀, hF₀, ⟨eF⟩⟩ := affineLine_constructible_descent Λ Y F hF
  let c₀ := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u}
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))).1
  have : Algebra.FiniteType ℤ Γ(Spec (.of R), ⊤) :=
    Algebra.FiniteType.equiv hft
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toIntAlgEquiv
  have h₀ := affineLine_shriek_constructible_of_finiteType Λ (Spec (.of R)) F₀ hF₀ c₀ q
  obtain ⟨e⟩ := compactSupport_homology_baseChange_iso Λ (AffineSpace.isPullback_map g)
    c₀ c F₀ q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h₀
  have := Scheme.IsConstructibleSheaf.upperStar g
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c₀).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F₀)))
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (e ≪≫ (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).mapIso
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)))

end AlgebraicGeometry
