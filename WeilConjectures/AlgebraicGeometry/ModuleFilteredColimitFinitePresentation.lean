/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.FinitePresentationPairsFiltered
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelGermEffacement
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkGermLifting
import WeilConjectures.AlgebraicGeometry.ModuleStalkFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Quasi-coherent modules as filtered colimits of finitely presented modules

Source: Stacks Project, Properties, Lemma 01PJ
(blueprint: lem-weil-pbc-module-filtered-colimit-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on a quasi-compact quasi-separated scheme is a filtered colimit
of modules of finite presentation. Finite presentation is the local finite-free cokernel
condition of Stacks, Modules, Definition 01BN.
Source: Stacks Project, Properties, Lemma 01PJ
(blueprint: lem-weil-pbc-module-filtered-colimit-finite-presentation).

Proof:
1. Use the small filtered family of finitely presented pairs over `F` from
   `exists_finitePresentation_pairs_filtered`, with its diagram and canonical cocone.
2. Form its colimit in `X.Modules` and the comparison map to `F`. The module-stalk
   filtered-colimit theorem identifies each stalk cocone as a colimit. Every element
   of that stalk colimit is represented by a germ at a stage.
3. For a stage germ mapping to zero in `F`, use
   `exists_finitePresentation_quotient_killing_kernel_germ` to obtain a finitely
   presented quotient killing it. Represent the quotient pair in the diagram; the
   quotient map followed by the inverse representing isomorphism is a diagram arrow.
   Cocone naturality makes the original germ zero in the colimit. Thus the comparison
   is injective on stalks.
4. Use `exists_finitePresentation_stalk_germ_lift` to lift any germ of `F` to a
   finitely presented module mapping to `F`. Represent that pair in the diagram and
   apply the inverse representing isomorphism to the lifted germ. Its image in the
   colimit maps to the given germ, proving stalkwise surjectivity.
5. Stalkwise bijectivity gives bijectivity on sections, hence invertibility of the
   module comparison. The resulting isomorphism of cocones transports the colimit
   property to the canonical cocone with vertex `F`. -/
theorem exists_filteredColimit_of_isQuasicoherent
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [SheafOfModules.IsQuasicoherent.{u} (R := X.ringCatSheaf) F] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (M : I ⥤ X.Modules),
      (∀ i : I, SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) (M.obj i)) ∧
        ∃ φ : M ⟶ (Functor.const I).obj F,
          Nonempty (IsColimit (Cocone.mk F φ)) := by
  classical
  obtain ⟨I, G, α, hG, hrep, hfiltered⟩ :=
    exists_finitePresentation_pairs_filtered X F
  let J := ModulePairIndex α
  have : IsFiltered J := hfiltered
  let D := modulePairDiagram α
  let c := modulePairCocone α
  let φ : colimit D ⟶ F := colimit.desc D c
  have hφ (i : J) : colimit.ι D i ≫ φ = α i := colimit.ι_desc c i
  have hb (x : X) : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨hc⟩ := module_stalk_filtered_colimit X x D
      (colimit.cocone D) (colimit.isColimit D)
    have hcomp (i : J) (t : S.obj (G i)) :
        S.map φ (S.map (colimit.ι D i) t) = S.map (α i) t := by
      rw [← ModuleCat.comp_apply, ← S.map_comp, hφ]
      rfl
    constructor
    · apply (injective_iff_map_eq_zero (S.map φ).hom).2
      intro z hz
      obtain ⟨i, t, ht⟩ := Concrete.isColimit_exists_rep (D ⋙ S) hc z
      change S.map (colimit.ι D i) t = z at ht
      have htzero : S.map (α i) t = 0 := by rw [← hcomp, ht, hz]
      have : (G i).IsFinitePresentation := hG i
      obtain ⟨K, ι, _, _, _, _, hQ, hkill, β, hβ⟩ :=
        exists_finitePresentation_quotient_killing_kernel_germ X (G i) F (α i) x t htzero
      obtain ⟨j, e, he⟩ := hrep (cokernel ι) hQ β
      let q : G i ⟶ G j := cokernel.π ι ≫ e.inv
      have hq : q ≫ α j = α i := by
        dsimp [q]
        rw [← he, Category.assoc, Iso.inv_hom_id_assoc, hβ]
      let a : i ⟶ (j : J) := InducedCategory.homMk (Over.homMk q hq)
      have hkill' : S.map q t = 0 := by
        change S.map (cokernel.π ι ≫ e.inv) t = 0
        rw [S.map_comp, ModuleCat.comp_apply]
        change S.map e.inv
          ((PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).map
            (cokernel.π ι).val t) = 0
        rw [hkill, map_zero]
      have hw := (colimit.cocone D).w a
      change q ≫ colimit.ι D j = colimit.ι D i at hw
      rw [← ht, ← hw, S.map_comp, ModuleCat.comp_apply]
      exact (congrArg (S.map (colimit.ι D j)) hkill').trans (map_zero _)
    · intro s
      obtain ⟨H, hH, ψ, t, ht⟩ := exists_finitePresentation_stalk_germ_lift X F x s
      obtain ⟨i, e, he⟩ := hrep H hH ψ
      refine ⟨S.map (colimit.ι D i) (S.map e.inv t), ?_⟩
      rw [hcomp, ← ModuleCat.comp_apply, ← S.map_comp, ← he,
        Iso.inv_hom_id_assoc]
      exact ht
  have : IsIso φ := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
      (F := ⟨(colimit D).presheaf, (colimit D).isSheaf⟩)
      (G := ⟨F.presheaf, F.isSheaf⟩) ⟨φ.mapPresheaf⟩ U (fun x _ ↦ hb x)
  refine ⟨J, inferInstance, inferInstance, D, hG, c.ι, ⟨?_⟩⟩
  let f : colimit.cocone D ⟶ c :=
    { hom := φ
      w := fun i ↦ hφ i }
  have : IsIso f := Cocone.cocone_iso_of_hom_iso f
  exact (colimit.isColimit D).ofIsoColimit (asIso f)

end AlgebraicGeometry.Scheme.Modules
