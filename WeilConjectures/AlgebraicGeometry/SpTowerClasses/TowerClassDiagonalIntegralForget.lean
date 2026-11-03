/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import all WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Forgetting support in the integral diagonal boundary

Source: latest blueprint geometric tower classes, clause (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem pole_forget {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    (Ext.mk₀ (supportedIntegralUnit i)).comp (cartierPoleBoundary i hI) (zero_add 1) =
      Scheme.Pic.toCohomologicalPicardGroup T
        (@Scheme.Pic.ofIsInvertible T (Scheme.Modules.dual i.ker.toModules)
          hI.isInvertible_dual_toModules) := by
  classical
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  let W : T.Opens :=
    ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hβ⟩ :=
    (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).1 W rfl
  let P := Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)
  let terminal := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let s := (supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    (supportedIntegralOne T)
  let Q := Sheaf.Torsor.lifts terminal hE s
  have hp : Sheaf.Torsor.classH1 T.gmSheaf terminal ⟦P⟧ =
      Sheaf.H.δ hE terminal s := by
    have heq := Sheaf.Torsor.classH1_eq_map_of_equivariant terminal (𝟙 T.gmSheaf) P Q
      (fun U p ↦ ⟨f.hom.app U p, hb U p⟩)
      (fun U V g p ↦ Subtype.ext (by
        change E.obj.map g (f.hom.app U p) = f.hom.app V (P.sheaf.obj.map g p)
        exact ConcreteCategory.congr_hom (f.hom.naturality g).symm p))
      (fun U g p ↦ Subtype.ext (by
        change f.hom.app U (P.vadd U g p) = (@id (E.obj.obj U) (f.hom.app U p)) + a.hom.app U g
        simpa only [id_eq, P, add_comm] using hf U g p))
    rw [Sheaf.Torsor.classH1_lifts] at heq
    simpa only [Sheaf.H.map_apply, Ext.comp_mk₀_id] using heq.symm
  have hpic : Scheme.Pic.toCohomologicalPicardGroup T
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) =
      Sheaf.H.δ hE terminal s := by
    rw [Scheme.Pic.toCohomologicalPicardGroup_apply, Scheme.Pic.ofIsInvertible,
      Scheme.Pic.etaleTorsorClass_mk]
    exact hp
  have hs : (Sheaf.H.equiv₀ _ terminal).symm s = Ext.mk₀ (supportedIntegralUnit i) :=
    integral_section T _ (supportedIntegralUnit i)
  rw [Sheaf.H.δ_apply, hs] at hpic
  change (Ext.mk₀ (supportedIntegralUnit i)).comp
    (Classical.choose (cartierPoleBoundary_existsUnique i hI)) (zero_add 1) = _
  rw [hβ]
  exact hpic.symm

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open FiniteExactArrow
attribute [local implicit_reducible] diagonalLine

/-- The signed integral diagonal boundary forgets support to the actual divisor class.

Source: latest blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (3).
(blueprint: lem-sp-tower-class-diagonal-integral-forget).

Proof: the pole extension's fibre over supported one is the frame torsor of
the dual Cartier ideal, with its original units action. Its connecting class
is therefore the cohomological Picard class of that divisor line. The
specified diagonal boundary negates the negative roof boundary, so its
extension class is precisely this positive pole extension. Apply exact site
comparison, cancel the supported-source comparison and then apply the exact
constant-tower functor. Naturality of the single and shift comparisons gives
the displayed equality on whole systems, with no finite-evaluation argument. -/
theorem diagonalIntegral_forget (S : Scheme.{u}) :
    (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
        ((constant (diagonalSurface S)).map (supportedIntegralUnit S)) ≫
      diagonalBoundary S = lineBundleClass (diagonalSurface S) (diagonalPic S) := by
  unfold diagonalBoundary lineBundleClass
  rw [← mapSingleArrow_precompose]
  congr 1
  have h := Etale.pole_forget (diagonalImmersion S) (diagonalImmersion_cartier S)
  have hp := congrArg (fun e ↦ (e.mapExactFunctor
    (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface S))).hom) h
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp] at hp
  simp only [extensionArrow, diagonalIntegralBoundary, neg_neg, transportBoundarySource,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ← mapSingleArrow_ext]
  simp only [supportedIntegralUnit, Functor.map_comp, Category.assoc]
  have hcancel :
      (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
          (cartierIntegralSourceIso (diagonalImmersion S)).hom ≫
        (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
          (cartierIntegralSourceIso (diagonalImmersion S)).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hcancel]
  rw [← mapSingleArrow_ext] at hp
  rw [reassoc_of% hp]
  unfold lineBundleEtaleClass mapExtensionEndpoints diagonalPic diagonalLine
  erw [mapSingleArrow_ext]

end AlgebraicGeometry.ProEtale.SpTowerClasses
