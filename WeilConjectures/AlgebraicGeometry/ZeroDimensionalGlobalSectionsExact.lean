/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyIso
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Global sections of abelian étale sheaves on a zero-dimensional finite-type scheme
 over an algebraically closed field preserve finite colimits. -/
theorem zero_dimensional_global_sections_preservesFiniteColimits
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) :
    PreservesFiniteColimits (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have : Finite C := finite_of_compact_of_discrete
  let s (x : C) := pointOfClosedPoint f x (isClosed_discrete {x})
  let T (x : C) := (Scheme.pointSmallEtale (s x)).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let G := Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}
  let c (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    F.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C ↦
      (Scheme.pointSmallEtale (s x)).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
        (Over.homMk (s x) (Category.comp_id _)) F.obj)
  have hc (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) : IsIso (c F) := by
    have h := zero_dimensional_etale_cohomology_iso k C f hdim F (fun _ ↦ k) s
      (fun x ↦ pointOfClosedPoint_apply f x (isClosed_discrete {x}) _)
    let a := (Functor.homologyRightDerivedFunctorObjSingleFunctorIso G F 0).hom
    let b := (Functor.rightDerivedZeroIsoSelf G).hom.app F
    have : IsIso (a ≫ b ≫ c F) := by simpa only [a, b, c, Category.assoc] using h
    have : IsIso (b ≫ c F) := IsIso.of_isIso_comp_left a (b ≫ c F)
    exact IsIso.of_isIso_comp_left b (c F)
  let e : G ≅ ∏ᶜ T := NatIso.ofComponents
    (fun F ↦ asIso (c F ≫ (piObjIso T F).inv)) (by
      intro F F' φ
      dsimp
      rw [piObj_map]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply (cancel_mono (piObjIso T F').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro x
      dsimp [G, T, GrothendieckTopology.Point.sheafFiber]
      simp only [c, Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
      rw [← Category.assoc, Sheaf.ΓRes_naturality, Category.assoc]
      exact congrArg (fun z ↦ F.ΓRes _ ≫ z)
        ((Scheme.pointSmallEtale (s x)).toPresheafFiber_naturality φ.hom
          (Scheme.Etale.mk (𝟙 C)) (Over.homMk (s x) (Category.comp_id _))).symm)
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : G.PreservesEpimorphisms := ⟨by
    intro F F' φ hφ
    rw [← NatIso.naturality_2 e φ]
    have := epi_piObj_map T φ
    infer_instance⟩
  have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  exact Functor.preservesFiniteColimits_of_preservesHomology G

end AlgebraicGeometry
