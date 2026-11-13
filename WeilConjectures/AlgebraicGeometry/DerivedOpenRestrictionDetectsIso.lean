/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

/-! # Open restrictions jointly detect derived isomorphisms

Source: Stacks Project, Tag 0AAB, the locality step of its proof.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- An ambient derived morphism is invertible if it is invertible on an open neighbourhood of
every point. No quasi-coherence or boundedness assumption is needed (Stacks, Tag 0AAB). -/
theorem schemeDerived_isIso_of_openRestriction
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X : Scheme.{u}} {A B : schemeDerivedCategory X} (φ : A ⟶ B)
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map φ)) :
    IsIso φ := by
  let I := {U : X.Opens // IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map φ)}
  let U : I → X.Opens := Subtype.val
  have hcover : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨V, hx, hV⟩ := hlocal x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  apply (DerivedCategory.isIso_iff _ φ).mpr
  intro n
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    X.toRingedSpace I U hcover _ _ ((DerivedCategory.homologyFunctor _ n).map φ)).mpr
  intro i
  have := i.property
  have hhom : IsIso ((schemeOpenRestriction X (U i)).map
      ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction X (U i)).mapDerivedCategoryHomologyFunctorIso n) φ).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction X (U i)).mapDerivedCategory.map φ))
        infer_instance)
  have : IsIso ((Scheme.Modules.overEquiv (U i)).functor.map
      (((DerivedCategory.homologyFunctor _ n).map φ).over (U i))) := hhom
  exact isIso_of_reflects_iso _ (Scheme.Modules.overEquiv (U i)).functor

end AlgebraicGeometry
