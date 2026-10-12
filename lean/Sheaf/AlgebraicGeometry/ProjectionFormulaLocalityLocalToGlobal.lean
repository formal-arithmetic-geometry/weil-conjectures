module
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.SheafIsomorphismLocalOpenCover
@[expose] public section
universe u w v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- Local isomorphisms of the projection map imply its global isomorphism.
Source: Stacks Project, perfect.tex, Lemma 36.22.1 (Tag 08EU).
(blueprint: lem-pc-projection-locality-local-to-global)
The proof identifies restrictions with maps for restricted morphisms and uses
cohomology sheaf locality on an open cover. -/
theorem projectionFormula_local_to_global
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (K : schemeDerivedCategory Y)
    (I : Type v) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (φ : ((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
      (schemeDerivedDirectImage f).obj (E ⊗ ((derivedPullback f).obj K))) :
    (∀ i : I, IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)) →
      IsIso φ := by
  intro hlocal
  apply (DerivedCategory.isIso_iff _ φ).mpr
  intro n
  have hU : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    Y.toRingedSpace I U hU _ _
    ((DerivedCategory.homologyFunctor _ n).map φ)).mpr
  intro i
  have := hlocal i
  have hhom : IsIso
      ((schemeOpenRestriction Y (U i)).map
        ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction Y (U i)).mapDerivedCategoryHomologyFunctorIso n) φ).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ))
        exact Functor.map_isIso _ _)
  let G := (Scheme.Modules.overEquiv (U i)).functor
  have : IsIso (G.map (((DerivedCategory.homologyFunctor _ n).map φ).over (U i))) :=
    hhom
  exact isIso_of_reflects_iso _ G
end AlgebraicGeometry
