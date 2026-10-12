module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Locality of the projection-formula isomorphism

Source: literature/stacks-project/cohomology.tex, Equation 20.54.2.1,
and perfect.tex, Lemma 36.22.1 (Tag 08EU)
(blueprint: lem-pc-projection-locality).

The map `φ` below is the canonical projection-formula map for `f`, `E`, and
`K`; the statement records that its being an isomorphism is local on an open
cover of the target. -/

@[expose] public section

universe u w v

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

set_option autoImplicit false

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Isomorphy of the projection-formula map can be checked on an open cover.
Source: literature/stacks-project/cohomology.tex, Equation 20.54.2.1, and
perfect.tex, Lemma 36.22.1 (Tag 08EU)
(blueprint: lem-pc-projection-locality).
Proof: identify the restriction of the canonical map with the canonical map
for the restricted morphism using restriction compatibility of derived pullback,
derived tensor, and derived direct image.  A morphism in a derived category is
an isomorphism exactly when all cohomology sheaf maps are isomorphisms; those
are detected on an open cover because restriction is exact and kernels and
cokernels are sheaves. -/
theorem projectionFormula_isIso_iff_openCover
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (K : schemeDerivedCategory Y)
    (I : Type v) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (φ : ((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
      (schemeDerivedDirectImage f).obj
        (E ⊗ ((derivedPullback f).obj K))) :
    IsIso φ ↔ ∀ i : I,
      IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ) := by
  sorry

end AlgebraicGeometry
