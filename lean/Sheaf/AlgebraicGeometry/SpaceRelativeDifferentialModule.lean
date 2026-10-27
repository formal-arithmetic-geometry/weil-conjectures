module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials

/-! # Relative differentials on algebraic spaces

Source: Stacks Project, Properties of Spaces, differentials; More on Morphisms of Spaces,
Tags 0618, 0619 and 05ZF (blueprint: def-sfb-space-relative-differential-module).

The structural ring map is the existing chart-normalized inverse-image map. The module
is the sheafification of Mathlib's differential presheaf, in the original module universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Relative differentials on the small étale ringed site: sheafify the differentials
of the actual inverse-image structural ring map. Source: Stacks, Tags 0618 and 05ZF
(blueprint: def-sfb-space-relative-differential-module). -/
def relativeDifferentialModule (f : X ⟶ Y) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj
    (CategoryTheory.SheafDifferentials.omega (cotangentRingMap f))

/-- The universal differential on an affine basis chart, transported by the counit
of the specified affine-basis equivalence. Source: Stacks, Tag 0619
(blueprint: def-sfb-space-relative-differential-module). -/
def relativeDifferentialSection (f : X ⟶ Y) (U : X.SmallEtaleModel)
    (s : X.smallStructureSheaf.obj.obj (op U)) :
    (relativeDifferentialModule f).val.obj (op (X.smallEtaleInclusion.obj U)) :=
  ((X.smallModuleEquivalence.counitIso.app
    (CategoryTheory.SheafDifferentials.omega (cotangentRingMap f))).inv.val.app (op U))
      ((CategoryTheory.SheafDifferentials.derivation (cotangentRingMap f)).d s)

end AlgebraicGeometry.AlgebraicSpace
