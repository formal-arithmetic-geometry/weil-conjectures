module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials

/-! # Relative differentials of an algebraic space over its scheme base

Source: Stacks Project, More on Morphisms of Spaces, Tag 04CT;
Modules on Sites, Tags 04BN and 08TP (blueprint: def-sfb-space-relative-differentials).

The construction sheafifies sectionwise differentials on the existing small affine
model, then extends along the fixed equivalence with the small etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- Relative differentials on the fixed affine basis, with the actual structural map.
Source: Stacks 04CT, 04BN and 08TP (blueprint: def-sfb-space-relative-differentials). -/
def relativeOmegaSmall (X : AlgebraicSpace S) : X.SmallModules :=
  SheafDifferentials.omega (cotangentRingMap (groupSpaceProjection X))

/-- The sheaf of relative differentials on the original small etale site.
Source: Stacks 04CT, 04BN and 08TP (blueprint: def-sfb-space-relative-differentials). -/
def relativeOmega (X : AlgebraicSpace S) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj (relativeOmegaSmall X)

/-- The universal differential of a regular function on an affine etale chart.
The counit of the fixed basis equivalence supplies its original-site section.
Source: Stacks 04CT, 04BN and 08TP (blueprint: def-sfb-space-relative-differentials). -/
def relativeOmegaSection (X : AlgebraicSpace S) (V : X.SmallEtaleModel)
    (x : X.smallStructureSheaf.obj.obj (op V)) :
    (relativeOmega X).val.obj (op (X.smallEtaleInclusion.obj V)) :=
  ((X.smallModuleEquivalence.counitIso.inv.app (relativeOmegaSmall X)).val.app (op V))
    ((SheafDifferentials.derivation (cotangentRingMap (groupSpaceProjection X))).d x)

end AlgebraicGeometry.AlgebraicSpace
