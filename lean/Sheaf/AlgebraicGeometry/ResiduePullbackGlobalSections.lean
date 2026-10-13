/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Global sections of residue-point tensor pullback

Source: Stacks Project, Sheaves, Tag 0098.
(blueprint: lem-sc-residue-pullback-global-sections).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Residue-point pullback, evaluated globally with its residue-field scalars,
is naturally extension of scalars of the original stalk.
Source: Stacks Project, Sheaves, Tag 0098.
(blueprint: lem-sc-residue-pullback-global-sections).

Proof: Let y be the unique point of Spec kappa(x). Every neighborhood of y is
the whole space, so the germ map identifies global sections of a module sheaf
with its stalk. The same statement for the structure sheaf identifies the ring
stalk with kappa(x), with the global scalar identification GammaSpecIso. Apply
the natural tensor-pullback stalk isomorphism of Tag 0098 at y. The residue-point
morphism sends y to x, and its stalk map, followed by the identification of the
stalk ring with kappa(x), is the residue homomorphism O_X,x -> kappa(x).
Thus the composite sends a pure tensor a tensor m to a times the germ of m
restricted to the residue point, and its inverse is the inverse stalk tensor
map followed by the inverse germ map. The balanced relations give linearity;
the inverse identities follow from those of these two isomorphisms. Naturality
of germs and of the tensor-pullback stalk identification gives naturality of the
composite for every morphism of module sheaves. Empty opens have zero sections,
so they impose no additional conditions. This includes zero sheaves and arbitrary
modules, and requires no quasi-coherence or flatness. -/
theorem nonempty_residuePullback_globalSections_iso (X : Scheme.{u}) (x : X) :
    Nonempty
      (Modules.tensorPullback (X.fromSpecResidueField x) ⋙
          (SheafOfModules.evaluation
            (moduleRings (Spec (X.residueField x)).toRingedSpace) (op ⊤) ⋙
              ModuleCat.restrictScalars (ΓSpecIso (X.residueField x)).inv.hom) ≅
        RingedSpace.moduleStalkFunctor X.toRingedSpace x ⋙
          ModuleCat.extendScalars (IsLocalRing.residue (X.presheaf.stalk x))) := by sorry

end AlgebraicGeometry.Scheme
