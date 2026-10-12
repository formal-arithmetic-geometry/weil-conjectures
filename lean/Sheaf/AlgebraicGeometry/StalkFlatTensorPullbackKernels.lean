/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Algebra.Homology.KFlatPullback
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import Sheaf.Algebra.Homology.InverseImageStalkScalarTransport
import Sheaf.Algebra.Homology.ModuleStalkExact

/-! # Kernels of tensor pullback along stalkwise flat morphisms
Source: Stacks Project, Modules, Tag 02N4.
(blueprint: lem-sc-stalk-flat-tensor-pullback-kernels)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RingedSpace

/-- Tensor pullback along a stalkwise flat morphism preserves kernels.
Source: Stacks Project, Modules, Tag 02N4, proof by stalks.
(blueprint: lem-sc-stalk-flat-tensor-pullback-kernels)

Proof: stalks preserve kernels. At x the inverse-image stalk comparison and the
change-of-rings tensor stalk comparison identify P(M)_x with extension of scalars
of M_(g(x)) along g's stalk map. The adjoint ring-map formula identifies that scalar
map with g.hom.stalkMap x. The prescribed map formula makes these comparisons
natural in M. Flat extension of scalars preserves kernels, so P(kernel a)_x,
with the stalk of P(kernel.ι a), is the kernel of (P.map a)_x. Thus the canonical
comparison P(kernel a) → kernel(P.map a) is an isomorphism on every stalk.
Stalks detect isomorphisms of module sheaves, so the comparison is an isomorphism
of sheaves. This is precisely preservation of the limit of parallelPair a 0;
additivity ensures P.map 0 = 0. No quasi-coherence assumption is used. -/
theorem stalkFlat_tensorModulePullback_preservesKernels
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (hg : ∀ x : X, (g.hom.stalkMap x).hom.Flat)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤
      SheafOfModules.{u} (moduleRings X))
    (h : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap
        g.hom.base X.sheaf
        Y.sheaf ⟨g.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule g.hom.base
        Y.sheaf M))
    (hm : ∀ {M N} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap
          g.hom.base X.sheaf
          Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base
          Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base
          Y.sheaf M a) ≫ eqToHom (h N).symm)
    [P.Additive] :
    ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      PreservesLimit (parallelPair a 0) P := by sorry

end AlgebraicGeometry.RingedSpace
