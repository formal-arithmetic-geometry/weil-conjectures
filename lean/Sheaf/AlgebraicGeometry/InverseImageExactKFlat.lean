/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Homology.KFlat

/-! # Exact inverse image and K-flat resolutions

Source: Stacks Project, Cohomology, Tags 06YI and 06YC.
(blueprint: lem-pc-inverse-image-exact-kflat-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Exact module inverse image carries K-flat resolutions to K-flat resolutions.
Source: Stacks Project, Cohomology, Tags 06YI and 06YC.

Proof: the inverse-image maps preserve identities, composition and addition because
these identities hold for the underlying abelian inverse-image functor. At each point
of T its stalk is the source stalk at the image point. Stalks detect exactness, so this
additive functor preserves finite limits and colimits, and hence quasi-isomorphisms
of complexes. Apply K-flat pullback preservation to the ringed-space morphism with
ring sheaf g⁻¹ O_S on T and identity adjoint ring map. Tensoring with that same ring
is naturally the identity, identifying this pullback complex with termwise inverse
image. It is therefore K-flat. The two conclusions give preservation of resolutions.
For the empty space the stalk criterion is vacuous and the module category is trivial;
no surjectivity or flatness hypothesis on g is required.
(blueprint: lem-pc-inverse-image-exact-kflat-resolution). -/
theorem exists_inverseImage_exact_kFlat {T S : Scheme.{u}} (g : T ⟶ S) :
    ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
  sorry

end AlgebraicGeometry
