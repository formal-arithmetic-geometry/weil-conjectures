/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-! # Scheme tests of relative ampleness for an algebraic-space line module

Source: Stacks Project, spaces-divisors.tex, Tags 0D31 and 0D32
(blueprint: def-sfb-space-relative-ample-test).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical map of a scheme over T to the identity T-scheme.
Source: Stacks, Tag 0D3D, notation for scheme tests
(blueprint: def-sfb-space-relative-ample-test). -/
def ampleLocusBaseMap {T : Scheme.{u}} (B : Over T) :
    schemeSpace B ⟶ schemeSpace (Over.mk (𝟙 T)) :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk B.hom (Category.comp_id B.hom))⟩

/-- The structure map from a scheme chart of the actual base-changed space to B.
Source: Stacks, Tag 0D3D, fibre-product projections
(blueprint: def-sfb-space-relative-ample-test). -/
def ampleLocusChartMap {T : Scheme.{u}} {X : AlgebraicSpace T}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (B : Over T)
    (U : (enlargedFibreProduct f (ampleLocusBaseMap B)).EtaleSite) : U.obj.left ⟶ B :=
  yoneda.preimage (U.obj.hom ≫ (Limits.pullback.snd f.hom (ampleLocusBaseMap B).hom).hom)

/-- Relative ampleness on the specified scheme base change. The isomorphism condition
on the chart says that the whole fibre product is a scheme, not merely that it has
an étale atlas. The ordinary module is the Zariski restriction of the canonical
ringed-étale tensor pullback of the given module, and is tested over every affine open.
Source: Stacks, Tags 0D31 and 0D32
(blueprint: def-sfb-space-relative-ample-test). -/
def IsAmpleSchemeBaseChange {T : Scheme.{u}} {X : AlgebraicSpace T}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (L : X.Modules) (B : Over T) : Prop :=
  ∃ U : (enlargedFibreProduct f (ampleLocusBaseMap B)).EtaleSite,
    IsIso U.obj.hom ∧
      ∀ W : B.left.Opens, IsAffineOpen W →
        ∃ h : ((Scheme.Modules.tensorPullback ((ampleLocusChartMap f B U).left ⁻¹ᵁ W).ι).obj
          ((schemeRestriction _ U).obj
            ((moduleTensorPullback (enlargedFibreProductFst f (ampleLocusBaseMap B))).obj
              L))).IsInvertible,
          @Scheme.Modules.IsAmple ((ampleLocusChartMap f B U).left ⁻¹ᵁ W).toScheme
            ((Scheme.Modules.tensorPullback ((ampleLocusChartMap f B U).left ⁻¹ᵁ W).ι).obj
              ((schemeRestriction _ U).obj
                ((moduleTensorPullback (enlargedFibreProductFst f (ampleLocusBaseMap B))).obj
                  L))) h

end AlgebraicGeometry.AlgebraicSpace
