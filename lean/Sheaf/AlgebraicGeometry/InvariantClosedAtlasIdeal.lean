/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Scheme-theoretically invariant closed subschemes of an atlas

Source: Stacks Project, stacks-properties.tex, Tags 0507 and 04YN
(blueprint: def-sfb-invariant-closed-atlas-ideal).

An arrow of the self-relation on a test scheme is two maps to the atlas and an
isomorphism of their images. Equality of pulled-back ideals on all such tests
means equality as closed subspaces of the relation, including nilpotent structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Invariance of a closed subscheme under every scheme-valued arrow of the self-relation.
The natural isomorphism is over the test scheme, and the equality is of actual ideals,
using the scheme-theoretic inverse image `IdealSheafData.comap`.
Source: Stacks Project, Tag 0507 and Tag 04YN
(blueprint: def-sfb-invariant-closed-atlas-ideal). -/
def IsInvariantClosedAtlasIdeal {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {U : Over S}
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) F) (I : U.left.IdealSheafData) : Prop :=
  ∀ (T : Over S) (a b : T ⟶ U),
    Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map a)).comp p)
      ((discreteModuliMap (yoneda.map b)).comp p)) → I.comap a.left = I.comap b.left

/-- The closed subscheme of the atlas defined by an ideal, as a scheme over the base.
Source: Stacks Project, Tag 0507; Schemes, closed subschemes
(blueprint: def-sfb-invariant-closed-atlas-ideal). -/
def closedAtlasScheme {S : Scheme.{u}} (U : Over S) (I : U.left.IdealSheafData) : Over S :=
  Over.mk (I.subschemeι ≫ U.hom)

/-- The specified closed immersion of the ideal's subscheme into the atlas.
Source: Stacks Project, Tag 0507; Schemes, closed subschemes
(blueprint: def-sfb-invariant-closed-atlas-ideal). -/
def closedAtlasSchemeι {S : Scheme.{u}} (U : Over S) (I : U.left.IdealSheafData) :
    closedAtlasScheme U I ⟶ U :=
  Over.homMk I.subschemeι

end CategoryTheory
