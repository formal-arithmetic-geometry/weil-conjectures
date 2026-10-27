/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ProperCurveModuli

/-! # Separated morphisms of algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Definition `definition-separated`, Tag 04YW;
spaces-morphisms.tex, Definition `definition-proper`
(blueprint: def-sfb-stack-separated-morphism).

The relative diagonal is tested on every scheme, retaining its actual algebraic-space
projection. Properness uses separatedness, quasi-compactness, local finite type and universal
closedness. The algebraic-space fibre is allowed to be a nonschematic algebraic space.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- Separated means proper relative diagonal. Each scheme test is presented by an
algebraic space with its actual projection, which is separated, quasi-compact, locally of
finite type on étale scheme charts, and universally closed. Universal closedness over a
scheme is tested after all scheme base changes, as in the recorded space convention.
Source: Stacks Project, stacks-morphisms.tex, Tag 04YW, Definition `definition-separated`;
spaces-morphisms.tex, Definition `definition-proper`
(blueprint: def-sfb-stack-separated-morphism). -/
def IsSeparatedAlgebraicModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct f f)),
    ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p ∧
        MapToSchemeIsSeparated Z T p ∧ MapIsQuasiCompact p ∧
        MapToSchemeIsLocally (@LocallyOfFiniteType) Z T p ∧
        MapToSchemeIsUniversallyClosed Z T p

end CategoryTheory
