/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties

/-! # Quasi-compact and quasi-separated morphisms of algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 050U and 04YW(4);
stacks-properties.tex, Tag 04YC(3); spaces-morphisms.tex, Tags 03HE and 03HL(3)
(blueprint: def-sfb-stack-qcqs-morphism).

Quasi-compactness of a fibred groupoid means existence of a smooth surjective atlas
by a quasi-compact scheme. Algebraic spaces use their existing discrete groupoids.
For algebraic-space morphisms we reuse `AlgebraicSpace.MapIsQuasiCompact`: its affine
scheme tests are equivalent to testing all quasi-compact algebraic spaces (03HE).
Relative diagonals use the existing canonical functor `moduliRelativeDiagonal`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact fppf sheaf has a representable surjective étale atlas from a
quasi-compact scheme. This also applies to sheaf fibre products before bundling them.
Source: Stacks, Properties of Spaces, Tag 03E3; Morphisms of Spaces, Tag 03HE
(blueprint: def-sfb-stack-qcqs-morphism). -/
def IsQuasiCompact {S : Scheme.{u}}
    (A : Sheaf (Scheme.fppfTopology.over S) (Type u)) : Prop :=
  ∃ (U : Over S) (a : yoneda.obj U ⟶ A.obj),
    CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a

/-- A map of algebraic spaces is quasi-separated when its relative diagonal is
quasi-compact. The existing quasi-compactness predicate uses affine scheme tests,
which agree with tests by all quasi-compact algebraic spaces.
Source: Stacks, Morphisms of Spaces, Tags 03HE and 03HL(3)
(blueprint: def-sfb-stack-qcqs-morphism). -/
def MapIsQuasiSeparated {S : Scheme.{u}} {A B : (Over S)ᵒᵖ ⥤ Type u}
    (g : A ⟶ B) : Prop :=
  MapIsQuasiCompact (pullback.diagonal g)

end AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- Quasi-compactness of a fibred groupoid, by existence of a smooth surjective
quasi-compact scheme atlas. No atlas is chosen, and the predicate applies to the
existing 2-fibre products as well as to discrete algebraic spaces.
Source: Stacks, Properties of Stacks, Tag 04YC(3)
(blueprint: def-sfb-stack-qcqs-morphism). -/
def IsQuasiCompactModuli {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    CompactSpace U.left ∧ IsSmoothModuliAtlas F U a

/-- A morphism of algebraic stacks is quasi-compact when every base change by a
quasi-compact algebraic stack is quasi-compact. The test universe includes the base
site and both endpoint universes, and may be enlarged by `v₃` and `w₃`.
Source: Stacks, Morphisms of Stacks, Tag 050U
(blueprint: def-sfb-stack-qcqs-morphism). -/
def IsQuasiCompactAlgebraicModuliMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (Z : BasedCategory.{max u v₁ v₂ v₃, max (u + 1) w₁ w₂ w₃} (Over S))
      (g : BasedFunctor Z G),
    IsAlgebraicModuliStack Z → IsQuasiCompactModuli Z →
      IsQuasiCompactModuli (moduliTwoFiberProduct f g)

/-- A morphism of algebraic stacks is quasi-separated if its canonical relative
 diagonal is representable by algebraic spaces and every scheme base change has a
quasi-compact, quasi-separated algebraic-space projection. Representability is part
of this predicate: the equivalence over the test scheme is `HasSpaceBaseChange`.
The target may be a discrete algebraic space; no DM or finite-type condition is used.
Source: Stacks, Morphisms of Stacks, Tag 04YW(4)
(blueprint: def-sfb-stack-qcqs-morphism). -/
def IsQuasiSeparatedAlgebraicModuliMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct f f)),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p ∧
        AlgebraicGeometry.AlgebraicSpace.MapIsQuasiCompact p ∧
        AlgebraicGeometry.AlgebraicSpace.MapIsQuasiSeparated p

end CategoryTheory
