/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # The fixed pullback-counit composite on global derived Hom

Source: Stacks Project, cohomology.tex, Tags 079W, 08I3 and 0B6A.
-/

@[expose] public section

universe u w
open CategoryTheory Opposite TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Pull back global Hom and postcompose with the fixed derived counit.
Source: Stacks Project, cohomology.tex, Tags 08I3 and 079W
(blueprint: lem-pc-global-hom-pullback-counit-isomorphism). -/
def schemeGlobalHomPullbackCounitMap {T S : Scheme.{u}} (g : T ⟶ S)
    (M : schemeDerivedCategory S) (E : schemeDerivedCategory T) :
    (schemeGlobalDerivedHom S).obj (op M, (schemeDerivedDirectImage g).obj E) ⟶
      (schemeGlobalScalarRestriction g).obj
        ((schemeGlobalDerivedHom T).obj (op ((derivedPullback g).obj M), E)) :=
  schemeGlobalDerivedHom_pullback_comparison g M ((schemeDerivedDirectImage g).obj E) ≫
    (schemeGlobalScalarRestriction g).map
      ((schemeGlobalDerivedHom T).map
        (((𝟙 ((derivedPullback g).obj M)).op,
          (schemeHomPullbackAdjunction g).counit.app E) :
          (op ((derivedPullback g).obj M),
            (derivedPullback g).obj ((schemeDerivedDirectImage g).obj E)) ⟶
          (op ((derivedPullback g).obj M), E)))

/-- The fixed counit composite is invertible and natural in its two inputs.
Source: Stacks Project, cohomology.tex, Tags 079W, 08I3 and 0B6A
(blueprint: lem-pc-global-hom-pullback-counit-isomorphism).

Proof: write F = Lg*, R = Rg*. For any A on S, tensor-Hom adjunction and
F ⊣ R identify maps A → RHom(M,RE) with maps F(A ⊗ M) → E. The canonical
pullback-tensor isomorphism identifies these with maps FA ⊗ FM → E.
Tensor-Hom adjunction on T and F ⊣ R identify the latter with maps
A → R RHom(FM,E). Under these bijections postcomposition with the internal
counit composite is the identity: expand the evaluation mate and cancel the
unit and counit using the two triangle identities. Yoneda therefore makes
this internal composite invertible. Apply RΓ(S,-), then the canonical Leray
isomorphism RΓ(S,R(-)) ≅ restriction RΓ(T,-). Naturality of Leray moves
postcomposition by the counit past this isomorphism, giving exactly the map
defined above. The bijections, evaluation, and counit are natural in both
inputs, so the resulting components satisfy the displayed naturality square. -/
theorem schemeGlobalHomPullbackCounitMap_isIso_natural {T S : Scheme.{u}} (g : T ⟶ S) :
    (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T),
      IsIso (schemeGlobalHomPullbackCounitMap g M E)) ∧
    (∀ (P Q : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ Q),
      (((𝟭 (schemeDerivedCategory S)).op.prod (schemeDerivedDirectImage g) ⋙
        schemeGlobalDerivedHom S).map f) ≫
          schemeGlobalHomPullbackCounitMap g Q.1.unop Q.2 =
      schemeGlobalHomPullbackCounitMap g P.1.unop P.2 ≫
        (((derivedPullback g).op.prod (𝟭 (schemeDerivedCategory T)) ⋙
          schemeGlobalDerivedHom T ⋙ schemeGlobalScalarRestriction g).map f)) := by
  sorry

end AlgebraicGeometry
