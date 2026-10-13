/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import Sheaf.AlgebraicGeometry.GlobalDerivedHom
import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-!
# The exchange square for global Hom comparisons

Source: Stacks Project, duality.tex, Tag 0AA8, final commutative diagrams.
(blueprint: lem-sc-global-hom-base-change-exchange).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- The evaluation-mate pullback and direct-image comparisons satisfy the exchange
square, with the canonical base-change map in each Hom entry. No invertibility,
counit equation, or additional morphisms are assumed.

Source: Stacks Project, duality.tex, Tag 0AA8, final commutative diagrams;
cohomology.tex, Tag 08I3, and duality.tex, Tag 0B6I, evaluation-mate comparisons.
(blueprint: lem-sc-global-hom-base-change-exchange).

Proof: expand both comparison maps as the transposes of evaluation under the
fixed tensor-Hom bijections and pullback/direct-image adjunctions. Transpose the
two paths once more. Naturality of evaluation identifies the occurrence of
base change in the second entry with postcomposition by its evaluation mate;
in the first entry, contravariance identifies it with precomposition by the
same mate. Expand that mate as the canonical pullback-composition comparison
followed by the adjunction counit. The counit naturality square and triangle
identity make the two resulting tensor-evaluation composites equal. The pinned
pullback tensor comparisons respect composition: on K-flat representatives both
are the ordinary tensor-pullback comparison, and their derived universal
properties transport this equality to all objects. Apply derived global sections.
The Leray comparisons respect composition by uniqueness of the comparison with
the same right-derived unit; the underived global-sections/scalar comparison is
the identity on sections. Thus its two scalar paths are identified by exactly
schemeGlobalScalarSquareIso. This gives the displayed equality. -/
theorem schemeGlobalHom_baseChange_exchange
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) :
    (schemeGlobalScalarRestriction f).map
        (schemeGlobalDerivedHom_pullback_comparison (pullback.fst f g) M N) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M),
              (derivedPullback (pullback.fst f g)).obj N)) ≫
      (schemeGlobalScalarRestriction g).map
        (schemeGlobalHomDirectImageMap (pullback.snd f g)
          ((derivedPullback (pullback.fst f g)).obj M)
          ((derivedPullback (pullback.fst f g)).obj N)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M)),
            (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj N)))
          (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
            (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj N)))
          ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M).op, 𝟙 _)) =
    schemeGlobalHomDirectImageMap f M N ≫
      schemeGlobalDerivedHom_pullback_comparison g
        ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          ((𝟙 _).op, schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition N)) := by
  sorry

end AlgebraicGeometry
