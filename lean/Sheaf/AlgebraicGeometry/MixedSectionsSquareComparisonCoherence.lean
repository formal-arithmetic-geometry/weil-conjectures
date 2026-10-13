/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Coherence of mixed sections comparisons
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-square-comparison-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Normalized Leray comparisons commute with the conjugate of the fixed pullback
composition comparison. No pullback unit or base-change map occurs in this statement.
Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY, with the normalized
sections comparison of Tag 0D5W.
(blueprint: lem-sc-mixed-sections-square-comparison-coherence).

Proof: Choose a K-injective representative J of F. Transpose the fixed left-derived
pullback composition comparisons under the pinned derived adjunctions. Their
left-derived counit equations and the Hom-equivalence equation of
exists_schemeDerivedAdjunction identify their conjugate delta with the right-derived
comparison induced by the identity underived pushforward square. Its normalization
is the pasted right-derived-unit equation of Tag 0D5T. Precompose the displayed
identity at Qh(J) with the pasted right-derived unit for the path p_*; f_*; Gamma_Y.
Direct image of a K-injective complex is acyclic for further direct image and global
sections, so this pasted unit is invertible. Substitute the characterizing equations
of exists_mixedGlobalSectionsDirectImageIso for f, p, f-prime, and g. Naturality
moves the units past the underived composition comparisons, and exact scalar
restriction moves its unit through localization. Both composites now localize the
same map on underived sections: all four Leray comparisons are identity on elements,
and pullback.condition identifies their scalar actions. The remaining scalar
comparison is precisely schemeGlobalScalarSquareIso, built from restriction along
composites. Cancel the invertible pasted unit. Every derived object is isomorphic
to Qh of a K-injective complex; naturality transports the equality to F. The sheaf
and module localizations are used separately, so no equality of w and wA is needed.
For F=0 the two morphisms are zero; identity squares give the composition unit law.
Empty schemes and nonflat g require no change, as neither units of pullback nor
invertibility of base change are asserted. -/
theorem mixedSections_square_comparison_coherence
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : schemeDerivedCategory (pullback f g)) :
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ schemeHomPullbackAdjunction h
    let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h)
        (pullback.condition (f := f) (g := g)).symm) ≪≫
          (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    (schemeDerivedGlobalSections Y).map (δ.app F) ≫
        (mixedGlobalSectionsDirectImageIso g).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso (pullback.snd f g)).hom.app F) =
      (mixedGlobalSectionsDirectImageIso f).hom.app
          ((schemeDerivedDirectImage (pullback.fst f g)).obj F) ≫
        (schemeGlobalScalarRestriction f).map
          ((mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app F) ≫
        (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition).hom.app ((schemeDerivedGlobalSections (pullback f g)).obj F)
    := by sorry

end AlgebraicGeometry
