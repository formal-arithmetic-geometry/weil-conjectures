/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism
public import Sheaf.AlgebraicGeometry.SpaceSetSheafOverlapArrows
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization
import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismStalkBijection
import Sheaf.AlgebraicGeometry.EtaleSetSectionsPhSheaf
import Sheaf.AlgebraicGeometry.PhSchemeSite

/-! # Proper-surjective descent of small étale sheaves of sets

Source: Stacks Project, More on Cohomology of Spaces, Tag 0DFX
(lemma-surjective-proper), with the adjunction normalization of Tags 03G2 and 03G8
(blueprint: lem-sfb-space-proper-surjection-set-sheaf-equalizer).

The overlap arrows are the published definitions of
`def-sfb-space-set-sheaf-overlap-arrows`. Their inverse comparison is the adjunction mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Proper-surjective descent is an equalizer for arbitrary sheaves of sets.
Source: Stacks, Tag 0DFX (lemma-surjective-proper)
(blueprint: lem-sfb-space-proper-surjection-set-sheaf-equalizer).

Proof, following the node's six steps:
1. Pullback on sections along any surjective space morphism is injective. Lift each
field-valued point after extension using def-trf-algebraic-space-jointly-surjective-family,
then pass to an algebraic closure (def-weil-algebraic-closure). The conservative geometric
stalks of lem-sfb-space-geometric-points-conservative detect equality. Extension of the
geometric field preserves the germ by lem-weil-pbc-geometric-point-morphism-stalk-bijection;
composition comparisons are those of lem-trf-space-enlarged-ringed-composition-localization.
2. Evaluate on affine scheme charts T of U. The chart and localization comparisons of
lem-trf-space-enlarged-chart-ringed-morphism and
lem-trf-space-enlarged-ringed-composition-localization identify the diagram with sections
over P = V ×_U T and P ×_T P. Properness and surjectivity persist by
lem-sfb-space-proper-base-change and lem-sfb-space-smooth-surjective-fppf-locality.
3. The proper space P over affine T admits a proper universally surjective scheme cover
Z → P by lem-sfb-space-weak-chow. Its composite Z → T is a proper surjection of schemes
by lem-sfb-space-proper-composition. Its double overlap maps to P ×_T P.
4. A matching section on P restricts to a matching section on Z. The ph sheaf property
lem-sfb-etale-set-sections-ph-sheaf, with the proper-surjective cover of
def-trf-ph-scheme-site, gives a unique section on T inducing the section on Z.
5. Injectivity for Z → P shows that its pullback to P is the original section.
Injectivity for P → T gives uniqueness. Conversely, a section from T matches because
the two composites from the overlap agree. This proves the equalizer on affine charts.
6. The section maps are precisely adjunction units; the composition comparisons above
are their adjunction-compatible mates. Unique local antecedents glue and commute with
restriction, giving the sheaf equalizer. They also give monicity of its unit and the
sectionwise image criterion. Empty spaces and empty section sets require no exception.
-/
theorem properSurjection_setSheaf_equalizer {V U : AlgebraicSpace S} (h : V ⟶ U)
    (hp : MapIsProper h) (hs : Function.Surjective (mapPoint h.hom.hom))
    (A : Sheaf U.etaleTopology (Type (max (u + 1) w))) :
    ∃ c :
      (smallEtaleMorphism h).adj.unit.app A ≫
          properDescentOverlapMap (enlargedFibreProductFst h h) h
            (enlargedFibreProductFst h h ≫ h) rfl A =
        (smallEtaleMorphism h).adj.unit.app A ≫
          properDescentOverlapMap (properDescentSecondProjection h) h
            (enlargedFibreProductFst h h ≫ h)
            (ObjectProperty.hom_ext _ (Limits.pullback.condition)).symm A,
      Nonempty (IsLimit (Fork.ofι ((smallEtaleMorphism h).adj.unit.app A) c)) ∧
      Mono ((smallEtaleMorphism h).adj.unit.app A) ∧
      ∀ (T : U.EtaleSite),
        Function.Injective (((smallEtaleMorphism h).adj.unit.app A).hom.app (op T)) ∧
        ∀ b : ((smallEtaleMorphism h).direct.obj
            ((smallEtaleMorphism h).inverse.obj A)).obj.obj (op T),
          (properDescentOverlapMap (enlargedFibreProductFst h h) h
              (enlargedFibreProductFst h h ≫ h) rfl A).hom.app (op T) b =
            (properDescentOverlapMap (properDescentSecondProjection h) h
              (enlargedFibreProductFst h h ≫ h)
              (ObjectProperty.hom_ext _ (Limits.pullback.condition)).symm A).hom.app (op T) b ↔
          ∃ s : A.obj.obj (op T),
            ((smallEtaleMorphism h).adj.unit.app A).hom.app (op T) s = b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
