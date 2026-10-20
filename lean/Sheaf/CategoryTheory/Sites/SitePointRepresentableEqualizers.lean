/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism

/-!
# Equalizers of the pointed sheafified representables

Source: Stacks Project, Sites, Tag 00YA, proof of (2), the paragraph establishing
condition (2) of a site point, and Tag 00WJ
(blueprint: lem-trf-site-point-representable-equalizers).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

open Limits

/-- The inverse image of a topos point carries sheafified representable equalizers
to equalizers of sets.

Source: Stacks Project, Sites, Tag 00YA, proof of (2), the displayed identity for
the sheaf associated to a representable fibre product; Tag 00WJ
(blueprint: lem-trf-site-point-representable-equalizers).

Proof: a map into the equalizer of two arrows is precisely a map whose two
composites agree, so Yoneda takes its equalizer fork to a limiting fork of
presheaves. The associated-sheaf equalizer comparison is bijective: locally
represent a section in the equalizer of the sheafified arrows, and refine until
the two images of its representative agree. It is then a section of the original
presheaf equalizer. Two such representatives coincide in that equalizer after
refinement exactly when their images in the original presheaf do. This is the
surjectivity and injectivity argument for the plus comparison. Apply plus twice
and use uniqueness of the sheafification adjunction to obtain the equalizer fork
for the supplied associated-sheaf functor. Finally apply `p.inverse`, whose
left-exactness preserves the limiting fork. Every parallel-pair diagram is
isomorphic to the diagram of its two arrows, so this gives preservation of all
limits of shape `WalkingParallelPair`. This is only the equalizer component of
condition (2); it asserts none of the other site-point reconstruction clauses. -/
theorem sitePoint_representable_preservesEqualizers
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C] [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v))) :
    PreservesLimitsOfShape WalkingParallelPair
      (yoneda ⋙ presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse) := by sorry

end CategoryTheory
