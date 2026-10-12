/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.HypercohomologyLeftEdge
public import Sheaf.CategoryTheory.GrothendieckComposablePair

import Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel
import Sheaf.CategoryTheory.CartanEilenbergExists

/-! # Comparing the resolution and complex hypercohomology edges

Source: Stacks Project, derived.tex, Tags 015N and 015J.
(blueprint: lem-pc-grothendieck-hypercohomology-edge).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For F applied to an injective resolution, the Grothendieck edge is the
hypercohomology edge transported through the canonical resolution comparisons.
Source: Stacks Project, Tags 015N and 015J; steps 1 and 2 of
lem-pc-grothendieck-cocycle-comparison
(blueprint: lem-pc-grothendieck-hypercohomology-edge).

Proof:
Extend F(I) by zero and choose its Cartan--Eilenberg resolution. Package it with
the prescribed I as a CartanEilenbergPresentation and apply
 grothendieckSSDoubleComplexModel. Every term F(I^q) is G-acyclic by hFG, so
applying G to the column augmentations is a quasi-isomorphism. The model's
augmentation equation identifies the source homology comparison with
I.isoRightDerivedObj (F composed with G) inverse. Its canonical E2 comparison
identifies the left endpoint with G(R^n F(X)); the comparison
I.isoRightDerivedObj F n then identifies that endpoint with G(H^n(F(I))).
The model's left edge is the quotient by the first filtration step followed by
the stable-page inclusion. The truncation spectral object defining
cochainHypercohomologyLeftEdge computes this same edge on F(I), with the derived
unit representing the column augmentation. Its target iso uses exactly the
same truncation, shift and rightDerivedZeroIsoSelf factors. Substitute these
source and target identifications and the model's edge equation. Naturality
under a comparison from I to the chosen injective resolution ensures the
canonical comparisons coincide, so the result holds for the prescribed I.
This is an equation of maps on the whole homology object, without a supplied
cocycle or its inclusion condition; it is only the resolution-identification
part of the cocycle comparison. The zero-degree case uses the same canonical
rightDerivedZeroIsoSelf, with all shift signs equal to one.
-/
theorem grothendieckLeftEdgeMap_eq_hypercohomology
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
        (F.grothendieckLeftEdgeMap G hFG n).app X ≫
        G.map (I.isoRightDerivedObj F n).hom =
      G.cochainHypercohomologyLeftEdge
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n := by
  sorry

end CategoryTheory
