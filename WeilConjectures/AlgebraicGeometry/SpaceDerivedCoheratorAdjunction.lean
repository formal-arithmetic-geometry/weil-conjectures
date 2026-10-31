/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceCompactPerfectGenerator
import WeilConjectures.CategoryTheory.CompactlyGenerated
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The triangulated derived quasi-coherator of an algebraic space

Source: Stacks Project, Derived Categories of Spaces, Tag 0CR4;
Derived Categories, Tag 0A8D; Categories, Tag 07RB
(blueprint: lem-sfb-space-derived-coherator-adjunction).

The ambient category and D_QCoh use the existing equivalent small ringed model.
The quasi-compactness hypotheses are the stated scheme-atlas and affine-etale-overlap
conditions, without restrictions on the base scheme or on cohomological bounds.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of D_QCoh has a triangulated right adjoint, with its counit Hom
bijections and invertible unit. Its shift structure is the one canonically induced
by the adjunction from the inherited shifts of the full inclusion.
Source: Stacks Project, Tag 0CR4, lemma-better-coherator, second proof;
Tag 0A8D, lemma-adjoint-is-exact; Tag 07RB, lemma-adjoint-fully-faithful
(blueprint: lem-sfb-space-derived-coherator-adjunction).

Proof:
1. On the specified small ringed model, module sheaves are Grothendieck abelian
   by lem-pur-ringed-site-grothendieck-abelian. Transport through the restriction
   equivalence gives the same module topos. The termwise coproduct theorem
   lem-kun-grothendieck-derived-coproducts supplies ambient derived coproducts.
2. The quasi-compact atlas makes the point space quasi-compact, by the final
   clause of lem-a1-space-finite-affine-subatlas. The affine etale overlap test
   gives absolute quasi-separatedness by lem-sfb-etale-affine-pairs-test-quasiseparated,
   applied after viewing X over Spec Z. Representability identifies each overlap
   with the scheme in hqs. By lem-sfb-space-perfect-localizing-generation, D_QCoh
   is closed under shifts, cones and ambient coproducts. It inherits its triangles,
   and its full inclusion is exact and preserves coproducts. By
   lem-sfb-space-compact-perfect-generator there is a compact perfect generator;
   detection by Hom(P[n], E) is detection by Hom(P, E[-n]), so this is compact
   generation in the sense of def-pc-compactly-generated.
3. Apply lem-pc-brown-representability-right-adjoint to this exact inclusion to
   obtain DQ and its adjunction, using only quasi-compactness and quasi-separatedness.
4. Clause (iii) of lem-weil-pbc-adjunction-shift-compatibility-unique gives the
   canonical coherent shifts on DQ, compatible with the unit and counit. Then
   lem-sf-triangulated-right-adjoint makes DQ triangulated with these same shifts.
5. The inverse adjunction equivalence sends a to I(a) followed by the counit.
   Its inverse sends b to the unit followed by DQ(b). Naturality and the triangle
   identities give the claimed natural bijections. The full inclusion is fully
   faithful, so lem-sp-adjunction-unit-fully-faithful-left makes the unit invertible.
   Empty spaces and unbounded complexes require no changes to this argument. -/
theorem exists_derivedCoheratorAdjunction
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : ∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj),
      IsAffine U.left → IsAffine V.left → IsEtale a → IsEtale b →
        ∃ W : Over S, Nonempty (yoneda.obj W ≅ Limits.pullback a b) ∧
          CompactSpace W.left) :
    ∃ (DQ : X.DerivedModules ⥤ X.DerivedQCoh) (adj : X.derivedQCohProperty.ι ⊣ DQ),
      @Functor.IsTriangulated _ _ _ _ _ _ DQ (adj.rightAdjointCommShift ℤ)
        _ _ _ _ _ _ _ _ ∧
      (∀ (P : X.DerivedQCoh) (E : X.DerivedModules),
        Function.Bijective (fun a : P ⟶ DQ.obj E ↦
          X.derivedQCohProperty.ι.map a ≫ adj.counit.app E)) ∧
      IsIso adj.unit := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
