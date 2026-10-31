/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenExtensionProducts
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf

/-!
# Open–closed operations on pro-etale module sheaves

Source: Weil conjectures blueprint, sec-proetale-coefficients,
`sk-prop-sf-open-closed-triangle`, statement and proof; Bhatt–Scholze, §6.1;
Stacks Project, Tags 09AA, 09AH, 09BM and 09BP
(blueprint: sk-prop-sf-open-closed-triangle).

The coefficients are an arbitrary, possibly noncommutative, ring sheaf: a monoid
object in abelian sheaves. All operations and coefficient transports are the
recorded canonical functors, with their actual adjunction unit and counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.unusedVariables false in
/-- Exactness, limits, localization, and base change for open–closed module operations.
Small limits and products use the site/module size convention `u + 1`. Derived
inverse limits are sequential Roos limits in the unbounded derived category.
The base-change comparisons are characterized by their underlying composition
comparison and their adjunction transposes; the last equations identify the two
canonical sequence arrows after pullback.

Source: Weil conjectures blueprint, sec-proetale-coefficients,
`sk-prop-sf-open-closed-triangle`; Bhatt–Scholze, §6.1; Stacks, Tags 09AA,
09AH, 09BM and 09BP (blueprint: sk-prop-sf-open-closed-triangle).

Proof:
1. Apply clause (2) of det-sf-open-closed-pullback-limits to `i` and `B`.
   The quasi-compact open complement gives its compactness hypothesis. This
   proves exactness and preservation of all small limits and colimits for `i^*`.
   Its henselian evaluation formula avoids any geometric-stalk argument.
2. Apply clauses (1)–(3) of det-sf-open-closed-sequence-ring-sheaf.
   They give exactness of `j^*`, `j_!`, and `i_*`; the invertible closed counit
   gives full faithfulness. The open counit followed by the closed unit is the
   asserted short exact sequence, naturally in the module sheaf.
3. Apply clauses (2)–(3) of det-sf-open-closed-extension-zero-limits.
   They give sheaf products, derived products, and preservation of every
   sequential Roos-limit object, without boundedness or constructibility.
4. Apply clause (4) of det-sf-open-closed-sequence-ring-sheaf to every qcqs
   base change. Its canonical comparisons identify the pulled-back sequence
   maps with the new counit and unit. The inverse-image composition comparison
   is exactly that of def-sf-proetale-ring-sheaf-operations.
-/
theorem proEtale_openClosed_operations
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    PreservesFiniteLimits (ringSheafInverseImage i B) ∧
    PreservesFiniteColimits (ringSheafInverseImage i B) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (ringSheafInverseImage i B) ∧
    PreservesColimitsOfSize.{u + 1, u + 1} (ringSheafInverseImage i B) ∧
    PreservesFiniteLimits (ringSheafDirectImage i B) ∧
    PreservesFiniteColimits (ringSheafDirectImage i B) ∧
    (ringSheafDirectImage i B).Full ∧ (ringSheafDirectImage i B).Faithful ∧
    PreservesFiniteLimits (ringSheafInverseImage j B) ∧
    PreservesFiniteColimits (ringSheafInverseImage j B) ∧
    PreservesFiniteLimits (ringSheafOpenExtension j B) ∧
    PreservesFiniteColimits (ringSheafOpenExtension j B) ∧
    (∀ M, Mono ((ringSheafOpenAdjunction j B).counit.app M) ∧
      Epi ((ringSheafAdjunction i B).unit.app M) ∧
      (ComposableArrows.mk₂ ((ringSheafOpenAdjunction j B).counit.app M)
        ((ringSheafAdjunction i B).unit.app M)).Exact) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I)
      (ringSheafDerivedOpenExtension j B)) ∧
    (∀ (K : ℕ → ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B))
      (t : ∀ n : ℕ, K (n + 1) ⟶ K n) [HasProduct K]
      (L : ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B)),
      IsDerivedLimit t L →
      Exists fun [hP : HasProduct (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))] ↦
        IsDerivedLimit (K := fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))
          (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).map (t n))
          ((ringSheafDerivedOpenExtension j B).obj L)) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) (ringSheafOpenExtension j B)) ∧
    (∀ {X' : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] (g : X' ⟶ X),
      Exists fun [hu : IsMonHom (ringSheafSquareCoefficient g j B)] ↦
      Exists fun [hz : IsMonHom (ringSheafSquareCoefficient g i B)] ↦
      ∃ delta : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage j B ⋙ ringSheafSquarePullback g j B,
      ∃ gamma : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage i B ⋙ ringSheafSquarePullback g i B,
        (∀ M, (delta.hom.app M).hom = (ringSheafSquareComparison g j).hom.app M.X) ∧
        (∀ M, (gamma.hom.app M).hom = (ringSheafSquareComparison g i).hom.app M.X) ∧
        (∀ M, Mono ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          Epi ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          (ComposableArrows.mk₂
            ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M))
            ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M))).Exact) ∧
        ∃ alpha : ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g j B ⋙
              ringSheafOpenExtension (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B),
        ∃ beta : ringSheafDirectImage i B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g i B ⋙
              ringSheafDirectImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B),
          (∀ N, (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _ (alpha.inv.app N) =
            (ringSheafSquarePullback g j B).map ((ringSheafOpenAdjunction j B).unit.app N) ≫
              delta.inv.app ((ringSheafOpenExtension j B).obj N)) ∧
          (∀ G, ((ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _).symm (beta.hom.app G) =
            gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫
              (ringSheafSquarePullback g i B).map ((ringSheafAdjunction i B).counit.app G)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafOpenAdjunction j B).counit.app M) =
            alpha.hom.app ((ringSheafInverseImage j B).obj M) ≫
              (ringSheafOpenExtension (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).map (delta.inv.app M) ≫
              (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).counit.app
                  ((ringSheafInverseImage g B).obj M)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafAdjunction i B).unit.app M) ≫
              beta.hom.app ((ringSheafInverseImage i B).obj M) =
            (ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).unit.app
                  ((ringSheafInverseImage g B).obj M) ≫
              (ringSheafDirectImage (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).map (gamma.hom.app M))) := by
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hcompact : IsCompact ((Set.range i)ᶜ) := by
    rw [← hU]
    exact isCompact_range j.continuous
  obtain ⟨_, hiLim, hiColim, hiAllLim, hiAllColim⟩ :=
    Scheme.closed_inverseImage_preserves_limits i hcompact B
  obtain ⟨hjLim, hjColim, heLim, heColim, _, hdLim, hdColim, hcounit, _, hseq, hbase⟩ :=
    proEtale_openClosed_sequence_ring_sheaf i j hU B
  have : ∀ G, IsIso ((ringSheafAdjunction i B).counit.app G) := hcounit
  have : IsIso (ringSheafAdjunction i B).counit := NatIso.isIso_of_isIso_app _
  let hff := (ringSheafAdjunction i B).fullyFaithfulROfIsIsoCounit
  obtain ⟨_, hproducts, hlimits, hsheafProducts⟩ :=
    proEtale_openExtension_products_derivedLimits i j hU B
  exact ⟨hiLim, hiColim, hiAllLim, hiAllColim, hdLim, hdColim, hff.full, hff.faithful,
    hjLim, hjColim, heLim, heColim, hseq, hproducts, hlimits, hsheafProducts, hbase⟩

end AlgebraicGeometry.ProEtale
