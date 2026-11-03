/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Helper.SequentialSemilinearDerivedDiagramsDefs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearRoofData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearStrictSystemAssembly

/-! Sequential semilinear derived diagram realization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived
open Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [siteSmall : EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Compatible bounded-below derived vertex diagrams are realized by a strict system.
Proof source: paragraph 4 of the proof of `lem-coef-integral-finite-extension`
(coherent maps of towers); right fractions, Stacks Tags 05RT and 04VI.
Proof: `sequentialSemilinearRoofData` chooses, by recursive right fractions,
complexes `L n`, isomorphisms `a n : Q(L n) ≅ K n` and adjacent chain maps `b n`
representing `k n`; `sequentialSemilinearStrictSystemAssembly` assembles them into a
complex `P` of strict systems with evaluation isomorphisms `c n` compatible with the
derived transitions. Put `M = Q P` and `e n = c n ≪≫ a n`; after cancelling the
isomorphism `v_n(a n)⁻¹` followed by the restriction factorization, the two helper
equations give the square. The lower bound is not used.
(blueprint: lem-sf-sequential-semilinear-derived-realization). -/
theorem sequentialSemilinearDerivedRealization :
    ∀ (K : ∀ n : ℕ, DerivedCategory (systemLevel B n))
      (k : ∀ n : ℕ, K (n + 1) ⟶ (adjacentRestriction B n).obj (K n)),
      (∃ a : ℤ, ∀ n : ℕ, (K n).IsGE a) →
      ∃ (M : DerivedCategory (StrictRingSystem B))
        (e : ∀ n : ℕ, (derivedSystemEvaluation B n).obj M ≅ K n),
        ∀ n : ℕ, (systemDerivedTransition B (Nat.le_succ n)).app M ≫
            (adjacentRestriction B n).map (e n).hom =
          (e (n + 1)).hom ≫ k n := by
  let _ := siteSmall
  intro K k _
  obtain ⟨L, a, b, hb⟩ := sequentialSemilinearRoofData B K k
  obtain ⟨P, c, hc⟩ := sequentialSemilinearStrictSystemAssembly B L b
  refine ⟨DerivedCategory.Q.obj P, fun n ↦ c n ≪≫ a n, ?_⟩
  intro n
  apply (cancel_mono ((adjacentRestriction B n).map (a n).inv ≫
      (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app (L n))).1
  simp only [CategoryTheory.Iso.trans_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rw [Category.assoc, hc, ← hb]
  simp only [Category.assoc]

end SheafOfModules.SequentialDerived
