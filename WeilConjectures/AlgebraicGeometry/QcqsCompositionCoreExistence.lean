/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionDefs

/-! # Existence of normalized qcqs compactification comparison data

Source: Stacks Tag 0F7J and latest blueprint lem-zl-shriek-composition.proof
(blueprint: new-z6-qcqs-composition-core-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]
/-- The qcqs compactification and normalized proper/open data exist before shift transport.
Source: Stacks Tag 0F7J, lemma-shriek-composition; latest blueprint
lem-zl-shriek-composition.proof (blueprint: new-z6-qcqs-composition-core-existence).

Proof:
1. Base change h₀ and g₀ to the geometric field. The sources and targets stay finite type and
   quasi-separated. The boundedness theorem gives compactifications and preservation of Dbc.
   Choose a compactification (i,q) of g. The compatible-triangle theorem gives a proper p and
   an open a from X. Pulling back along i gives an open b, a proper r and an open j, with
   b j = a, r j = h and p b = i r. The tower compactifications of h and gh are (j,r) and
   (a,qp). All opens are quasi-compact.
2. Whisker the pasting Gamma for p b = i r by Rq_* and j_!, then compose with the canonical
   proper and open compositors. Its open transpose is inverse restriction. Hence the uniqueness
   in condensed-proper-open-interchange identifies Gamma with the normalized interchange, which
   is invertible on Dctf = Dbc. This is the tower compositor required by TowerNormalized.
3. For a proper refinement v : d → c, Gamma for v j_d = j_c followed by the proper compositor
   gives rho_v, the prescribed CompactificationReindexing.refinement. Identity and pasting give
   the cocycle. Common refinements define comparison(c,d) and prove its independence. On a
   compatible tower, properOpen_tower_refinement relates the compositor expressions through
   these comparisons. So the compositor extends to every triple (c,d,e) and satisfies
   `independent`.
4. For each of h, g and gh, pull a compactification back along the target automorphism.
   Compose the proper exchange, the open exchange, the exact-to-total pullback identifications
   and the step 3 comparison. This gives exchangeComponent, and it is invertible by the
   isomorphism-square and open-exchange theorems, which gives an Exchange.
5. Pull the step 1 tower back by the automorphism (compatible-tower theorem). The triangle
   identities cancel the ambient units and counits, and open-exchange pasting cancels the open
   factors. The remaining square is the mixed cube of condensed-open-proper-pasting, which
   whiskered gives comp_exchange. These data together form Comparisons. -/
theorem qcqsCompositionCoreExists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated] :
    Nonempty (Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
