/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.AdicCyclicDecomposition
public import WeilConjectures.WeilSheaf.ConstantFieldEquivalence
public import WeilConjectures.WeilSheaf.GeometricFiberPullbackStr

/-!
# Pulled-back Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme, with projections `p₀ : V̄₀ ⟶ V` and `p' : V̄' ⟶ V` of its geometric fibres over `k₀`
and over `k'`. The equivalence `ProEtaleWeilSheaf.constantFieldFunctor` between pro-étale Weil
sheaves relative to `k₀` and relative to `k'` takes the pullback `p₀^* H` of an `ℓ`-adic sheaf `H`
on `V`, with its canonical Weil structure, to `p'^* H` with its canonical Weil structure
(`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackIso`): the
pieces `jᵢ^* p₀^* H` are all identified with `(jᵢ ≫ p₀)^* H = p'^* H`, compatibly with the Weil
structures by the associativity of the factorisation isomorphisms of pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale



namespace ProEtaleWeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  (l : ℕ) [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- The pieces `jᵢ : V̄' ⟶ V̄₀` lie over `V`. -/
lemma pieceMap_comp_geometricFiberProj (i : Fin (m + 1)) :
    pieceMap hc i ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      (V ↘ Spec (CommRingCat.of k')).geometricFiberProj := by
  rw [pieceMap, Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  exact Scheme.Hom.geometricFiberComponentMap_comp_geometricFiberProj _ _ hc

/-- The constant field equivalence is the first piece of a cyclic decomposition by pullbacks. -/
lemma constantFieldFunctor_eq : constantFieldFunctor l hc hm =
    (adicCyclicDecomposition (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
      (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius (pieceMap hc)
      (pieceMap_comp_frobenius hc) (pieceMap_last_comp_frobenius hc hm)
      (cyclicDecomposition l hc hm).fullyFaithful (cyclicDecomposition l hc hm).essSurj).functor :=
  rfl

/-- **The constant field equivalence takes `p₀^* H` to `p'^* H`**, with their canonical Weil
structures. -/
def constantFieldFunctorObjGeometricFiberPullbackIso (H : AdicSheaf l V) :
    (constantFieldFunctor l hc hm).obj ((geometricFiberPullback k₀ l V).obj H) ≅
      (geometricFiberPullback k' l V).obj H :=
  eqToIso (by rw [constantFieldFunctor_eq, geometricFiberPullback_eq_functorOfNatIso]) ≪≫
    adicCyclicDecompositionFunctorObjPullbackIso _ _ (pieceMap hc) (pieceMap_comp_frobenius hc)
    (pieceMap_last_comp_frobenius hc hm) (cyclicDecomposition l hc hm).fullyFaithful
    (cyclicDecomposition l hc hm).essSurj _ _
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
    (pieceMap_comp_geometricFiberProj hc) H ≪≫
    eqToIso (geometricFiberPullback_obj_eq_mk k' l V H).symm

end ProEtaleWeilSheaf

end AlgebraicGeometry
