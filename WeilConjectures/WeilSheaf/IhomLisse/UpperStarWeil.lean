/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.IhomLisse.UpperStar

/-!
# Pullback of the internal hom out of a lisse pro-étale Weil sheaf

The comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]` is a morphism of pro-étale Weil sheaves, an
isomorphism for `A` lisse.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]` is compatible with the Weil structures. -/
lemma upperStarIhomComparison_comm (A B : ProEtaleWeilSheaf k₀ l Y) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier) ≫
      ((ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A)).obj ((upperStar k₀ l φ).obj B)).obj.str =
    ((upperStar k₀ l φ).obj ((ihomFunctor k₀ l Y A).obj B)).obj.str ≫
      adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier :=
  adicUpperStarIhomComparison_str
    (c := (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm) A.str B.str

/-- **Pullback commutes with the internal hom out of a lisse pro-étale Weil sheaf**:
`φ^* [A, -] ≅ [φ^* A, φ^* -]`. -/
noncomputable def ihomFunctorCompUpperStarIso (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : IsAdicLisseSheaf A.carrier) :
    ihomFunctor k₀ l Y A ⋙ upperStar k₀ l φ ≅
      upperStar k₀ l φ ⋙ ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) :=
  NatIso.ofComponents (fun B ↦
    have := hA.isIso_adicUpperStarIhomComparison
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) B.carrier
    IsoAlgebra.isoMk (asIso (adicUpperStarIhomComparison l
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
      A.carrier B.carrier)) (upperStarIhomComparison_comm φ A B))
    fun f ↦ IsoAlgebra.hom_ext (adicUpperStarIhomComparison_naturality _ _ f.hom.f)

end AlgebraicGeometry.ProEtaleWeilSheaf
