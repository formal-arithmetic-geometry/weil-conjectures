/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescentRepresentation

/-!
# The Weil fundamental representation of a sheaf pulled back from the model

Let `p : X ⟶ X₀` be the projection of the geometric fibre of a scheme over a finite field `K`,
`Fr` its geometric Galois Frobenius (`Fr ≫ p = p`), `B = (t, β)` base point data, and `M`, `M₀`
monodromies of lisse sheaves on `X` and `X₀` compatible with `p`. For a lisse sheaf `H` on `X₀`,
the Weil sheaf `p^* H` with its canonical Weil structure `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`
(`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`) has Weil fundamental representation the
restriction of the monodromy representation of `π₁(X₀, t ≫ p)` on `H_{t ≫ p} = (p^* H)_t` along
`arithHom : π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ p)`
(`AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_of_iso_upperStar`): on loops this is the
compatibility of the monodromies, and on the Frobenius lift `F₀ = p_* β` it is a coherence of the
pullback pseudofunctor (`AlgebraicGeometry.ProEtale.upperStarComp_frobenius_coherence`).

To keep the kernel away from unfolding the concrete Weil sheaf `p^* H`, the statement is made
for any lisse Weil sheaf `F` with an isomorphism `e : F ≅ p^* H` of underlying sheaves carrying
its Weil structure to the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale

namespace ProEtale

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The congruence isomorphisms of pullbacks compose; the composite equality is an independent
hypothesis, so that the kernel never compares proofs of equalities of morphisms. -/
@[reassoc]
lemma upperStarCongr_hom_app_trans' {P Q : Scheme.{u}} {x y z : P ⟶ Q} (h : x = y)
    (h' : y = z) (h'' : x = z) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N =
      (upperStarCongr A h'').hom.app N := by
  subst h h'
  simp [upperStarCongr]

/-- **Frobenius coherence of pullbacks.** For `φ : Z ⟶ Z` with `φ ≫ p = p` and `y : T ⟶ Z`, the
identification `((y ≫ φ) ≫ p)^* = (y ≫ p)^* ≅ y^* p^*` is the composite
`((y ≫ φ) ≫ p)^* ≅ (y ≫ φ)^* p^* ≅ y^* φ^* p^* ≅ y^* (φ ≫ p)^* = y^* p^*`. -/
lemma upperStarComp_frobenius_coherence {T Z Y : Scheme.{u}} (y : T ⟶ Z) (φ : Z ⟶ Z)
    (p : Z ⟶ Y) (hφ : φ ≫ p = p) (h : (y ≫ φ) ≫ p = y ≫ p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarComp A y p).hom.app N =
      (upperStarComp A (y ≫ φ) p).hom.app N ≫ (upperStarComp A y φ).hom.app ((p)^*[A].obj N) ≫
        (y)^*[A].map ((upperStarComp A φ p).inv.app N ≫ (upperStarCongr A hφ).hom.app N) := by
  rw [reassoc_of% upperStarComp_hom_app_comp_upperStarComp_hom_app, Functor.map_comp,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← upperStarCongr_hom_app_comp_upperStarComp_hom_app',
    upperStarCongr_hom_app_trans'_assoc _ _ _ h]

end ProEtale

namespace FrobeniusBasePoint

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) (M₀ : LisseMonodromy l X K)
  (B : FrobeniusBasePoint K X)

/-- The stalk of the canonical Weil structure `Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H` at `t`, after
the identifications `H_{(t ≫ Fr) ≫ p} = (p^* H)_{t ≫ Fr} = (Fr^* p^* H)_t`, is the identification
`H_{(t ≫ Fr) ≫ p} = H_{t ≫ p} = (p^* H)_t`. -/
lemma stalk_frobenius_coherence (t : Spec (.of (AlgebraicClosure K)) ⟶
      (X ↘ Spec (.of K)).geometricFiber) (H : AdicSheaf l X)
    (h : (t ≫ (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom) ≫
      (X ↘ Spec (.of K)).geometricFiberProj = t ≫ (X ↘ Spec (.of K)).geometricFiberProj) :
    (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app H.X) ≫
        (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj t H.X).hom =
      (upperStarStalkIso l (X ↘ Spec (.of K)).geometricFiberProj
          (t ≫ (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom) H.X).hom ≫
        (upperStarStalkIso l (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom t
          (((X ↘ Spec (.of K)).geometricFiberProj)^*[_].obj H.X)).hom ≫
        (stalkFunctor l t).map
          ((upperStarComp _ (X ↘ Spec (.of K)).geometricGaloisFrobenius.hom
              (X ↘ Spec (.of K)).geometricFiberProj).inv.app H.X ≫
            (upperStarCongr _ (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj
              (X ↘ Spec (.of K)))).hom.app H.X) := by
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map,
    ← Functor.map_comp]
  rw [upperStarComp_frobenius_coherence]

end FrobeniusBasePoint

end AlgebraicGeometry

