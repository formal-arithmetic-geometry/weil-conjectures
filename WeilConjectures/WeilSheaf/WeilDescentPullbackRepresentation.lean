/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescentRepresentation

/-!
# A Frobenius coherence of pullbacks

Let `p : X ⟶ X₀` be the projection of the geometric fibre of a scheme over a finite field and `Fr`
its geometric Galois Frobenius, so that `Fr ≫ p = p`. The Weil fundamental representation of a
sheaf `p^* H` pulled back from the model, with its canonical Weil structure
`Fr^* p^* H ≅ (Fr ≫ p)^* H = p^* H`, is computed on the Frobenius lift through a coherence of the
pullback pseudofunctor (`AlgebraicGeometry.ProEtale.upperStarComp_frobenius_coherence`), used in
`WeilConjectures.WeilSheaf.WeilDescentFundamentalRep`.
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

end AlgebraicGeometry

