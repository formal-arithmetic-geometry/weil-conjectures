/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

/-!
# Blueprint statements

lem-galois-descent.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Blueprint: lem-galois-descent. -/
theorem finiteEtaleDescent {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g] :
    ∃ (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
      (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left),
      Nonempty F.IsEquivalence ∧
      (∀ P : Y.FiniteEtale,
        ∃ hq : q P ≫ P.obj.hom = (F.obj P).obj.V.hom ≫ g,
          IsPullback (q P) (F.obj P).obj.V.hom P.obj.hom g ∧
          ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y')
            (h : f₁ ≫ g = f₂ ≫ g) (z : Over.mk f₁ ⟶ (F.obj P).obj.V),
            ((F.obj P).obj.datum.transport f₁ f₂ h z).left ≫ q P =
              z.left ≫ q P) ∧
      ∀ P Q : Y.FiniteEtale, ∀ f : P ⟶ Q,
        (F.map f).hom.hom.left ≫ q Q = q P ≫ f.hom.left := by
  sorry

end AlgebraicGeometry
