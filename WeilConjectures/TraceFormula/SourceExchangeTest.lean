/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ClassTest
public import WeilConjectures.TraceFormula.ProperCompatibilitySupport
public import WeilConjectures.TraceFormula.SupportedClass

/-!

# Test maps for classes on products

A morphism `φ : Z ⟶ RHom(Lp₂^* M, Rp₁^! M)` on `S ⨯ S` is determined by its *test map*
`Rp₁_! (Lp₂^* M ⊗ Z) ⟶ M` (`ProEtale.CondensedRing.classTest`), its uncurried
`Rp₁_! ⊣ Rp₁^!`-adjoint. The test map of the class of a correspondence is the projection formula
followed by the exceptional adjoint of the coefficient map
(`ProEtale.CondensedRing.classTest_correspondenceClassEquiv_symm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (M : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

variable {M}

set_option maxHeartbeats 1000000 in
-- the compactly supported direct images are unfolded in the defeq checks
/-- The test map of a class: the left projection morphism of the support, the composition law
and the exceptional adjoint of the coefficient map. -/
lemma classTest_correspondenceClassEquiv_symm {C : Over (Spec (.of k))} [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (s : C ⟶ S ⨯ S)
    (w : (boundedConstructibleUpperStar _ ℓ (s ≫ prod.snd)).obj M ⟶
      (boundedConstructibleUpperShriek ℓ (s ≫ prod.fst)).obj M) :
    classTest ℓ M ((correspondenceClassEquiv ℓ s M M).symm w) =
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
          (Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ s) _ (𝟙_ _) ≫
            (boundedConstructibleLowerShriek ℓ s).map
              ((ρ_ _).hom ≫ (boundedConstructibleUpperStarComp _ ℓ s prod.snd).inv.app M)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (s ≫ prod.fst)).map w ≫
        (boundedConstructibleUpperShriekAdjunction ℓ (s ≫ prod.fst)).counit.app M := by
  have hP := Adjunction.map_map_conjugateIsoEquiv_comp_counit
    (boundedConstructibleUpperShriekAdjunction ℓ s)
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S))
    (boundedConstructibleUpperShriekAdjunction ℓ (s ≫ prod.fst))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst) M
  simp only [classTest, correspondenceClassEquiv, Equiv.coe_fn_symm_mk,
    Verdier.uncurry_correspondenceClassEquiv_symm, Adjunction.homEquiv_counit,
    boundedConstructibleUpperShriekComp_padicAlgCl,
    Functor.map_comp, Category.assoc] at hP ⊢
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ s prod.fst).inv.naturality w
  simp only [Functor.comp_map] at hn
  rw [hP, ← Category.assoc ((boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map
    ((boundedConstructibleLowerShriek ℓ s).map w)), hn, Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
