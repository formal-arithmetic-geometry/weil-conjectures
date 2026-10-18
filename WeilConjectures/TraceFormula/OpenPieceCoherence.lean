/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import WeilConjectures.TraceFormula.CompactCohomology

/-!

# Coherences for the open piece of the trace additivity

For an open immersion `j : U ⟶ X` stable under the Frobenius, the extension by zero commutes with
the pullbacks along the Frobenii on compactly supported cohomology. This is the first square of
the open piece in blueprint `prop-trf-trace-additivity-open-closed` (Steps 2(a) and 3).

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion`:
  for vertical open immersions, `Ex_!` is the extension-by-zero base change through
  `Rj_! ≅ j_!` (blueprint `def-exchange-projection`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The exchange `H ⋙ jS' ⟶ jS ⋙ H'` of an isomorphism `θ : jU ⋙ H ≅ H' ⋙ jU'` along the
adjunctions `jS ⊣ jU` and `jS' ⊣ jU'` is compatible with the counits. -/
lemma Adjunction.exchangeLeft_app_comp_map_counit_app {A B A' B' : Type*} [Category A]
    [Category B] [Category A'] [Category B'] {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'}
    {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU')
    (θ : jU ⋙ H ≅ H' ⋙ jU') (M : B) :
    (Adjunction.exchangeLeft aj aj' θ).app (jU.obj M) ≫ H'.map (aj.counit.app M) =
      jS'.map (θ.hom.app M) ≫ aj'.counit.app (H'.obj M) := by
  rw [Adjunction.exchangeLeft_app]
  have hε := aj'.counit.naturality (H'.map (aj.counit.app M))
  have hθ := θ.hom.naturality (aj.counit.app M)
  simp only [Functor.comp_map, Functor.id_map] at hε hθ
  simp only [Category.assoc]
  erw [← hε]
  rw [← jS'.map_comp_assoc (θ.hom.app _)]
  erw [← hθ]
  rw [← jS'.map_comp_assoc, ← Category.assoc,
    ← H.map_comp]
  erw [aj.right_triangle_components]
  simp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section OpenImmersion

variable {X U : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The counit of `Rj_! ⊣ Lj^*` (the adjunction `Rj_! ⊣ Rj^!` transported along
`Rj^! ≅ Lj^*`) is the counit of `j_! ⊣ Lj^*` through `Rj_! ≅ j_!`. -/
lemma counit_app_ofNatIsoRight_upperShriekIsoUpperStar
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j).ofNatIsoRight
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)).counit.app M =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj M) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app M := by
  have h := conjugateEquiv_counit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom M
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl,
    Iso.symm_inv, conjugateIsoEquiv_apply_hom]
  exact h

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
