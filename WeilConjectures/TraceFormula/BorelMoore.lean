/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Dualizing

/-!

# Pushforward and linearity of Borel–Moore sections

Let `h : T ⟶ T'` be a proper morphism of separated `k`-schemes of finite type. The
*pushforward* of a Borel–Moore section `α : ℚ̄_ℓ,T ⟶ ω_T` is the Borel–Moore section
```
h_* α : ℚ̄_ℓ,T' ⟶ Rh_* Lh^* ℚ̄_ℓ,T' ≅ Rh_* ℚ̄_ℓ,T --Rh_* α--> Rh_* ω_T ≅ Rh_! Rh^! ω_T' ⟶ ω_T'
```
(`ProEtale.CondensedRing.BorelMooreSection.pushforward`, blueprint
`def-trf-borel-moore-pushforward`), built from the unit of `Lh^* ⊣ Rh_*`, the unit isomorphism
of the monoidal functor `Lh^*`, the identification `Rh_! ≅ Rh_*` of the proper `h`, the
composition isomorphism `Rh^! ω_T' ≅ ω_T` and the counit of `Rh_! ⊣ Rh^!`.

The scalars `End (ℚ̄_ℓ,s)` act on the Borel–Moore sections of `T` through the monoidal pullback
`La_T^*` (`ProEtale.CondensedRing.BorelMooreSection.scalar`), and the integral is linear for
this action (`ProEtale.CondensedRing.BorelMooreSection.integral_scalar_comp`, blueprint
`lem-trf-integration-linear`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace BorelMooreSection

section Pushforward

variable {T T' : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
  [IsSeparated T.hom] [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
  (h : T ⟶ T') [IsProper h.left]

/-- The *pushforward* `h_* α` of a Borel–Moore section `α` along a proper morphism `h`
(blueprint `def-trf-borel-moore-pushforward`):
```
ℚ̄_ℓ,T' ⟶ Rh_* Lh^* ℚ̄_ℓ,T' ≅ Rh_* ℚ̄_ℓ,T --Rh_* α--> Rh_* ω_T ≅ Rh_! ω_T ≅ Rh_! Rh^! ω_T'
  ⟶ ω_T'.
```
-/
noncomputable def pushforward (α : BorelMooreSection ℓ T) : BorelMooreSection ℓ T' :=
  (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ h).unit.app
      (𝟙_ _) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
      ((Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)).inv ≫ α) ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app _ ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ h).map
      (dualizingComplexComp ℓ h).inv ≫
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ h).counit.app _

/-- The pushforward of Borel–Moore sections is additive. -/
lemma pushforward_add (α β : BorelMooreSection ℓ T) :
    pushforward h (α + β) = pushforward h α + pushforward h β := by
  simp only [pushforward, Preadditive.comp_add, Functor.map_add, Preadditive.add_comp]

end Pushforward

section Scalar

variable {X : Over (Spec (.of k))} [QuasiCompact X.hom]

/-- The action of a scalar `t ∈ End (ℚ̄_ℓ,s)` on `ℚ̄_ℓ,X`: the pullback of `t` along the structure
morphism `a_X`, read through the unit isomorphism `ℚ̄_ℓ,X ≅ La_X^* ℚ̄_ℓ,s` of the monoidal functor
`La_X^*`. -/
noncomputable def scalar [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    (t : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :
    End (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map t ≫
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv

/-- **Linearity of the integral** (blueprint `lem-trf-integration-linear`,
`rem-ptr-trf-integration-8`): for a scalar `t ∈ End (ℚ̄_ℓ,s)` acting on a Borel–Moore section `α`
through `scalar`, `∫_X (t • α) = t ∘ ∫_X α`. Together with `integral_add` this is the
`End (ℚ̄_ℓ,s)`-linearity of the integral. -/
lemma integral_scalar_comp [IsProper X.hom]
    (t : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (α : BorelMooreSection ℓ X) :
    integral (scalar t ≫ α : BorelMooreSection ℓ X) = t ≫ α.integral := by
  have : IsProper (toPoint X).left := inferInstanceAs (IsProper X.hom)
  have hn := (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
    (toPoint X)).unit.naturality t
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [integral, scalar, Adjunction.homEquiv_counit, Category.assoc, Functor.map_comp]
  rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc,
    ← reassoc_of% hn]

end Scalar

end BorelMooreSection

end AlgebraicGeometry.ProEtale.CondensedRing
