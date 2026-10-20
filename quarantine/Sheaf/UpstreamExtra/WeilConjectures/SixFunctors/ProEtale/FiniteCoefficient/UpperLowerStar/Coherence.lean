module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-! Declarations of ours that lived in the upstream file `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!

# Coherence of the composition isomorphisms of `g^*` and `g_*` on pro-étale sheaves

The composition isomorphisms `ProEtale.lowerStarComp : f_* ⋙ g_* ≅ (f ≫ g)_*` and
`ProEtale.upperStarComp : (f ≫ g)^* ≅ g^* ⋙ f^*` of pushforwards and pullbacks on pro-étale
sheaves with values in a Grothendieck abelian category `A`, and the identity isomorphisms
`ProEtale.lowerStarId` and `ProEtale.upperStarId`, satisfy the coherences of a pseudofunctor.
This file proves those that compare pullbacks along morphisms over a fixed base.

## The morphisms `η`

Let `k_X : X ⟶ W` and `k_Y : Y ⟶ W` be morphisms of schemes and `f : X ⟶ Y` with
`f ≫ k_Y = k_X`. For a sheaf `F` on `W_proét`, the composition isomorphism of the pullbacks gives
`f^* k_Y^* F ≅ (f ≫ k_Y)^* F = k_X^* F`, and its mate under `f^* ⊣ f_*` is a morphism
```
η_f(F) : k_Y^* F ⟶ f_* k_X^* F,
```
the unit of `f^* ⊣ f_*` followed by `f_*` of that isomorphism. For the coefficient rings pulled
back from the pro-étale site of a point, `k_X` is the structure morphism `X ⟶ Spec ℤ`, and
`η_f(F)` is the canonical coefficient morphism `Λ_Y ⟶ f_* Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The morphisms `η` are compatible with identities and compositions
(`ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp`):
```
η_{𝟙 X}(F) = (𝟙 X)_* ≅ 𝟭 at k_X^* F,
η_{f ≫ g}(F) = η_g(F) ≫ g_* η_f(F) ≫ (g_* f_* ≅ (f ≫ g)_*) at k_X^* F.
```

## Proof

Under the adjunction `k^* ⊣ k_*`, the morphism `η_f(F)` corresponds to the unit of
`k_X^* ⊣ k_X_*` followed by the composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the
pushforwards (`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`), the composition
isomorphism of the pullbacks being by definition conjugate to that of the pushforwards. The two
compatibilities are thus reduced to the associativity and the left unit law of the composition
isomorphisms of the pushforwards (`ProEtale.lowerStarComp_assoc` and
`ProEtale.lowerStarComp_id_left`). These hold on sections, the pushforwards being restrictions
along the base change functors of the pro-étale sites: both sides are the restriction maps along
the canonical isomorphisms between iterated fibre products, which agree, maps into a fibre
product being determined by their projections.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### Base change along the identity -/

section Site

end Site

/-! ### The composition isomorphisms of the pushforwards -/

section LowerStar

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphisms of pushforwards are associative, up to `eqToHom` along
`(h₁ ≫ h₂) ≫ h₃ = h₁ ≫ h₂ ≫ h₃`: on sections, both sides are the restriction maps along the
canonical isomorphisms of iterated fibre products. -/
lemma ProEtale.coefficient_lowerStarComp_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂)
    (h₃ : X₂ ⟶ X₃) :
    Functor.whiskerLeft (h₁)_*[A] (lowerStarComp A h₂ h₃).hom ≫
        (lowerStarComp A h₁ (h₂ ≫ h₃)).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (lowerStarComp A h₁ h₂).hom (h₃)_*[A] ≫
        (lowerStarComp A (h₁ ≫ h₂) h₃).hom ≫ eqToHom (by rw [Category.assoc]) := by
  apply (cancel_epi (Functor.associator (h₁)_*[A] (h₂)_*[A] (h₃)_*[A]).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom] using
      congrArg Iso.hom (ProEtale.legacy_lowerStarComp_assoc A h₁ h₂ h₃)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism `(𝟙 X)_* ⋙ k_* ≅ (𝟙 X ≫ k)_*` is induced by the identity
isomorphism `(𝟙 X)_* ≅ 𝟭`, up to `eqToHom` along `𝟙 X ≫ k = k`. -/
lemma ProEtale.coefficient_lowerStarComp_id_left {X Y : Scheme.{u}} (k : X ⟶ Y) :
    (lowerStarComp A (𝟙 X) k).hom =
      Functor.whiskerRight (lowerStarId A X).hom (k)_*[A] ≫ (Functor.leftUnitor _).hom ≫
        eqToHom (by rw [Category.id_comp]) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv] using congrArg Iso.hom (ProEtale.legacy_lowerStarComp_id_left A k)


end LowerStar

/-! ### The morphisms `η` -/

section Eta

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
end Eta

end AlgebraicGeometry
