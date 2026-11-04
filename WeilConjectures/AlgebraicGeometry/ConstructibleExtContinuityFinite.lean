/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelExtContinuity
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
/-! Finite-coefficient Ext continuity on a Noetherian quasi-compact scheme.

Source: blueprint `sk-lem-constructible-ext-continuity`, clause (1).

The factorization condition `ConstantModelExtContinuity` is false on arbitrary schemes:
on `∐_{n ∈ ℕ} Spec k`, with `F_i = Λ` on the points `n ≤ i` and `0` elsewhere, the identity
of `Λ = colim F_i` factors through no `F_i`. We therefore state it on locally Noetherian,
quasi-compact schemes, where it follows from `constructible_sheaf_ext_continuity`.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The degree-zero filtered-colimit factorization of `Ext` out of constant-model
constructible sheaves, for the coefficient rings `E` and `ℚ̄_ℓ`, on a locally Noetherian
quasi-compact scheme.
Source: blueprint `sk-lem-constructible-ext-continuity`, clause (1).

Proof: `constructible_sheaf_ext_continuity` says that the shifted `Hom` functor out of the
source preserves the filtered colimit; every element of a filtered colimit of abelian groups
has a representative at some stage. -/
theorem constantModelExtContinuity_of_isLocallyNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    ConstantModelExtContinuity (coefficientHeartRingObj R) X := by
  intro M hM I _ _ F c hc n f
  let G := DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M))
  have : IsIso (colimit.post F G) :=
    constructible_sheaf_ext_continuity ℓ E R hR X M hM F (colimit.cocone F)
      (colimit.isColimit F) n
  have : PreservesColimit F G := preservesColimit_of_isIso_post G F
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (F ⋙ G)
    (isColimitOfPreserves G hc) f
  exact ⟨i, g, hg.symm⟩

/-- The factorization of `Ext` out of constant-model constructible sheaves for the finite
coefficient field `E`, on a locally Noetherian quasi-compact scheme.
Source: blueprint `sk-lem-constructible-ext-continuity`, clause (1). -/
theorem continuousMap_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [IsCommMonObj (Profinite.continuousMapRingObj E)]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    ConstantModelExtContinuity (Profinite.continuousMapRingObj E) X :=
  constantModelExtContinuity_of_isLocallyNoetherian ℓ E
    (Profinite.padicSubfieldCondensedRing ℓ E) (Or.inl rfl) X

end AlgebraicGeometry.ProEtale
