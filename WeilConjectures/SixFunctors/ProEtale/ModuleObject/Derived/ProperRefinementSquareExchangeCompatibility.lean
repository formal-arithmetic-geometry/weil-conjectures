/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperIdentityRefinementIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison

/-! # Proper refinement transport of compact exchanges

This isolates the arbitrary-square transport used by proper compactification
coincidence. (blueprint: sk-prop-sf-comp-proper).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

def properIdentityRefinementForSquare {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsProper f] (c : Compactification f) :
    (Compactification.ofIsProper f).Refinement c where
  hom := c.i
  i_hom := Category.id_comp _
  hom_g := c.comm.symm

theorem properIdentityRefinementForSquare_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : Compactification f) :
    IsIso (refinement Λ (properIdentityRefinementForSquare c)) := by
  exact properIdentityRefinement_isIso Λ f c
    (properIdentityRefinementForSquare c)

/-- The normalized comparison attached to one identity-model refinement. -/
noncomputable def properRefinementComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : Compactification f)
    (r : (Compactification.ofIsProper f).Refinement c)
    [IsIso (refinement Λ r)] : F Λ c ≅ R Λ f :=
  @asIso _ _ _ _ (refinement Λ r) inferInstance ≪≫
    properIdentityComparison Λ f

noncomputable def properRefinementComparisonForSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : Compactification f) : F Λ c ≅ R Λ f :=
  letI := properIdentityRefinementForSquare_isIso Λ f c
  properRefinementComparison Λ f c (properIdentityRefinementForSquare c)

/-- The normalized compact exchange agrees with proper base change after
identity-refinement comparison, for an arbitrary Cartesian square.

Source: Step 2 of `sk-prop-sf-comp-proper`, using clause (3) of
`det-sf-comp-composition-base-change` and the third conjunct of
`identityOpenExchangeNormalization`.

Proof in words: compare both compactifications with their identity-open proper
models.  The refinement cube transports `squareExchange` through those
comparisons, while identity-open normalization identifies the two identity
exchanges with `baseChangeMap`.  Naturality of the comparison isomorphisms and
associativity of composition give the displayed equality before cancellation.
The argument does not assume that the two vertical maps of the square are
isomorphisms.
(blueprint: sk-prop-sf-comp-proper). -/
theorem properRefinement_squareExchange_compatibility
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [IsProper f] [IsProper f'] {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback w f' f v) (c : Compactification f)
    (c' : Compactification f')
    (s : Square c c' w v) (K : D Λ X) :
    (squareExchange Λ s).app K ≫
        (properRefinementComparisonForSquare Λ f' c').hom.app ((P Λ w).obj K) =
      (P Λ v).map
          ((properRefinementComparisonForSquare Λ f c).hom.app K) ≫
        (baseChangeMap Λ sq.toCommSq).app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
